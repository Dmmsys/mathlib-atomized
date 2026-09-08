/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Comap

/-!
# Restricting a measure to a subset or a subtype

Given a measure `μ` on a type `α` and a subset `s` of `α`, we define a measure `μ.restrict s` as
the restriction of `μ` to `s` (still as a measure on `α`).

We investigate how this notion interacts with usual operations on measures (sum, pushforward,
pullback), and on sets (inclusion, union, Union).

We also study the relationship between the restriction of a measure to a subtype (given by the
pullback under `Subtype.val`) and the restriction to a set as above.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open Set MeasureTheory Measure Filter MeasurableSpace ENNReal Function

variable {R α β δ γ ι : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}

namespace Measure

/-! ### Restricting a measure -/

/-- Restrict a measure `μ` to a set `s` as an `ℝ≥0∞`-linear map. -/
@[irreducible]
/-
**MeasureTheory.Measure.restrict** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：restrict {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α
参数：μ : Measure α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a measure `μ` to a set `s` as an `ℝ≥0∞`-linear map.
-/
noncomputable def restrictₗ {m0 : MeasurableSpace α} (s : Set α) : Measure α →ₗ[ℝ≥0∞] Measure α :=
  liftLinear (OuterMeasure.restrict s) fun μ s' hs' t => by
    suffices μ (s ∩ t) = μ (s ∩ t ∩ s') + μ ((s ∩ t) \ s') by
      simpa [← Set.inter_assoc, Set.inter_comm _ s, ← inter_sdiff_assoc]
    exact le_toOuterMeasure_caratheodory _ _ hs' _

/-- Restrict a measure `μ` to a set `s`. -/
/-
**MeasureTheory.Measure.restrict** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：restrict {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α
参数：μ : Measure α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a measure `μ` to a set `s`.
-/
noncomputable def restrict {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α :=
  restrictₗ s μ

@[simp]
/-
**MeasureTheory.Measure.restrict** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：restrict {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α
参数：μ : Measure α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictₗ_apply {_m0 : MeasurableSpace α} (s : Set α) (μ : Measure α) :
    restrictₗ s μ = μ.restrict s :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- This lemma shows that `restrict` and `toOuterMeasure` commute. Note that the LHS has a
restrict on measures and the RHS has a restrict on outer measures. -/
/-
**MeasureTheory.Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：restrict_toOuterMeasure_eq_toOuterMeasure_restrict (h : MeasurableSet s) :
 (μ.restrict s).toOuterMeasure = OuterMeasure.restrict s μ.toOuterMeasure
参数：h : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrictₗ.eq_1`：∀ {α : Type u_2} {m0 : MeasurableS
pace α} (s : Set α),   MeasureTheory.Measure.restrictₗ s = MeasureTheory.Measure
.liftLinear (MeasureTheory…
· 使用定理 `MeasureTheory.OuterMeasure.restrict_trim`：restrict_trim {μ : OuterMeasur
e α} {s : Set α} (hs : MeasurableSet s) : (restrict s μ).trim = restrict s μ.tri
m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.trimmed`：trimmed (μ : Measure α) : μ.toOuterMeasur
e.trim = μ.toOuterMeasure
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This lemma shows that `restrict` and `toOuterMeasure` commute. Note that the LHS
 has a
restrict on measures and the RHS has a restrict on outer measures.
-/
theorem restrict_toOuterMeasure_eq_toOuterMeasure_restrict (h : MeasurableSet s) :
    (μ.restrict s).toOuterMeasure = OuterMeasure.restrict s μ.toOuterMeasure := by
  simp_rw [restrict, restrictₗ, liftLinear, LinearMap.coe_mk, AddHom.coe_mk,
    toMeasure_toOuterMeasure, OuterMeasure.restrict_trim h, μ.trimmed]
/-
**MeasureTheory.Measure.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t inter s)
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_apply₀`：restrict_apply₀ (ht : NullMeasura
bleSet t (μ.restrict s)) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_apply₀ (ht : NullMeasurableSet t (μ.restrict s)) : μ.restrict s t = μ (t ∩ s) := by
  rw [restrict, restrictₗ] at ht
  rw [← restrictₗ_apply, restrictₗ, liftLinear_apply₀ _ ht, OuterMeasure.restrict_apply,
    coe_toOuterMeasure]

/-- If `t` is a measurable set, then the measure of `t` with respect to the restriction of
  the measure to `s` equals the outer measure of `t ∩ s`. An alternate version requiring that `s`
  be measurable instead of `t` exists as `Measure.restrict_apply'`. -/
@[simp]
/-
**MeasureTheory.Measure.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t inter s)
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_apply₀`：restrict_apply₀ (ht : NullMeasura
bleSet t (μ.restrict s)) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ

--- 原说明 ---
If `t` is a measurable set, then the measure of `t` with respect to the restrict
ion of
  the measure to `s` equals the outer measure of `t ∩ s`. An alternate version r
equiring that `s`
  be measurable instead of `t` exists as `Measure.restrict_apply'`.
-/
theorem restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t ∩ s) :=
  restrict_apply₀ ht.nullMeasurableSet

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
/-
**MeasureTheory.Measure.restrict_mono'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：restrict_mono' {_m0 : MeasurableSpace α} ⦃s s' : Set α⦄ ⦃μ ν : Measure α⦄ 
(hs : s <=ᵐ[μ] s') (hμν : μ <= ν) : μ.restrict s <= ν.restrict s'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measure_mono_ae`：measure_mono_ae (H : s <=ᵐ[μ] t) : μ s <=
 μ t
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.le_iff'`：le_iff' : μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂
 s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Restriction of a measure to a subset is monotone both in set and in measure.
-/
theorem restrict_mono' {_m0 : MeasurableSpace α} ⦃s s' : Set α⦄ ⦃μ ν : Measure α⦄ (hs : s ≤ᵐ[μ] s')
    (hμν : μ ≤ ν) : μ.restrict s ≤ ν.restrict s' :=
  Measure.le_iff.2 fun t ht => calc
    μ.restrict s t = μ (t ∩ s) := restrict_apply ht
    _ ≤ μ (t ∩ s') := (measure_mono_ae <| hs.mono fun _x hx ⟨hxt, hxs⟩ => ⟨hxt, hx hxs⟩)
    _ ≤ ν (t ∩ s') := le_iff'.1 hμν (t ∩ s')
    _ = ν.restrict s' t := (restrict_apply ht).symm

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
@[mono, gcongr]
/-
**MeasureTheory.Measure.restrict_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：restrict_mono {_m0 : MeasurableSpace α} ⦃s s' : Set α⦄ (hs : s subseteq s'
) ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.restrict s <= ν.restrict s'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_mono'`：restrict_mono' {_m0 : MeasurableSp
ace α} ⦃s s' : Set α⦄ ⦃μ ν : Measure α⦄ (hs : s <=ᵐ[μ] s') (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Restriction of a measure to a subset is monotone both in set and in measure.
-/
theorem restrict_mono {_m0 : MeasurableSpace α} ⦃s s' : Set α⦄ (hs : s ⊆ s') ⦃μ ν : Measure α⦄
    (hμν : μ ≤ ν) : μ.restrict s ≤ ν.restrict s' :=
  restrict_mono' (ae_of_all _ hs) hμν
/-
**MeasureTheory.Measure.restrict_mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：restrict_mono_measure {_ : MeasurableSpace α} {μ ν : Measure α} (h : μ <= 
ν) (s : Set α) : μ.restrict s <= ν.restrict s
参数：h : μ <= ν；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem restrict_mono_measure {_ : MeasurableSpace α} {μ ν : Measure α} (h : μ ≤ ν) (s : Set α) :
    μ.restrict s ≤ ν.restrict s :=
  restrict_mono subset_rfl h
/-
**MeasureTheory.Measure.restrict_mono_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：restrict_mono_set {_ : MeasurableSpace α} (μ : Measure α) {s t : Set α} (h
 : s subseteq t) : μ.restrict s <= μ.restrict t
参数：μ : Measure α；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem restrict_mono_set {_ : MeasurableSpace α} (μ : Measure α) {s t : Set α} (h : s ⊆ t) :
    μ.restrict s ≤ μ.restrict t :=
  restrict_mono h le_rfl
/-
**MeasureTheory.Measure.restrict_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：restrict_mono_ae (h : s <=ᵐ[μ] t) : μ.restrict s <= μ.restrict t
参数：h : s <=ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.restrict_mono'`：restrict_mono' {_m0 : MeasurableSp
ace α} ⦃s s' : Set α⦄ ⦃μ ν : Measure α⦄ (hs : s <=ᵐ[μ] s') (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem restrict_mono_ae (h : s ≤ᵐ[μ] t) : μ.restrict s ≤ μ.restrict t :=
  restrict_mono' h (le_refl μ)
/-
**MeasureTheory.Measure.restrict_congr_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：restrict_congr_set (h : s =ᵐ[μ] t) : μ.restrict s = μ.restrict t
参数：h : s =ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.Measure.restrict_mono_ae`：restrict_mono_ae (h : s <=ᵐ[μ] t
) : μ.restrict s <= μ.restrict t
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem restrict_congr_set (h : s =ᵐ[μ] t) : μ.restrict s = μ.restrict t :=
  le_antisymm (restrict_mono_ae h.le) (restrict_mono_ae h.symm.le)

/-- If `s` is a measurable set, then the outer measure of `t` with respect to the restriction of
the measure to `s` equals the outer measure of `t ∩ s`. This is an alternate version of
`Measure.restrict_apply`, requiring that `s` is measurable instead of `t`. -/
@[simp]
/-
**MeasureTheory.Measure.restrict_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：restrict_apply' (hs : MeasurableSet s) : μ.restrict s t = μ (t inter s)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.toOuterMeasure_apply`：∀ {α : Type u_1} [inst : Mea
surableSpace α] (μ : MeasureTheory.Measure α) (s : Set α), μ.toOuterMeasure s = 
μ s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict
`：restrict_toOuterMeasure_eq_toOuterMeasure_restrict (h : MeasurableSet s) : (μ.
restrict s).toOuterMeasure = OuterMeasure.restrict s μ.toOuter…
· 使用定理 `MeasureTheory.OuterMeasure.restrict_apply`：restrict_apply (s t : Set α) 
(m : OuterMeasure α) : restrict s m t = m (t inter s)

--- 原说明 ---
If `s` is a measurable set, then the outer measure of `t` with respect to the re
striction of
the measure to `s` equals the outer measure of `t ∩ s`. This is an alternate ver
sion of
`Measure.restrict_apply`, requiring that `s` is measurable instead of `t`.
-/
theorem restrict_apply' (hs : MeasurableSet s) : μ.restrict s t = μ (t ∩ s) := by
  rw [← toOuterMeasure_apply,
    Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict hs,
    OuterMeasure.restrict_apply s t _, toOuterMeasure_apply]
/-
**MeasureTheory.Measure._root_.IsCountablySpanning.null_of_forall_inter_null** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsCountablySpanning.null_of_forall_inter_null {C : Set (Set α)}
    (hC : IsCountablySpanning C) (ht : ∀ t ∈ C, μ (s ∩ t) = 0) :
    μ s = 0 := by
  obtain ⟨t, ht1, ht2⟩ := hC
  rw [show s = ⋃ n, s ∩ t n by rw [← inter_iUnion, ht2, inter_univ], measure_iUnion_null_iff]
  exact fun i => ht (t i) (ht1 i)
/-
**MeasureTheory.Measure.forall_measure_inter_isCountablySpanning_eq_zero** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：forall_measure_inter_isCountablySpanning_eq_zero {C : Set (Set α)} (hC : I
sCountablySpanning C) : (forall t in C, μ (s inter t) = 0) ↔ μ s = 0 where mp
参数：Set α；hC : IsCountablySpanning C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCountablySpanning.null_of_forall_inter_null`：∀ {α : Type u_2} {m0 : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} {C : Set (Set α)},   
IsCountablySpanning C → (∀ t ∈ C, μ…
· 使用定理 `MeasureTheory.measure_inter_null_of_null_left`：measure_inter_null_of_nul
l_left {S : Set α} (T : Set α) (h : μ S = 0) : μ (S inter T) = 0
-/
theorem forall_measure_inter_isCountablySpanning_eq_zero {C : Set (Set α)}
    (hC : IsCountablySpanning C) : (∀ t ∈ C, μ (s ∩ t) = 0) ↔ μ s = 0 where
  mp := hC.null_of_forall_inter_null
  mpr h t _ := measure_inter_null_of_null_left t h
/-
**MeasureTheory.Measure._root_.IsCountablySpanning.null_of_forall_restrict_null*
* 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsCountablySpanning.null_of_forall_restrict_null {C : Set (Set α)}
    (hC : IsCountablySpanning C) (hm : ∀ t ∈ C, MeasurableSet t)
    (ht : ∀ t ∈ C, μ.restrict t s = 0) :
    μ s = 0 := by
  rw [← forall_measure_inter_isCountablySpanning_eq_zero hC]
  intro t htc
  simpa [← μ.restrict_apply' (hm _ htc)] using ht t htc
/-
**MeasureTheory.Measure.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t inter s)
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_apply₀`：restrict_apply₀ (ht : NullMeasura
bleSet t (μ.restrict s)) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_apply₀' (hs : NullMeasurableSet s μ) : μ.restrict s t = μ (t ∩ s) := by
  rw [← restrict_congr_set hs.toMeasurable_ae_eq,
    restrict_apply' (measurableSet_toMeasurable _ _),
    measure_congr ((ae_eq_refl t).inter hs.toMeasurable_ae_eq)]
/-
**MeasureTheory.Measure.restrict_le_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：restrict_le_self : μ.restrict s <= μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem restrict_le_self : μ.restrict s ≤ μ :=
  Measure.le_iff.2 fun t ht => calc
    μ.restrict s t = μ (t ∩ s) := restrict_apply ht
    _ ≤ μ t := measure_mono inter_subset_left
/-
**MeasureTheory.Measure.absolutelyContinuous_restrict** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_restrict : μ.restrict s ≪ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
theorem absolutelyContinuous_restrict : μ.restrict s ≪ μ :=
  Measure.absolutelyContinuous_of_le Measure.restrict_le_self

variable (μ)
/-
**MeasureTheory.Measure.restrict_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：restrict_eq_self (h : s subseteq t) : μ.restrict t s = μ s
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.le_iff'`：le_iff' : μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂
 s
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
-/
theorem restrict_eq_self (h : s ⊆ t) : μ.restrict t s = μ s :=
  (le_iff'.1 restrict_le_self s).antisymm <|
    calc
      μ s ≤ μ (toMeasurable (μ.restrict t) s ∩ t) :=
        measure_mono (subset_inter (subset_toMeasurable _ _) h)
      _ = μ.restrict t s := by
        rw [← restrict_apply (measurableSet_toMeasurable _ _), measure_toMeasurable]

@[simp]
/-
**MeasureTheory.Measure.restrict_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：restrict_apply_self (s : Set α) : (μ.restrict s) s = μ s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_eq_self`：restrict_eq_self (h : s subseteq
 t) : μ.restrict t s = μ s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem restrict_apply_self (s : Set α) : (μ.restrict s) s = μ s :=
  restrict_eq_self μ Subset.rfl

variable {μ}
/-
**MeasureTheory.Measure.restrict_apply_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：restrict_apply_univ (s : Set α) : μ.restrict s univ = μ s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem restrict_apply_univ (s : Set α) : μ.restrict s univ = μ s := by
  rw [restrict_apply MeasurableSet.univ, Set.univ_inter]
/-
**MeasureTheory.Measure.le_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：le_restrict_apply (s t : Set α) : μ (t inter s) <= μ.restrict s t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_eq_self`：restrict_eq_self (h : s subseteq
 t) : μ.restrict t s = μ s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem le_restrict_apply (s t : Set α) : μ (t ∩ s) ≤ μ.restrict s t :=
  calc
    μ (t ∩ s) = μ.restrict s (t ∩ s) := (restrict_eq_self μ inter_subset_right).symm
    _ ≤ μ.restrict s t := measure_mono inter_subset_left
/-
**MeasureTheory.Measure.restrict_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：restrict_apply_le (s t : Set α) : μ.restrict s t <= μ t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.le_iff'`：le_iff' : μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂
 s
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
theorem restrict_apply_le (s t : Set α) : μ.restrict s t ≤ μ t :=
  Measure.le_iff'.1 restrict_le_self _
/-
**MeasureTheory.Measure.restrict_apply_superset** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：restrict_apply_superset (h : s subseteq t) : μ.restrict s t = μ s
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_apply_self`：restrict_apply_self (s : Set 
α) : (μ.restrict s) s = μ s
-/
theorem restrict_apply_superset (h : s ⊆ t) : μ.restrict s t = μ s :=
  ((measure_mono (subset_univ _)).trans_eq <| restrict_apply_univ _).antisymm
    ((restrict_apply_self μ s).symm.trans_le <| measure_mono h)

@[simp]
/-
**MeasureTheory.Measure.restrict_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：restrict_add {_m0 : MeasurableSpace α} (μ ν : Measure α) (s : Set α) : (μ 
+ ν).restrict s = μ.restrict s + ν.restrict s
参数：μ ν : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem restrict_add {_m0 : MeasurableSpace α} (μ ν : Measure α) (s : Set α) :
    (μ + ν).restrict s = μ.restrict s + ν.restrict s :=
  (restrictₗ s).map_add μ ν

@[simp]
/-
**MeasureTheory.Measure.restrict_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：restrict_zero {_m0 : MeasurableSpace α} (s : Set α) : (0 : Measure α).rest
rict s = 0
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem restrict_zero {_m0 : MeasurableSpace α} (s : Set α) : (0 : Measure α).restrict s = 0 :=
  (restrictₗ s).map_zero

@[simp]
/-
**MeasureTheory.Measure.restrict_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：restrict_smul {_m0 : MeasurableSpace α} {R : Type*} [SMul R Real>=0∞] [IsS
calarTower R Real>=0∞ Real>=0∞] (c : R) (μ : Measure α) (s : Set α) : (c • μ).re
strict s = c • μ.restrict s
参数：c : R；μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
theorem restrict_smul {_m0 : MeasurableSpace α} {R : Type*} [SMul R ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (μ : Measure α) (s : Set α) :
    (c • μ).restrict s = c • μ.restrict s := by
  simpa only [smul_one_smul] using! (restrictₗ s).map_smul (c • 1) μ
/-
**MeasureTheory.Measure.restrict_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：restrict_restrict (hs : MeasurableSet s) : (μ.restrict t).restrict s = μ.r
estrict (s inter t)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_restrict₀`：restrict_restrict₀ (hs : NullM
easurableSet s (μ.restrict t)) : (μ.restrict t).restrict s = μ.restrict (s inter
 t)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_restrict₀ (hs : NullMeasurableSet s (μ.restrict t)) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  ext fun u hu => by
    simp only [Set.inter_assoc, restrict_apply hu,
      restrict_apply₀ (hu.nullMeasurableSet.inter hs)]

@[simp]
/-
**MeasureTheory.Measure.restrict_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：restrict_restrict (hs : MeasurableSet s) : (μ.restrict t).restrict s = μ.r
estrict (s inter t)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_restrict₀`：restrict_restrict₀ (hs : NullM
easurableSet s (μ.restrict t)) : (μ.restrict t).restrict s = μ.restrict (s inter
 t)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_restrict (hs : MeasurableSet s) : (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  restrict_restrict₀ hs.nullMeasurableSet
/-
**MeasureTheory.Measure.restrict_restrict_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：restrict_restrict_of_subset (h : s subseteq t) : (μ.restrict t).restrict s
 = μ.restrict s
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.restrict_eq_self`：restrict_eq_self (h : s subseteq
 t) : μ.restrict t s = μ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem restrict_restrict_of_subset (h : s ⊆ t) : (μ.restrict t).restrict s = μ.restrict s := by
  ext1 u hu
  rw [restrict_apply hu, restrict_apply hu, restrict_eq_self]
  exact inter_subset_right.trans h
/-
**MeasureTheory.Measure.restrict_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：restrict_restrict (hs : MeasurableSet s) : (μ.restrict t).restrict s = μ.r
estrict (s inter t)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_restrict₀`：restrict_restrict₀ (hs : NullM
easurableSet s (μ.restrict t)) : (μ.restrict t).restrict s = μ.restrict (s inter
 t)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_restrict₀' (ht : NullMeasurableSet t μ) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  ext fun u hu => by simp only [restrict_apply hu, restrict_apply₀' ht, inter_assoc]
/-
**MeasureTheory.Measure.restrict_restrict'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：restrict_restrict' (ht : MeasurableSet t) : (μ.restrict t).restrict s = μ.
restrict (s inter t)
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_restrict₀'`：restrict_restrict₀' (ht : Nul
lMeasurableSet t μ) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_restrict' (ht : MeasurableSet t) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  restrict_restrict₀' ht.nullMeasurableSet
/-
**MeasureTheory.Measure.restrict_comm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：restrict_comm (hs : MeasurableSet s) : (μ.restrict t).restrict s = (μ.rest
rict s).restrict t
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.Measure.restrict_restrict'`：restrict_restrict' (ht : Measu
rableSet t) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem restrict_comm (hs : MeasurableSet s) :
    (μ.restrict t).restrict s = (μ.restrict s).restrict t := by
  rw [restrict_restrict hs, restrict_restrict' hs, inter_comm]
/-
**MeasureTheory.Measure.restrict_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：restrict_apply_eq_zero (ht : MeasurableSet t) : μ.restrict s t = 0 ↔ μ (t 
inter s) = 0
参数：ht : MeasurableSet t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem restrict_apply_eq_zero (ht : MeasurableSet t) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 := by
  rw [restrict_apply ht]
/-
**MeasureTheory.Measure.measure_inter_eq_zero_of_restrict** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure`。
形式化陈述：measure_inter_eq_zero_of_restrict (h : μ.restrict s t = 0) : μ (t inter s)
 = 0
参数：h : μ.restrict s t = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.Measure.le_restrict_apply`：le_restrict_apply (s t : Set α)
 : μ (t inter s) <= μ.restrict s t
-/
theorem measure_inter_eq_zero_of_restrict (h : μ.restrict s t = 0) : μ (t ∩ s) = 0 :=
  nonpos_iff_eq_zero.1 (h ▸ le_restrict_apply _ _)
/-
**MeasureTheory.Measure.restrict_apply_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：restrict_apply_eq_zero' (hs : MeasurableSet s) : μ.restrict s t = 0 ↔ μ (t
 inter s) = 0
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem restrict_apply_eq_zero' (hs : MeasurableSet s) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 := by
  rw [restrict_apply' hs]

@[simp]
/-
**MeasureTheory.Measure.restrict_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：restrict_eq_zero : μ.restrict s = 0 ↔ μ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem restrict_eq_zero : μ.restrict s = 0 ↔ μ s = 0 := by
  rw [← measure_univ_eq_zero, restrict_apply_univ]

/-- If `μ s ≠ 0`, then `μ.restrict s ≠ 0`, in terms of `NeZero` instances. -/
/-
**MeasureTheory.Measure.restrict.neZero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure.restrict`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 : Set α} [NeZero (μ s)],   NeZero (μ.restrict s)
参数：μ s；μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0

--- 原说明 ---
If `μ s ≠ 0`, then `μ.restrict s ≠ 0`, in terms of `NeZero` instances.
-/
instance restrict.neZero [NeZero (μ s)] : NeZero (μ.restrict s) :=
  ⟨mt restrict_eq_zero.mp <| NeZero.ne _⟩
/-
**MeasureTheory.Measure.restrict_zero_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：restrict_zero_set {s : Set α} (h : μ s = 0) : μ.restrict s = 0
参数：h : μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
-/
theorem restrict_zero_set {s : Set α} (h : μ s = 0) : μ.restrict s = 0 :=
  restrict_eq_zero.2 h

@[simp]
/-
**MeasureTheory.Measure.restrict_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：restrict_empty : μ.restrict ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_zero_set`：restrict_zero_set {s : Set α} (
h : μ s = 0) : μ.restrict s = 0
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem restrict_empty : μ.restrict ∅ = 0 :=
  restrict_zero_set measure_empty

@[simp]
/-
**MeasureTheory.Measure.restrict_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：restrict_univ : μ.restrict univ = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_univ : μ.restrict univ = μ :=
  ext fun s hs => by simp [hs]
/-
**MeasureTheory.Measure.restrict_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：restrict_inter_add_sdiff (s : Set α) (ht : MeasurableSet t) : μ.restrict (
s inter t) + μ.restrict (s \ t) = μ.restrict s
参数：s : Set α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_inter_add_sdiff₀`：restrict_inter_add_sdif
f₀ (s : Set α) (ht : NullMeasurableSet t μ) : μ.restrict (s inter t) + μ.restric
t (s \ t) = μ.restrict s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_inter_add_sdiff₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∩ t) + μ.restrict (s \ t) = μ.restrict s := by
  ext1 u hu
  simp only [add_apply, restrict_apply hu, ← inter_assoc, sdiff_eq]
  exact measure_inter_add_sdiff₀ (u ∩ s) ht

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff₀ := restrict_inter_add_sdiff₀
/-
**MeasureTheory.Measure.restrict_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：restrict_inter_add_sdiff (s : Set α) (ht : MeasurableSet t) : μ.restrict (
s inter t) + μ.restrict (s \ t) = μ.restrict s
参数：s : Set α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_inter_add_sdiff₀`：restrict_inter_add_sdif
f₀ (s : Set α) (ht : NullMeasurableSet t μ) : μ.restrict (s inter t) + μ.restric
t (s \ t) = μ.restrict s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_inter_add_sdiff (s : Set α) (ht : MeasurableSet t) :
    μ.restrict (s ∩ t) + μ.restrict (s \ t) = μ.restrict s :=
  restrict_inter_add_sdiff₀ s ht.nullMeasurableSet

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff
/-
**MeasureTheory.Measure.restrict_union_add_inter** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：restrict_union_add_inter (s : Set α) (ht : MeasurableSet t) : μ.restrict (
s union t) + μ.restrict (s inter t) = μ.restrict s + μ.restrict t
参数：s : Set α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_union_add_inter₀`：restrict_union_add_inte
r₀ (s : Set α) (ht : NullMeasurableSet t μ) : μ.restrict (s union t) + μ.restric
t (s inter t) = μ.restrict s + μ.rest…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t := by
  rw [← restrict_inter_add_sdiff₀ (s ∪ t) ht, union_inter_cancel_right, union_sdiff_right, ←
    restrict_inter_add_sdiff₀ s ht, add_comm, ← add_assoc, add_right_comm]
/-
**MeasureTheory.Measure.restrict_union_add_inter** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：restrict_union_add_inter (s : Set α) (ht : MeasurableSet t) : μ.restrict (
s union t) + μ.restrict (s inter t) = μ.restrict s + μ.restrict t
参数：s : Set α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_union_add_inter₀`：restrict_union_add_inte
r₀ (s : Set α) (ht : NullMeasurableSet t μ) : μ.restrict (s union t) + μ.restric
t (s inter t) = μ.restrict s + μ.rest…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t :=
  restrict_union_add_inter₀ s ht.nullMeasurableSet
/-
**MeasureTheory.Measure.restrict_union_add_inter'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：restrict_union_add_inter' (hs : MeasurableSet s) (t : Set α) : μ.restrict 
(s union t) + μ.restrict (s inter t) = μ.restrict s + μ.restrict t
参数：hs : MeasurableSet s；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.Measure.restrict_union_add_inter`：restrict_union_add_inter
 (s : Set α) (ht : MeasurableSet t) : μ.restrict (s union t) + μ.restrict (s int
er t) = μ.restrict s + μ.restrict t
-/
theorem restrict_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t := by
  simpa only [union_comm, inter_comm, add_comm] using restrict_union_add_inter t hs
/-
**MeasureTheory.Measure.restrict_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：restrict_union (h : Disjoint s t) (ht : MeasurableSet t) : μ.restrict (s u
nion t) = μ.restrict s + μ.restrict t
参数：h : Disjoint s t；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_union₀`：restrict_union₀ (h : AEDisjoint μ
 s t) (ht : NullMeasurableSet t μ) : μ.restrict (s union t) = μ.restrict s + μ.r
estrict t
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_union₀ (h : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t := by
  simp [← restrict_union_add_inter₀ s ht, restrict_zero_set h]
/-
**MeasureTheory.Measure.restrict_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：restrict_union (h : Disjoint s t) (ht : MeasurableSet t) : μ.restrict (s u
nion t) = μ.restrict s + μ.restrict t
参数：h : Disjoint s t；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_union₀`：restrict_union₀ (h : AEDisjoint μ
 s t) (ht : NullMeasurableSet t μ) : μ.restrict (s union t) = μ.restrict s + μ.r
estrict t
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_union (h : Disjoint s t) (ht : MeasurableSet t) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t :=
  restrict_union₀ h.aedisjoint ht.nullMeasurableSet
/-
**MeasureTheory.Measure.restrict_union'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：restrict_union' (h : Disjoint s t) (hs : MeasurableSet s) : μ.restrict (s 
union t) = μ.restrict s + μ.restrict t
参数：h : Disjoint s t；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `MeasureTheory.Measure.restrict_union`：restrict_union (h : Disjoint s t) 
(ht : MeasurableSet t) : μ.restrict (s union t) = μ.restrict s + μ.restrict t
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem restrict_union' (h : Disjoint s t) (hs : MeasurableSet s) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t := by
  rw [union_comm, restrict_union h.symm hs, add_comm]

@[simp]
/-
**MeasureTheory.Measure.restrict_add_restrict_compl** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：restrict_add_restrict_compl (hs : MeasurableSet s) : μ.restrict s + μ.rest
rict sᶜ = μ
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_union`：restrict_union (h : Disjoint s t) 
(ht : MeasurableSet t) : μ.restrict (s union t) = μ.restrict s + μ.restrict t
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
theorem restrict_add_restrict_compl (hs : MeasurableSet s) :
    μ.restrict s + μ.restrict sᶜ = μ := by
  rw [← restrict_union (@disjoint_compl_right (Set α) _ _) hs.compl, union_compl_self,
    restrict_univ]

@[simp]
/-
**MeasureTheory.Measure.restrict_compl_add_restrict** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：restrict_compl_add_restrict (hs : MeasurableSet s) : μ.restrict sᶜ + μ.res
trict s = μ
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.restrict_add_restrict_compl`：restrict_add_restrict
_compl (hs : MeasurableSet s) : μ.restrict s + μ.restrict sᶜ = μ
-/
theorem restrict_compl_add_restrict (hs : MeasurableSet s) : μ.restrict sᶜ + μ.restrict s = μ := by
  rw [add_comm, restrict_add_restrict_compl hs]
/-
**MeasureTheory.Measure.restrict_union_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：restrict_union_le (s s' : Set α) : μ.restrict (s union s') <= μ.restrict s
 + μ.restrict s'
参数：s s' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem restrict_union_le (s s' : Set α) : μ.restrict (s ∪ s') ≤ μ.restrict s + μ.restrict s' :=
  le_iff.2 fun t ht ↦ by
    simpa [ht, inter_union_distrib_left] using measure_union_le (t ∩ s) (t ∩ s')
/-
**MeasureTheory.Measure.restrict_iUnion_apply_ae** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：restrict_iUnion_apply_ae [Countable ι] {s : ι -> Set α} (hd : Pairwise (AE
Disjoint μ on s)) (hm : forall i, NullMeasurableSet (s i) μ) {t : Set α} (ht : M
easurableSet t) : μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t
参数：hd : Pairwise (AEDisjoint μ on s)；hm : forall i, NullMeasurableSet (s i) μ；ht
 : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_iUnion₀`：measure_iUnion₀ [Countable ι] {f : ι -> S
et α} (hd : Pairwise (AEDisjoint μ on f)) (h : forall i, NullMeasurableSet (f i)
 μ) : μ (⋃ i, f i) …
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `MeasureTheory.AEDisjoint.mono`：∀ {α : Type u_2} {m : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {s t u v : Set α},   MeasureTheory.AEDisjoint μ s 
t → u ⊆ s → v ⊆ t →…
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_iUnion_apply_ae [Countable ι] {s : ι → Set α} (hd : Pairwise (AEDisjoint μ on s))
    (hm : ∀ i, NullMeasurableSet (s i) μ) {t : Set α} (ht : MeasurableSet t) :
    μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t := by
  simp only [restrict_apply, ht, inter_iUnion]
  exact
    measure_iUnion₀ (hd.mono fun i j h => h.mono inter_subset_right inter_subset_right)
      fun i => ht.nullMeasurableSet.inter (hm i)
/-
**MeasureTheory.Measure.restrict_iUnion_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：restrict_iUnion_apply [Countable ι] {s : ι -> Set α} (hd : Pairwise (Disjo
int on s)) (hm : forall i, MeasurableSet (s i)) {t : Set α} (ht : MeasurableSet 
t) : μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t
参数：hd : Pairwise (Disjoint on s)；hm : forall i, MeasurableSet (s i)；ht : Measura
bleSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_apply_ae`：restrict_iUnion_apply_ae
 [Countable ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoint μ on s)) (hm : forall
 i, NullMeasurableSet (s i) μ) {t : …
· 使用定理 `Pairwise.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {f : ι → Set α},   Pairwise (Function.onFun D
isjoint f…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_iUnion_apply [Countable ι] {s : ι → Set α} (hd : Pairwise (Disjoint on s))
    (hm : ∀ i, MeasurableSet (s i)) {t : Set α} (ht : MeasurableSet t) :
    μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t :=
  restrict_iUnion_apply_ae hd.aedisjoint (fun i => (hm i).nullMeasurableSet) ht
/-
**MeasureTheory.Measure.restrict_iUnion_apply_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：restrict_iUnion_apply_eq_iSup [Countable ι] {s : ι -> Set α} (hd : Directe
d (· subseteq ·) s) {t : Set α} (ht : MeasurableSet t) : μ.restrict (⋃ i, s i) t
 = ⨆ i, μ.restrict (s i) t
参数：hd : Directed (· subseteq ·) s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Directed.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [Countable ι] {s : ι → Set α},   Directed
 (fun x1 x2 =…
· 使用定理 `Directed.mono_comp`：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β 
-> β -> Prop} {g : α -> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g
 y)) (hf…
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
-/
theorem restrict_iUnion_apply_eq_iSup [Countable ι] {s : ι → Set α} (hd : Directed (· ⊆ ·) s)
    {t : Set α} (ht : MeasurableSet t) : μ.restrict (⋃ i, s i) t = ⨆ i, μ.restrict (s i) t := by
  simp only [restrict_apply ht, inter_iUnion]
  rw [Directed.measure_iUnion]
  exacts [hd.mono_comp _ fun s₁ s₂ => inter_subset_inter_right _]

/-- The restriction of the pushforward measure is the pushforward of the restriction. For a version
assuming only `AEMeasurable`, see `restrict_map_of_aemeasurable`. -/
/-
**MeasureTheory.Measure.restrict_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：restrict_map {f : α -> β} (hf : Measurable f) {s : Set β} (hs : Measurable
Set s) : (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f
参数：hf : Measurable f；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The restriction of the pushforward measure is the pushforward of the restriction
. For a version
assuming only `AEMeasurable`, see `restrict_map_of_aemeasurable`.
-/
theorem restrict_map {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  ext fun t ht => by simp [*, hf ht]
/-
**MeasureTheory.Measure.restrict_inter_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：restrict_inter_toMeasurable (h : μ s != ∞) (ht : MeasurableSet t) (hst : s
 subseteq t) : μ.restrict (t inter toMeasurable μ s) = μ.restrict s
参数：h : μ s != ∞；ht : MeasurableSet t；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_inter`：measure_toMeasurable_i
nter {s t : Set α} (hs : MeasurableSet s) (ht : μ t != ∞) : μ (toMeasurable μ t 
inter s) = μ (t inter s)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem restrict_inter_toMeasurable (h : μ s ≠ ∞) (ht : MeasurableSet t) (hst : s ⊆ t) :
    μ.restrict (t ∩ toMeasurable μ s) = μ.restrict s := by
  ext u hu
  rw [restrict_apply hu, restrict_apply hu, inter_comm t, inter_comm, inter_assoc,
    measure_toMeasurable_inter (ht.inter hu) h]
  congr 1
  grind
/-
**MeasureTheory.Measure.restrict_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：restrict_toMeasurable (h : μ s != ∞) : μ.restrict (toMeasurable μ s) = μ.r
estrict s
参数：h : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.Measure.restrict_inter_toMeasurable`：restrict_inter_toMeas
urable (h : μ s != ∞) (ht : MeasurableSet t) (hst : s subseteq t) : μ.restrict (
t inter toMeasurable μ s) = μ.restrict …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem restrict_toMeasurable (h : μ s ≠ ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s := by
  simpa using restrict_inter_toMeasurable h MeasurableSet.univ (subset_univ _)
/-
**MeasureTheory.Measure.restrict_eq_self_of_ae_mem** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：restrict_eq_self_of_ae_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Meas
ure α⦄ (hs : forallᵐ x ∂μ, x in s) : μ.restrict s = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_univ`：eventuallyEq_univ {s : Set α} {l : Filter α} :
 s =ᶠ[l] univ ↔ s in l
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
theorem restrict_eq_self_of_ae_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄
    (hs : ∀ᵐ x ∂μ, x ∈ s) : μ.restrict s = μ :=
  calc
    μ.restrict s = μ.restrict univ := restrict_congr_set (eventuallyEq_univ.mpr hs)
    _ = μ := restrict_univ
/-
**MeasureTheory.Measure.restrict_congr_meas** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：restrict_congr_meas (hs : MeasurableSet s) : μ.restrict s = ν.restrict s ↔
 forall t subseteq s, MeasurableSet t -> μ t = ν t
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
theorem restrict_congr_meas (hs : MeasurableSet s) :
    μ.restrict s = ν.restrict s ↔ ∀ t ⊆ s, MeasurableSet t → μ t = ν t :=
  ⟨fun H t hts ht => by
    rw [← inter_eq_self_of_subset_left hts, ← restrict_apply ht, H, restrict_apply ht], fun H =>
    ext fun t ht => by
      rw [restrict_apply ht, restrict_apply ht, H _ inter_subset_right (ht.inter hs)]⟩
/-
**MeasureTheory.Measure.restrict_congr_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：restrict_congr_mono (hs : s subseteq t) (h : μ.restrict t = ν.restrict t) 
: μ.restrict s = ν.restrict s
参数：hs : s subseteq t；h : μ.restrict t = ν.restrict t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_restrict_of_subset`：restrict_restrict_of_
subset (h : s subseteq t) : (μ.restrict t).restrict s = μ.restrict s
-/
theorem restrict_congr_mono (hs : s ⊆ t) (h : μ.restrict t = ν.restrict t) :
    μ.restrict s = ν.restrict s := by
  rw [← restrict_restrict_of_subset hs, h, restrict_restrict_of_subset hs]

/-- If two measures agree on all measurable subsets of `s` and `t`, then they agree on all
measurable subsets of `s ∪ t`. -/
/-
**MeasureTheory.Measure.restrict_union_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：restrict_union_congr : μ.restrict (s union t) = ν.restrict (s union t) ↔ μ
.restrict s = ν.restrict s ∧ μ.restrict t = ν.restrict t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_congr_mono`：restrict_congr_mono (hs : s s
ubseteq t) (h : μ.restrict t = ν.restrict t) : μ.restrict s = ν.restrict s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `MeasureTheory.exists_measurable_superset₂`：exists_measurable_superset₂ (
μ ν : Measure α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 
μ s ∧ ν t = ν s
· 使用定理 `MeasureTheory.measure_union_congr_of_subset`：measure_union_congr_of_subs
et {t₁ t₂ : Set α} (hs : s₁ subseteq s₂) (hsμ : μ s₂ <= μ s₁) (ht : t₁ subseteq 
t₂) (htμ : μ t₂ <= μ t₁) : μ (s₁ …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_add_sdiff`：measure_add_sdiff (hs : NullMeasurableS
et s μ) (t : Set α) : μ s + μ (t \ s) = μ (s union t)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `Set.inter_sdiff_assoc`：inter_sdiff_assoc (a b c : Set α) : (a inter b) \
 c = a inter (b \ c)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If two measures agree on all measurable subsets of `s` and `t`, then they agree 
on all
measurable subsets of `s ∪ t`.
-/
theorem restrict_union_congr :
    μ.restrict (s ∪ t) = ν.restrict (s ∪ t) ↔
      μ.restrict s = ν.restrict s ∧ μ.restrict t = ν.restrict t := by
  refine ⟨fun h ↦ ⟨restrict_congr_mono subset_union_left h,
    restrict_congr_mono subset_union_right h⟩, ?_⟩
  rintro ⟨hs, ht⟩
  ext1 u hu
  simp only [restrict_apply hu, inter_union_distrib_left]
  rcases exists_measurable_superset₂ μ ν (u ∩ s) with ⟨US, hsub, hm, hμ, hν⟩
  calc
    μ (u ∩ s ∪ u ∩ t) = μ (US ∪ u ∩ t) :=
      measure_union_congr_of_subset hsub hμ.le Subset.rfl le_rfl
    _ = μ US + μ ((u ∩ t) \ US) := (measure_add_sdiff hm.nullMeasurableSet _).symm
    _ = restrict μ s u + restrict μ t (u \ US) := by
      simp only [restrict_apply, hu, hu.diff hm, hμ, ← inter_comm t, inter_sdiff_assoc]
    _ = restrict ν s u + restrict ν t (u \ US) := by rw [hs, ht]
    _ = ν US + ν ((u ∩ t) \ US) := by
      simp only [restrict_apply, hu, hu.diff hm, hν, ← inter_comm t, inter_sdiff_assoc]
    _ = ν (US ∪ u ∩ t) := measure_add_sdiff hm.nullMeasurableSet _
    _ = ν (u ∩ s ∪ u ∩ t) := .symm <| measure_union_congr_of_subset hsub hν.le Subset.rfl le_rfl
/-
**MeasureTheory.Measure.restrict_biUnion_finset_congr** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：restrict_biUnion_finset_congr {s : Finset ι} {t : ι -> Set α} : μ.restrict
 (⋃ i in s, t i) = ν.restrict (⋃ i in s, t i) ↔ forall i in s, μ.restrict (t i) 
= ν.restrict (t i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `MeasureTheory.Measure.restrict_union_congr`：restrict_union_congr : μ.res
trict (s union t) = ν.restrict (s union t) ↔ μ.restrict s = ν.restrict s ∧ μ.res
trict t = ν.restrict t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem restrict_biUnion_finset_congr {s : Finset ι} {t : ι → Set α} :
    μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
      ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ hs =>
    simp only [forall_eq_or_imp, iUnion_iUnion_eq_or_left, Finset.mem_insert]
    rw [restrict_union_congr, ← hs]
/-
**MeasureTheory.Measure.restrict_iUnion_congr** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：restrict_iUnion_congr [Countable ι] {s : ι -> Set α} : μ.restrict (⋃ i, s 
i) = ν.restrict (⋃ i, s i) ↔ forall i, μ.restrict (s i) = ν.restrict (s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_congr_mono`：restrict_congr_mono (hs : s s
ubseteq t) (h : μ.restrict t = ν.restrict t) : μ.restrict s = ν.restrict s
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_eq_iUnion_finset`：iUnion_eq_iUnion_finset (s : ι -> Set α) : 
⋃ i, s i = ⋃ t : Finset ι, ⋃ i in t, s i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_apply_eq_iSup`：restrict_iUnion_app
ly_eq_iSup [Countable ι] {s : ι -> Set α} (hd : Directed (· subseteq ·) s) {t : 
Set α} (ht : MeasurableSet t) : μ.restric…
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_biUnion_finset_congr`：restrict_biUnion_fi
nset_congr {s : Finset ι} {t : ι -> Set α} : μ.restrict (⋃ i in s, t i) = ν.rest
rict (⋃ i in s, t i) ↔ forall i in s, μ.r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_iUnion_congr [Countable ι] {s : ι → Set α} :
    μ.restrict (⋃ i, s i) = ν.restrict (⋃ i, s i) ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) := by
  refine ⟨fun h i => restrict_congr_mono (subset_iUnion _ _) h, fun h => ?_⟩
  ext1 t ht
  have D : Directed (· ⊆ ·) fun t : Finset ι => ⋃ i ∈ t, s i :=
    Monotone.directed_le fun t₁ t₂ ht => biUnion_subset_biUnion_left ht
  rw [iUnion_eq_iUnion_finset]
  simp only [restrict_iUnion_apply_eq_iSup D ht, restrict_biUnion_finset_congr.2 fun i _ => h i]
/-
**MeasureTheory.Measure.restrict_biUnion_congr** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：restrict_biUnion_congr {s : Set ι} {t : ι -> Set α} (hc : s.Countable) : μ
.restrict (⋃ i in s, t i) = ν.restrict (⋃ i in s, t i) ↔ forall i in s, μ.restri
ct (t i) = ν.restrict (t i)
参数：hc : s.Countable。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem restrict_biUnion_congr {s : Set ι} {t : ι → Set α} (hc : s.Countable) :
    μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
      ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) := by
  have := hc.toEncodable
  simp only [biUnion_eq_iUnion, SetCoe.forall', restrict_iUnion_congr]
/-
**MeasureTheory.Measure.restrict_sUnion_congr** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：restrict_sUnion_congr {S : Set (Set α)} (hc : S.Countable) : μ.restrict (⋃
₀ S) = ν.restrict (⋃₀ S) ↔ forall s in S, μ.restrict s = ν.restrict s
参数：Set α；hc : S.Countable。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `MeasureTheory.Measure.restrict_biUnion_congr`：restrict_biUnion_congr {s 
: Set ι} {t : ι -> Set α} (hc : s.Countable) : μ.restrict (⋃ i in s, t i) = ν.re
strict (⋃ i in s, t i) ↔ forall i …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem restrict_sUnion_congr {S : Set (Set α)} (hc : S.Countable) :
    μ.restrict (⋃₀ S) = ν.restrict (⋃₀ S) ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s := by
  rw [sUnion_eq_biUnion, restrict_biUnion_congr hc]

/-- This lemma shows that `Inf` and `restrict` commute for measures. -/
/-
**MeasureTheory.Measure.restrict_sInf_eq_sInf_restrict** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：restrict_sInf_eq_sInf_restrict {m0 : MeasurableSpace α} {m : Set (Measure 
α)} (hm : m.Nonempty) (ht : MeasurableSet t) : (sInf m).restrict t = sInf ((fun 
μ : Measure α => μ.restrict t) '' m)
参数：Measure α；hm : m.Nonempty；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sInf_apply`：sInf_apply (hs : MeasurableSet s) : sI
nf m s = sInf (toOuterMeasure '' m) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `MeasureTheory.Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict
`：restrict_toOuterMeasure_eq_toOuterMeasure_restrict (h : MeasurableSet s) : (μ.
restrict s).toOuterMeasure = OuterMeasure.restrict s μ.toOuter…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.OuterMeasure.restrict_sInf_eq_sInf_restrict`：restrict_sInf
_eq_sInf_restrict (m : Set (OuterMeasure α)) {s : Set α} (hm : m.Nonempty) : res
trict s (sInf m) = sInf (restrict s '' m)
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.OuterMeasure.restrict_apply`：restrict_apply (s t : Set α) 
(m : OuterMeasure α) : restrict s m t = m (t inter s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This lemma shows that `Inf` and `restrict` commute for measures.
-/
theorem restrict_sInf_eq_sInf_restrict {m0 : MeasurableSpace α} {m : Set (Measure α)}
    (hm : m.Nonempty) (ht : MeasurableSet t) :
    (sInf m).restrict t = sInf ((fun μ : Measure α => μ.restrict t) '' m) := by
  ext1 s hs
  simp_rw [sInf_apply hs, restrict_apply hs, sInf_apply (MeasurableSet.inter hs ht),
    Set.image_image, restrict_toOuterMeasure_eq_toOuterMeasure_restrict ht, ←
    Set.image_image _ toOuterMeasure, ← OuterMeasure.restrict_sInf_eq_sInf_restrict _ (hm.image _),
    OuterMeasure.restrict_apply]
/-
**MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure`。
形式化陈述：exists_mem_of_measure_ne_zero_of_ae (hs : μ s != 0) {p : α -> Prop} (hp : 
forallᵐ x ∂μ.restrict s, p x) : exists x, x in s ∧ p x
参数：hs : μ s != 0；hp : forallᵐ x ∂μ.restrict s, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.frequently_ae_mem_iff`：frequently_ae_mem_iff {s : Set α} :
 (existsᵐ a ∂μ, a in s) ↔ μ s != 0
· 使用定理 `MeasureTheory.Measure.restrict_apply_self`：restrict_apply_self (s : Set 
α) : (μ.restrict s) s = μ s
-/
theorem exists_mem_of_measure_ne_zero_of_ae (hs : μ s ≠ 0) {p : α → Prop}
    (hp : ∀ᵐ x ∂μ.restrict s, p x) : ∃ x, x ∈ s ∧ p x := by
  rw [← μ.restrict_apply_self, ← frequently_ae_mem_iff] at hs
  exact (hs.and_eventually hp).exists

/-- If a quasi-measure-preserving map `f` maps a set `s` to a set `t`,
then it is quasi-measure-preserving with respect to the restrictions of the measures. -/
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.restrict** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {m0 : MeasurableSpace α} [inst : Measurabl
eSpace β] {μ : MeasureTheory.Measure α}   {s : Set α} {ν : MeasureTheory.Measure
 β} {f : α → β},   MeasureTheory.Measure.QuasiMeasurePreserving f μ ν →     ∀ {t
 : Set β}, Set.MapsTo f s t → MeasureTheory.Measure.QuasiMeasurePreserving f (μ.
restrict s) (ν.restrict t)
参数：μ.restrict s；ν.restrict t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_inter`：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f
 ⁻¹' s inter f ⁻¹' t
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null`：preimage_nul
l (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) : μa (f ⁻¹' s
) = 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)

--- 原说明 ---
If a quasi-measure-preserving map `f` maps a set `s` to a set `t`,
then it is quasi-measure-preserving with respect to the restrictions of the meas
ures.
-/
theorem QuasiMeasurePreserving.restrict {ν : Measure β} {f : α → β}
    (hf : QuasiMeasurePreserving f μ ν) {t : Set β} (hmaps : MapsTo f s t) :
    QuasiMeasurePreserving f (μ.restrict s) (ν.restrict t) where
  measurable := hf.measurable
  absolutelyContinuous := by
    refine AbsolutelyContinuous.mk fun u hum ↦ ?_
    suffices ν (u ∩ t) = 0 → μ (f ⁻¹' u ∩ s) = 0 by simpa [hum, hf.measurable, hf.measurable hum]
    refine fun hu ↦ measure_mono_null ?_ (hf.preimage_null hu)
    rw [preimage_inter]
    gcongr
    assumption

/-! ### Extensionality results -/

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `Union`). -/
/-
**MeasureTheory.Measure.ext_iff_of_iUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：ext_iff_of_iUnion_eq_univ [Countable ι] {s : ι -> Set α} (hs : ⋃ i, s i = 
univ) : μ = ν ↔ forall i, μ.restrict (s i) = ν.restrict (s i)
参数：hs : ⋃ i, s i = univ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_congr`：restrict_iUnion_congr [Coun
table ι] {s : ι -> Set α} : μ.restrict (⋃ i, s i) = ν.restrict (⋃ i, s i) ↔ fora
ll i, μ.restrict (s i) = ν.restri…
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two measures are equal if they have equal restrictions on a spanning collection 
of sets
  (formulated using `Union`).
-/
theorem ext_iff_of_iUnion_eq_univ [Countable ι] {s : ι → Set α} (hs : ⋃ i, s i = univ) :
    μ = ν ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) := by
  rw [← restrict_iUnion_congr, hs, restrict_univ, restrict_univ]

alias ⟨_, ext_of_iUnion_eq_univ⟩ := ext_iff_of_iUnion_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `biUnion`). -/
/-
**MeasureTheory.Measure.ext_iff_of_biUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：ext_iff_of_biUnion_eq_univ {S : Set ι} {s : ι -> Set α} (hc : S.Countable)
 (hs : ⋃ i in S, s i = univ) : μ = ν ↔ forall i in S, μ.restrict (s i) = ν.restr
ict (s i)
参数：hc : S.Countable；hs : ⋃ i in S, s i = univ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_biUnion_congr`：restrict_biUnion_congr {s 
: Set ι} {t : ι -> Set α} (hc : s.Countable) : μ.restrict (⋃ i in s, t i) = ν.re
strict (⋃ i in s, t i) ↔ forall i …
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two measures are equal if they have equal restrictions on a spanning collection 
of sets
  (formulated using `biUnion`).
-/
theorem ext_iff_of_biUnion_eq_univ {S : Set ι} {s : ι → Set α} (hc : S.Countable)
    (hs : ⋃ i ∈ S, s i = univ) : μ = ν ↔ ∀ i ∈ S, μ.restrict (s i) = ν.restrict (s i) := by
  rw [← restrict_biUnion_congr hc, hs, restrict_univ, restrict_univ]

alias ⟨_, ext_of_biUnion_eq_univ⟩ := ext_iff_of_biUnion_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `sUnion`). -/
/-
**MeasureTheory.Measure.ext_iff_of_sUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：ext_iff_of_sUnion_eq_univ {S : Set (Set α)} (hc : S.Countable) (hs : ⋃₀ S 
= univ) : μ = ν ↔ forall s in S, μ.restrict s = ν.restrict s
参数：Set α；hc : S.Countable；hs : ⋃₀ S = univ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_iff_of_biUnion_eq_univ`：ext_iff_of_biUnion_eq_
univ {S : Set ι} {s : ι -> Set α} (hc : S.Countable) (hs : ⋃ i in S, s i = univ)
 : μ = ν ↔ forall i in S, μ.restrict (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i

--- 原说明 ---
Two measures are equal if they have equal restrictions on a spanning collection 
of sets
  (formulated using `sUnion`).
-/
theorem ext_iff_of_sUnion_eq_univ {S : Set (Set α)} (hc : S.Countable) (hs : ⋃₀ S = univ) :
    μ = ν ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s :=
  ext_iff_of_biUnion_eq_univ hc <| by rwa [← sUnion_eq_biUnion]

alias ⟨_, ext_of_sUnion_eq_univ⟩ := ext_iff_of_sUnion_eq_univ
/-
**MeasureTheory.Measure.ext_of_generateFrom_of_cover** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：ext_of_generateFrom_of_cover {S T : Set (Set α)} (h_gen : ‹_› = generateFr
om S) (hc : T.Countable) (h_inter : IsPiSystem S) (hU : ⋃₀ T = univ) (htop : for
all t in T, μ t != ∞) (ST_eq : forall t in T, forall s in S, μ (s inter t) = ν (
s inter t)) (T_eq : forall t in T, μ t = ν t) : μ = ν
参数：Set α；h_gen : ‹_› = generateFrom S；hc : T.Countable；h_inter : IsPiSystem S；hU
 : ⋃₀ T = univ；htop : forall t in T, μ t != ∞；ST_eq : forall t in T, forall s in
 S, μ (s inter t) = ν (s inter t)；T_eq : forall t in T, μ t = ν t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_sUnion_eq_univ`：∀ {α : Type u_2} {m0 : Meas
urableSpace α} {μ ν : MeasureTheory.Measure α} {S : Set (Set α)},   S.Countable 
→ ⋃₀ S = Set.univ → (∀ s ∈ S, μ.r…
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `ENNReal.add_right_inj`：add_right_inj (h : a != ∞) : a + b = a + c ↔ b = 
c
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem ext_of_generateFrom_of_cover {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
    (hc : T.Countable) (h_inter : IsPiSystem S) (hU : ⋃₀ T = univ) (htop : ∀ t ∈ T, μ t ≠ ∞)
    (ST_eq : ∀ t ∈ T, ∀ s ∈ S, μ (s ∩ t) = ν (s ∩ t)) (T_eq : ∀ t ∈ T, μ t = ν t) : μ = ν := by
  refine ext_of_sUnion_eq_univ hc hU fun t ht => ?_
  ext1 u hu
  simp only [restrict_apply hu]
  induction u, hu using induction_on_inter h_gen h_inter with
  | empty => simp only [Set.empty_inter, measure_empty]
  | basic u hu => exact ST_eq _ ht _ hu
  | compl u hu ihu =>
    have := T_eq t ht
    rw [Set.inter_comm] at ihu ⊢
    rwa [← measure_inter_add_sdiff t hu, ← measure_inter_add_sdiff t hu, ← ihu,
      ENNReal.add_right_inj] at this
    exact ne_top_of_le_ne_top (htop t ht) (measure_mono Set.inter_subset_left)
  | iUnion f hfd hfm ihf =>
    simp only [← restrict_apply (hfm _), ← restrict_apply (MeasurableSet.iUnion hfm)] at ihf ⊢
    simp only [measure_iUnion hfd hfm, ihf]

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on an increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `sUnion`. -/
/-
**MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure`。
形式化陈述：ext_of_generateFrom_of_cover_subset {S T : Set (Set α)} (h_gen : ‹_› = gen
erateFrom S) (h_inter : IsPiSystem S) (h_sub : T subseteq S) (hc : T.Countable) 
(hU : ⋃₀ T = univ) (htop : forall s in T, μ s != ∞) (h_eq : forall s in S, μ s =
 ν s) : μ = ν
参数：Set α；h_gen : ‹_› = generateFrom S；h_inter : IsPiSystem S；h_sub : T subseteq 
S；hc : T.Countable；hU : ⋃₀ T = univ；htop : forall s in T, μ s != ∞；h_eq : forall
 s in S, μ s = ν s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_generateFrom_of_cover`：ext_of_generateFrom_
of_cover {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S) (hc : T.Countable) (
h_inter : IsPiSystem S) (hU : ⋃₀ T = uni…
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two measures are equal if they are equal on the π-system generating the σ-algebr
a,
  and they are both finite on an increasing spanning sequence of sets in the π-s
ystem.
  This lemma is formulated using `sUnion`.
-/
theorem ext_of_generateFrom_of_cover_subset {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
    (h_inter : IsPiSystem S) (h_sub : T ⊆ S) (hc : T.Countable) (hU : ⋃₀ T = univ)
    (htop : ∀ s ∈ T, μ s ≠ ∞) (h_eq : ∀ s ∈ S, μ s = ν s) : μ = ν := by
  refine ext_of_generateFrom_of_cover h_gen hc h_inter hU htop ?_ fun t ht => h_eq t (h_sub ht)
  intro t ht s hs; rcases (s ∩ t).eq_empty_or_nonempty with H | H
  · simp only [H, measure_empty]
  · exact h_eq _ (h_inter _ hs _ (h_sub ht) H)

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on an increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `iUnion`.
  `FiniteSpanningSetsIn.ext` is a reformulation of this lemma. -/
/-
**MeasureTheory.Measure.ext_of_generateFrom_of_iUnion** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：ext_of_generateFrom_of_iUnion (C : Set (Set α)) (B : Nat -> Set α) (hA : ‹
_› = generateFrom C) (hC : IsPiSystem C) (h1B : ⋃ i, B i = univ) (h2B : forall i
, B i in C) (hμB : forall i, μ (B i) != ∞) (h_eq : forall s in C, μ s = ν s) : μ
 = ν
参数：C : Set (Set α)；B : Nat -> Set α；hA : ‹_› = generateFrom C；hC : IsPiSystem C；
h1B : ⋃ i, B i = univ；h2B : forall i, B i in C；hμB : forall i, μ (B i) != ∞；h_eq
 : forall s in C, μ s = ν s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset`：ext_of_genera
teFrom_of_cover_subset {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S) (h_int
er : IsPiSystem S) (h_sub : T subseteq S) (hc :…
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableNat`：Countable ℕ

--- 原说明 ---
Two measures are equal if they are equal on the π-system generating the σ-algebr
a,
  and they are both finite on an increasing spanning sequence of sets in the π-s
ystem.
  This lemma is formulated using `iUnion`.
  `FiniteSpanningSetsIn.ext` is a reformulation of this lemma.
-/
theorem ext_of_generateFrom_of_iUnion (C : Set (Set α)) (B : ℕ → Set α) (hA : ‹_› = generateFrom C)
    (hC : IsPiSystem C) (h1B : ⋃ i, B i = univ) (h2B : ∀ i, B i ∈ C) (hμB : ∀ i, μ (B i) ≠ ∞)
    (h_eq : ∀ s ∈ C, μ s = ν s) : μ = ν := by
  refine ext_of_generateFrom_of_cover_subset hA hC ?_ (countable_range B) h1B ?_ h_eq
  · rintro _ ⟨i, rfl⟩
    apply h2B
  · rintro _ ⟨i, rfl⟩
    apply hμB

@[simp]
/-
**MeasureTheory.Measure.restrict_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：restrict_sum (μ : ι -> Measure α) {s : Set α} (hs : MeasurableSet s) : (su
m μ).restrict s = sum fun i => (μ i).restrict s
参数：μ : ι -> Measure α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_sum (μ : ι → Measure α) {s : Set α} (hs : MeasurableSet s) :
    (sum μ).restrict s = sum fun i => (μ i).restrict s :=
  ext fun t ht => by simp only [sum_apply, restrict_apply, ht, ht.inter hs]

@[simp]
/-
**MeasureTheory.Measure.restrict_sum_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：restrict_sum_of_countable [Countable ι] (μ : ι -> Measure α) (s : Set α) :
 (sum μ).restrict s = sum fun i => (μ i).restrict s
参数：μ : ι -> Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.sum_apply_of_countable`：sum_apply_of_countable [Co
untable ι] (f : ι -> Measure α) (s : Set α) : sum f s = ∑' i, f i s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_sum_of_countable [Countable ι] (μ : ι → Measure α) (s : Set α) :
    (sum μ).restrict s = sum fun i => (μ i).restrict s := by
  ext t ht
  simp_rw [sum_apply _ ht, restrict_apply ht, sum_apply_of_countable]
/-
**MeasureTheory.Measure.AbsolutelyContinuous.restrict** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},
   μ.AbsolutelyContinuous ν → ∀ (s : Set α), (μ.restrict s).AbsolutelyContinuous
 (ν.restrict s)
参数：s : Set α；μ.restrict s；ν.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
-/
lemma AbsolutelyContinuous.restrict (h : μ ≪ ν) (s : Set α) : μ.restrict s ≪ ν.restrict s := by
  refine Measure.AbsolutelyContinuous.mk (fun t ht htν ↦ ?_)
  rw [restrict_apply ht] at htν ⊢
  exact h htν
/-
**MeasureTheory.Measure.restrict_iUnion_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：restrict_iUnion_ae [Countable ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoi
nt μ on s)) (hm : forall i, NullMeasurableSet (s i) μ) : μ.restrict (⋃ i, s i) =
 sum fun i => μ.restrict (s i)
参数：hd : Pairwise (AEDisjoint μ on s)；hm : forall i, NullMeasurableSet (s i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_apply_ae`：restrict_iUnion_apply_ae
 [Countable ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoint μ on s)) (hm : forall
 i, NullMeasurableSet (s i) μ) {t : …
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_iUnion_ae [Countable ι] {s : ι → Set α} (hd : Pairwise (AEDisjoint μ on s))
    (hm : ∀ i, NullMeasurableSet (s i) μ) : μ.restrict (⋃ i, s i) = sum fun i => μ.restrict (s i) :=
  ext fun t ht => by simp only [sum_apply _ ht, restrict_iUnion_apply_ae hd hm ht]
/-
**MeasureTheory.Measure.restrict_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：restrict_iUnion [Countable ι] {s : ι -> Set α} (hd : Pairwise (Disjoint on
 s)) (hm : forall i, MeasurableSet (s i)) : μ.restrict (⋃ i, s i) = sum fun i =>
 μ.restrict (s i)
参数：hd : Pairwise (Disjoint on s)；hm : forall i, MeasurableSet (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_ae`：restrict_iUnion_ae [Countable 
ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoint μ on s)) (hm : forall i, NullMeas
urableSet (s i) μ) : μ.restric…
· 使用定理 `Pairwise.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {f : ι → Set α},   Pairwise (Function.onFun D
isjoint f…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem restrict_iUnion [Countable ι] {s : ι → Set α} (hd : Pairwise (Disjoint on s))
    (hm : ∀ i, MeasurableSet (s i)) : μ.restrict (⋃ i, s i) = sum fun i => μ.restrict (s i) :=
  restrict_iUnion_ae hd.aedisjoint fun i => (hm i).nullMeasurableSet
/-
**MeasureTheory.Measure.restrict_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：restrict_biUnion {s : ι -> Set α} {T : Set ι} (hT : Countable T) (hd : T.P
airwise (Disjoint on s)) (hm : forall i, MeasurableSet (s i)) : μ.restrict (⋃ i 
in T, s i) = sum fun (i : T) => μ.restrict (s i)
参数：hT : Countable T；hd : T.Pairwise (Disjoint on s)；hm : forall i, MeasurableSet
 (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `MeasureTheory.Measure.restrict_iUnion`：restrict_iUnion [Countable ι] {s 
: ι -> Set α} (hd : Pairwise (Disjoint on s)) (hm : forall i, MeasurableSet (s i
)) : μ.restrict (⋃ i, s i) …
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
-/
theorem restrict_biUnion {s : ι → Set α} {T : Set ι} (hT : Countable T)
    (hd : T.Pairwise (Disjoint on s)) (hm : ∀ i, MeasurableSet (s i)) :
    μ.restrict (⋃ i ∈ T, s i) = sum fun (i : T) => μ.restrict (s i) := by
  rw [Set.biUnion_eq_iUnion]
  exact restrict_iUnion (fun i j hij ↦ hd i.coe_prop j.coe_prop (Subtype.coe_ne_coe.mpr hij)) (hm ·)
/-
**MeasureTheory.Measure.restrict_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：restrict_biUnion_finset {s : ι -> Set α} {T : Finset ι} (hd : (T : Set ι).
Pairwise (Disjoint on s)) (hm : forall i, MeasurableSet (s i)) : μ.restrict (⋃ i
 in T, s i) = sum fun (i : T) => μ.restrict (s i)
参数：hd : (T : Set ι).Pairwise (Disjoint on s)；hm : forall i, MeasurableSet (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_biUnion`：restrict_biUnion {s : ι -> Set α
} {T : Set ι} (hT : Countable T) (hd : T.Pairwise (Disjoint on s)) (hm : forall 
i, MeasurableSet (s i)) : μ.…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem restrict_biUnion_finset {s : ι → Set α} {T : Finset ι}
    (hd : (T : Set ι).Pairwise (Disjoint on s)) (hm : ∀ i, MeasurableSet (s i)) :
    μ.restrict (⋃ i ∈ T, s i) = sum fun (i : T) => μ.restrict (s i) :=
  restrict_biUnion (T := (T : Set ι)) Finite.to_countable hd hm
/-
**MeasureTheory.Measure.restrict_iUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：restrict_iUnion_le [Countable ι] {s : ι -> Set α} : μ.restrict (⋃ i, s i) 
<= sum fun i => μ.restrict (s i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem restrict_iUnion_le [Countable ι] {s : ι → Set α} :
    μ.restrict (⋃ i, s i) ≤ sum fun i => μ.restrict (s i) :=
  le_iff.2 fun t ht ↦ by simpa [ht, inter_iUnion] using measure_iUnion_le (t ∩ s ·)
/-
**MeasureTheory.Measure.restrict_biUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：restrict_biUnion_le {s : ι -> Set α} {T : Set ι} (hT : Countable T) : μ.re
strict (⋃ i in T, s i) <= sum fun (i : T) => μ.restrict (s i)
参数：hT : Countable T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measure_biUnion_le`：measure_biUnion_le {I : Set ι} (μ : F)
 (hI : I.Countable) (s : ι -> Set α) : μ (⋃ i in I, s i) <= ∑' i : I, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem restrict_biUnion_le {s : ι → Set α} {T : Set ι} (hT : Countable T) :
    μ.restrict (⋃ i ∈ T, s i) ≤ sum fun (i : T) => μ.restrict (s i) :=
  le_iff.2 fun t ht ↦ by simpa [ht, inter_iUnion] using measure_biUnion_le μ hT (t ∩ s ·)

end Measure

@[simp]
/-
**MeasureTheory.ae_restrict_iUnion_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_iUnion_eq [Countable ι] (s : ι -> Set α) : ae (μ.restrict (⋃ i
, s i)) = ⨆ i, ae (μ.restrict (s i))
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_le`：restrict_iUnion_le [Countable 
ι] {s : ι -> Set α} : μ.restrict (⋃ i, s i) <= sum fun i => μ.restrict (s i)
· 使用定理 `MeasureTheory.Measure.ae_sum_eq`：ae_sum_eq [Countable ι] (μ : ι -> Measu
re α) : ae (sum μ) = ⨆ i, ae (μ i)
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem ae_restrict_iUnion_eq [Countable ι] (s : ι → Set α) :
    ae (μ.restrict (⋃ i, s i)) = ⨆ i, ae (μ.restrict (s i)) :=
  le_antisymm ((ae_sum_eq fun i => μ.restrict (s i)) ▸ ae_mono restrict_iUnion_le) <|
    iSup_le fun i => ae_mono <| restrict_mono (subset_iUnion s i) le_rfl

@[simp]
/-
**MeasureTheory.ae_restrict_union_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_union_eq (s t : Set α) : ae (μ.restrict (s union t)) = ae (μ.r
estrict s) ⊔ ae (μ.restrict t)
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `MeasureTheory.ae_restrict_iUnion_eq`：ae_restrict_iUnion_eq [Countable ι]
 (s : ι -> Set α) : ae (μ.restrict (⋃ i, s i)) = ⨆ i, ae (μ.restrict (s i))
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ae_restrict_union_eq (s t : Set α) :
    ae (μ.restrict (s ∪ t)) = ae (μ.restrict s) ⊔ ae (μ.restrict t) := by
  simp [union_eq_iUnion, iSup_bool_eq]
/-
**MeasureTheory.ae_restrict_biUnion_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：ae_restrict_biUnion_eq (s : ι -> Set α) {t : Set ι} (ht : t.Countable) : a
e (μ.restrict (⋃ i in t, s i)) = ⨆ i in t, ae (μ.restrict (s i))
参数：s : ι -> Set α；ht : t.Countable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `MeasureTheory.ae_restrict_iUnion_eq`：ae_restrict_iUnion_eq [Countable ι]
 (s : ι -> Set α) : ae (μ.restrict (⋃ i, s i)) = ⨆ i, ae (μ.restrict (s i))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
-/
theorem ae_restrict_biUnion_eq (s : ι → Set α) {t : Set ι} (ht : t.Countable) :
    ae (μ.restrict (⋃ i ∈ t, s i)) = ⨆ i ∈ t, ae (μ.restrict (s i)) := by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion, ae_restrict_iUnion_eq, ← iSup_subtype'']
/-
**MeasureTheory.ae_restrict_biUnion_finset_eq** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：ae_restrict_biUnion_finset_eq (s : ι -> Set α) (t : Finset ι) : ae (μ.rest
rict (⋃ i in t, s i)) = ⨆ i in t, ae (μ.restrict (s i))
参数：s : ι -> Set α；t : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_restrict_biUnion_eq`：ae_restrict_biUnion_eq (s : ι -> S
et α) {t : Set ι} (ht : t.Countable) : ae (μ.restrict (⋃ i in t, s i)) = ⨆ i in 
t, ae (μ.restrict (s i))
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
-/
theorem ae_restrict_biUnion_finset_eq (s : ι → Set α) (t : Finset ι) :
    ae (μ.restrict (⋃ i ∈ t, s i)) = ⨆ i ∈ t, ae (μ.restrict (s i)) :=
  ae_restrict_biUnion_eq s t.countable_toSet
/-
**MeasureTheory.ae_restrict_iUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：ae_restrict_iUnion_iff [Countable ι] (s : ι -> Set α) (p : α -> Prop) : (f
orallᵐ x ∂μ.restrict (⋃ i, s i), p x) ↔ forall i, forallᵐ x ∂μ.restrict (s i), p
 x
参数：s : ι -> Set α；p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iUnion_eq`：ae_restrict_iUnion_eq [Countable ι]
 (s : ι -> Set α) : ae (μ.restrict (⋃ i, s i)) = ⨆ i, ae (μ.restrict (s i))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_restrict_iUnion_iff [Countable ι] (s : ι → Set α) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i, s i), p x) ↔ ∀ i, ∀ᵐ x ∂μ.restrict (s i), p x := by simp
/-
**MeasureTheory.ae_restrict_union_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_union_iff (s t : Set α) (p : α -> Prop) : (forallᵐ x ∂μ.restri
ct (s union t), p x) ↔ (forallᵐ x ∂μ.restrict s, p x) ∧ forallᵐ x ∂μ.restrict t,
 p x
参数：s t : Set α；p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_union_eq`：ae_restrict_union_eq (s t : Set α) :
 ae (μ.restrict (s union t)) = ae (μ.restrict s) ⊔ ae (μ.restrict t)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_restrict_union_iff (s t : Set α) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (s ∪ t), p x) ↔ (∀ᵐ x ∂μ.restrict s, p x) ∧ ∀ᵐ x ∂μ.restrict t, p x := by simp
/-
**MeasureTheory.ae_restrict_biUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：ae_restrict_biUnion_iff (s : ι -> Set α) {t : Set ι} (ht : t.Countable) (p
 : α -> Prop) : (forallᵐ x ∂μ.restrict (⋃ i in t, s i), p x) ↔ forall i in t, fo
rallᵐ x ∂μ.restrict (s i), p x
参数：s : ι -> Set α；ht : t.Countable；p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_biUnion_eq`：ae_restrict_biUnion_eq (s : ι -> S
et α) {t : Set ι} (ht : t.Countable) : ae (μ.restrict (⋃ i in t, s i)) = ⨆ i in 
t, ae (μ.restrict (s i))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_restrict_biUnion_iff (s : ι → Set α) {t : Set ι} (ht : t.Countable) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i ∈ t, s i), p x) ↔ ∀ i ∈ t, ∀ᵐ x ∂μ.restrict (s i), p x := by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_eq s ht, mem_iSup]

@[simp]
/-
**MeasureTheory.ae_restrict_biUnion_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：ae_restrict_biUnion_finset_iff (s : ι -> Set α) (t : Finset ι) (p : α -> P
rop) : (forallᵐ x ∂μ.restrict (⋃ i in t, s i), p x) ↔ forall i in t, forallᵐ x ∂
μ.restrict (s i), p x
参数：s : ι -> Set α；t : Finset ι；p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_biUnion_finset_eq`：ae_restrict_biUnion_finset_
eq (s : ι -> Set α) (t : Finset ι) : ae (μ.restrict (⋃ i in t, s i)) = ⨆ i in t,
 ae (μ.restrict (s i))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_restrict_biUnion_finset_iff (s : ι → Set α) (t : Finset ι) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i ∈ t, s i), p x) ↔ ∀ i ∈ t, ∀ᵐ x ∂μ.restrict (s i), p x := by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_finset_eq s, mem_iSup]
/-
**MeasureTheory.ae_eq_restrict_iUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：ae_eq_restrict_iUnion_iff [Countable ι] (s : ι -> Set α) (f g : α -> δ) : 
f =ᵐ[μ.restrict (⋃ i, s i)] g ↔ forall i, f =ᵐ[μ.restrict (s i)] g
参数：s : ι -> Set α；f g : α -> δ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iUnion_eq`：ae_restrict_iUnion_eq [Countable ι]
 (s : ι -> Set α) : ae (μ.restrict (⋃ i, s i)) = ⨆ i, ae (μ.restrict (s i))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_eq_restrict_iUnion_iff [Countable ι] (s : ι → Set α) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i, s i)] g ↔ ∀ i, f =ᵐ[μ.restrict (s i)] g := by
  simp_rw [EventuallyEq, ae_restrict_iUnion_eq, eventually_iSup]
/-
**MeasureTheory.ae_eq_restrict_biUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：ae_eq_restrict_biUnion_iff (s : ι -> Set α) {t : Set ι} (ht : t.Countable)
 (f g : α -> δ) : f =ᵐ[μ.restrict (⋃ i in t, s i)] g ↔ forall i in t, f =ᵐ[μ.res
trict (s i)] g
参数：s : ι -> Set α；ht : t.Countable；f g : α -> δ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_biUnion_eq`：ae_restrict_biUnion_eq (s : ι -> S
et α) {t : Set ι} (ht : t.Countable) : ae (μ.restrict (⋃ i in t, s i)) = ⨆ i in 
t, ae (μ.restrict (s i))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_eq_restrict_biUnion_iff (s : ι → Set α) {t : Set ι} (ht : t.Countable) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i ∈ t, s i)] g ↔ ∀ i ∈ t, f =ᵐ[μ.restrict (s i)] g := by
  simp_rw [ae_restrict_biUnion_eq s ht, EventuallyEq, eventually_iSup]
/-
**MeasureTheory.ae_eq_restrict_biUnion_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：ae_eq_restrict_biUnion_finset_iff (s : ι -> Set α) (t : Finset ι) (f g : α
 -> δ) : f =ᵐ[μ.restrict (⋃ i in t, s i)] g ↔ forall i in t, f =ᵐ[μ.restrict (s 
i)] g
参数：s : ι -> Set α；t : Finset ι；f g : α -> δ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_restrict_biUnion_iff`：ae_eq_restrict_biUnion_iff (s 
: ι -> Set α) {t : Set ι} (ht : t.Countable) (f g : α -> δ) : f =ᵐ[μ.restrict (⋃
 i in t, s i)] g ↔ forall i in…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
-/
theorem ae_eq_restrict_biUnion_finset_iff (s : ι → Set α) (t : Finset ι) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i ∈ t, s i)] g ↔ ∀ i ∈ t, f =ᵐ[μ.restrict (s i)] g :=
  ae_eq_restrict_biUnion_iff s t.countable_toSet f g

open scoped Interval in
/-
**MeasureTheory.ae_restrict_uIoc_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_uIoc_eq [LinearOrder α] (a b : α) : ae (μ.restrict (Ι a b)) = 
ae (μ.restrict (Ioc a b)) ⊔ ae (μ.restrict (Ioc b a))
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用引理 `Set.uIoc_eq_union`：uIoc_eq_union : Ι a b = Ioc a b union Ioc b a
· 使用定理 `MeasureTheory.ae_restrict_union_eq`：ae_restrict_union_eq (s t : Set α) :
 ae (μ.restrict (s union t)) = ae (μ.restrict s) ⊔ ae (μ.restrict t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ae_restrict_uIoc_eq [LinearOrder α] (a b : α) :
    ae (μ.restrict (Ι a b)) = ae (μ.restrict (Ioc a b)) ⊔ ae (μ.restrict (Ioc b a)) := by
  simp only [uIoc_eq_union, ae_restrict_union_eq]

open scoped Interval in
/-- See also `MeasureTheory.ae_uIoc_iff`. -/
/-
**MeasureTheory.ae_restrict_uIoc_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_uIoc_iff [LinearOrder α] {a b : α} {P : α -> Prop} : (forallᵐ 
x ∂μ.restrict (Ι a b), P x) ↔ (forallᵐ x ∂μ.restrict (Ioc a b), P x) ∧ forallᵐ x
 ∂μ.restrict (Ioc b a), P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_uIoc_eq`：ae_restrict_uIoc_eq [LinearOrder α] (
a b : α) : ae (μ.restrict (Ι a b)) = ae (μ.restrict (Ioc a b)) ⊔ ae (μ.restrict 
(Ioc b a))
· 使用定理 `Filter.eventually_sup`：eventually_sup {p : α -> Prop} {f g : Filter α} :
 (forallᶠ x in f ⊔ g, p x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See also `MeasureTheory.ae_uIoc_iff`.
-/
theorem ae_restrict_uIoc_iff [LinearOrder α] {a b : α} {P : α → Prop} :
    (∀ᵐ x ∂μ.restrict (Ι a b), P x) ↔
      (∀ᵐ x ∂μ.restrict (Ioc a b), P x) ∧ ∀ᵐ x ∂μ.restrict (Ioc b a), P x := by
  rw [ae_restrict_uIoc_eq, eventually_sup]
/-
**MeasureTheory.ae_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_iff {p : α -> Prop} (hp : MeasurableSet { x | p x }) : (forall
ᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -> p x
参数：hp : MeasurableSet { x | p x }。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_restrict_iff₀`：ae_restrict_iff₀ {p : α -> Prop} (hp : N
ullMeasurableSet { x | p x } (μ.restrict s)) : (forallᵐ x ∂μ.restrict s, p x) ↔ 
forallᵐ x ∂μ, x in s…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem ae_restrict_iff₀ {p : α → Prop} (hp : NullMeasurableSet { x | p x } (μ.restrict s)) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x := by
  simp only [ae_iff, ← compl_ofPred, Measure.restrict_apply₀ hp.compl]
  rw [iff_iff_eq]; congr with x; simp [and_comm]
/-
**MeasureTheory.ae_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_iff {p : α -> Prop} (hp : MeasurableSet { x | p x }) : (forall
ᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -> p x
参数：hp : MeasurableSet { x | p x }。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_restrict_iff₀`：ae_restrict_iff₀ {p : α -> Prop} (hp : N
ullMeasurableSet { x | p x } (μ.restrict s)) : (forallᵐ x ∂μ.restrict s, p x) ↔ 
forallᵐ x ∂μ, x in s…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem ae_restrict_iff {p : α → Prop} (hp : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x :=
  ae_restrict_iff₀ hp.nullMeasurableSet
/-
**MeasureTheory.ae_imp_of_ae_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_imp_of_ae_restrict {s : Set α} {p : α -> Prop} (h : forallᵐ x ∂μ.restri
ct s, p x) : forallᵐ x ∂μ, x in s -> p x
参数：h : forallᵐ x ∂μ.restrict s, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.Measure.measure_inter_eq_zero_of_restrict`：measure_inter_e
q_zero_of_restrict (h : μ.restrict s t = 0) : μ (t inter s) = 0
-/
theorem ae_imp_of_ae_restrict {s : Set α} {p : α → Prop} (h : ∀ᵐ x ∂μ.restrict s, p x) :
    ∀ᵐ x ∂μ, x ∈ s → p x := by
  simp only [ae_iff] at h ⊢
  simpa [ofPred_and, inter_comm] using measure_inter_eq_zero_of_restrict h
/-
**MeasureTheory.ae_restrict_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_iff'₀ {p : α -> Prop} (hs : NullMeasurableSet s μ) : (forallᵐ 
x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -> p x
参数：hs : NullMeasurableSet s μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_restrict_iff'₀`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α} {p : α → Prop},   MeasureTheory.Nul
lMeasurableSet s μ → …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem ae_restrict_iff'₀ {p : α → Prop} (hs : NullMeasurableSet s μ) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x := by
  simp only [ae_iff, ← compl_ofPred, restrict_apply₀' hs]
  rw [iff_iff_eq]; congr with x; simp [and_comm]
/-
**MeasureTheory.ae_restrict_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_iff'₀ {p : α -> Prop} (hs : NullMeasurableSet s μ) : (forallᵐ 
x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -> p x
参数：hs : NullMeasurableSet s μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_restrict_iff'₀`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α} {p : α → Prop},   MeasureTheory.Nul
lMeasurableSet s μ → …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem ae_restrict_iff' {p : α → Prop} (hs : MeasurableSet s) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x :=
  ae_restrict_iff'₀ hs.nullMeasurableSet
/-
**MeasureTheory._root_.Filter.EventuallyEq.restrict** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.restrict {f g : α → δ} {s : Set α} (hfg : f =ᵐ[μ] g) :
    f =ᵐ[μ.restrict s] g := by
  -- note that we cannot use `ae_restrict_iff` since we do not require measurability
  refine hfg.filter_mono ?_
  rw [Measure.ae_le_iff_absolutelyContinuous]
  exact absolutelyContinuous_restrict
/-
**MeasureTheory.ae_restrict_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_mem (hs : MeasurableSet s) : forallᵐ x ∂μ.restrict s, x in s
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_restrict_mem₀`：ae_restrict_mem₀ (hs : NullMeasurableSet
 s μ) : forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem ae_restrict_mem₀ (hs : NullMeasurableSet s μ) : ∀ᵐ x ∂μ.restrict s, x ∈ s :=
  (ae_restrict_iff'₀ hs).2 (Filter.Eventually.of_forall fun _ => id)
/-
**MeasureTheory.ae_restrict_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_mem (hs : MeasurableSet s) : forallᵐ x ∂μ.restrict s, x in s
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_restrict_mem₀`：ae_restrict_mem₀ (hs : NullMeasurableSet
 s μ) : forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem ae_restrict_mem (hs : MeasurableSet s) : ∀ᵐ x ∂μ.restrict s, x ∈ s :=
  ae_restrict_mem₀ hs.nullMeasurableSet
/-
**MeasureTheory.ae_restrict_of_forall_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：ae_restrict_of_forall_mem {μ : Measure α} {s : Set α} (hs : MeasurableSet 
s) {p : α -> Prop} (h : forall x in s, p x) : forallᵐ (x : α) ∂μ.restrict s, p x
参数：hs : MeasurableSet s；h : forall x in s, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
-/
theorem ae_restrict_of_forall_mem {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {p : α → Prop} (h : ∀ x ∈ s, p x) : ∀ᵐ (x : α) ∂μ.restrict s, p x :=
  (ae_restrict_mem hs).mono h
/-
**MeasureTheory._root_.Set.EqOn.aeEq_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.EqOn.aeEq_restrict {α β : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α → β} (h : s.EqOn f g) (hs : MeasurableSet s) : f =ᵐ[μ.restrict s] g :=
  ae_restrict_of_forall_mem hs h
/-
**MeasureTheory.ae_restrict_of_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_of_ae {s : Set α} {p : α -> Prop} (h : forallᵐ x ∂μ, p x) : fo
rallᵐ x ∂μ.restrict s, p x
参数：h : forallᵐ x ∂μ, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
theorem ae_restrict_of_ae {s : Set α} {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ x ∂μ.restrict s, p x :=
  h.filter_mono (ae_mono Measure.restrict_le_self)
/-
**MeasureTheory.ae_restrict_of_ae_restrict_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：ae_restrict_of_ae_restrict_of_subset {s t : Set α} {p : α -> Prop} (hst : 
s subseteq t) (h : forallᵐ x ∂μ.restrict t, p x) : forallᵐ x ∂μ.restrict s, p x
参数：hst : s subseteq t；h : forallᵐ x ∂μ.restrict t, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem ae_restrict_of_ae_restrict_of_subset {s t : Set α} {p : α → Prop} (hst : s ⊆ t)
    (h : ∀ᵐ x ∂μ.restrict t, p x) : ∀ᵐ x ∂μ.restrict s, p x :=
  h.filter_mono (ae_mono <| Measure.restrict_mono hst (le_refl μ))
/-
**MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：ae_of_ae_restrict_of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : f
orallᵐ x ∂μ.restrict t, p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x) : forallᵐ x ∂
μ, p x
参数：t : Set α；ht : forallᵐ x ∂μ.restrict t, p x；htc : forallᵐ x ∂μ.restrict tᶜ, p
 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_le_inter_add_sdiff`：measure_le_inter_add_sdiff (μ 
: F) (s t : Set α) : μ s <= μ (s inter t) + μ (s \ t)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.Measure.le_restrict_apply`：le_restrict_apply (s t : Set α)
 : μ (t inter s) <= μ.restrict s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem ae_of_ae_restrict_of_ae_restrict_compl (t : Set α) {p : α → Prop}
    (ht : ∀ᵐ x ∂μ.restrict t, p x) (htc : ∀ᵐ x ∂μ.restrict tᶜ, p x) : ∀ᵐ x ∂μ, p x :=
  nonpos_iff_eq_zero.1 <|
    calc
      μ { x | ¬p x } ≤ μ ({ x | ¬p x } ∩ t) + μ ({ x | ¬p x } ∩ tᶜ) :=
        measure_le_inter_add_sdiff _ _ _
      _ ≤ μ.restrict t { x | ¬p x } + μ.restrict tᶜ { x | ¬p x } :=
        add_le_add (le_restrict_apply _ _) (le_restrict_apply _ _)
      _ = 0 := by rw [ae_iff.1 ht, ae_iff.1 htc, zero_add]
/-
**MeasureTheory.mem_map_restrict_ae_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：mem_map_restrict_ae_iff {β} {s : Set α} {t : Set β} {f : α -> β} (hs : Mea
surableSet s) : t in Filter.map f (ae (μ.restrict s)) ↔ μ ((f ⁻¹' t)ᶜ inter s) =
 0
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map_restrict_ae_iff {β} {s : Set α} {t : Set β} {f : α → β} (hs : MeasurableSet s) :
    t ∈ Filter.map f (ae (μ.restrict s)) ↔ μ ((f ⁻¹' t)ᶜ ∩ s) = 0 := by
  rw [mem_map, mem_ae_iff, Measure.restrict_apply' hs]
/-
**MeasureTheory.ae_add_measure_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {p
 : α → Prop} {ν : MeasureTheory.Measure α},   (∀ᵐ (x : α) ∂μ + ν, p x) ↔ (∀ᵐ (x 
: α) ∂μ, p x) ∧ ∀ᵐ (x : α) ∂ν, p x
参数：∀ᵐ (x : α) ∂μ + ν, p x；∀ᵐ (x : α) ∂μ, p x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
@[simp] theorem ae_add_measure_iff {p : α → Prop} {ν} :
    (∀ᵐ x ∂μ + ν, p x) ↔ (∀ᵐ x ∂μ, p x) ∧ ∀ᵐ x ∂ν, p x :=
  add_eq_zero

/-- See also `Measure.ae_sum_iff`. -/
/-
**MeasureTheory.ae_finsetSum_measure_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_6} {m0 : MeasurableSpace α} {p : α → Prop} {s
 : Finset ι}   {μ : ι → MeasureTheory.Measure α}, (∀ᵐ (x : α) ∂∑ i ∈ s, μ i, p x
) ↔ ∀ i ∈ s, ∀ᵐ (x : α) ∂μ i, p x
参数：∀ᵐ (x : α) ∂∑ i ∈ s, μ i, p x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …

--- 原说明 ---
See also `Measure.ae_sum_iff`.
-/
@[simp] lemma ae_finsetSum_measure_iff {p : α → Prop} {s : Finset ι} {μ : ι → Measure α} :
    (∀ᵐ x ∂∑ i ∈ s, μ i, p x) ↔ ∀ i ∈ s, ∀ᵐ x ∂μ i, p x := by
  induction s using Finset.cons_induction <;> simp [*]
/-
**MeasureTheory.ae_eq_comp'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_comp' {ν : Measure β} {f : α -> β} {g g' : β -> δ} (hf : AEMeasurabl
e f μ) (h : g =ᵐ[ν] g') (h2 : μ.map f ≪ ν) : g ∘ f =ᵐ[μ] g' ∘ f
参数：hf : AEMeasurable f μ；h : g =ᵐ[ν] g'；h2 : μ.map f ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `MeasureTheory.Measure.tendsto_ae_map`：tendsto_ae_map {f : α -> β} (hf : 
AEMeasurable f μ) : Tendsto f (ae μ) (ae (μ.map f))
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
-/
theorem ae_eq_comp' {ν : Measure β} {f : α → β} {g g' : β → δ} (hf : AEMeasurable f μ)
    (h : g =ᵐ[ν] g') (h2 : μ.map f ≪ ν) : g ∘ f =ᵐ[μ] g' ∘ f :=
  (tendsto_ae_map hf).mono_right h2.ae_le h
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq_comp** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {δ : Type u_4} {m0 : MeasurableSpace α} [i
nst : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Meas
ure β} {f : α → β} {g g' : β → δ},   MeasureTheory.Measure.QuasiMeasurePreservin
g f μ ν → g =ᵐ[ν] g' → g ∘ f =ᵐ[μ] g' ∘ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_comp'`：ae_eq_comp' {ν : Measure β} {f : α -> β} {g g
' : β -> δ} (hf : AEMeasurable f μ) (h : g =ᵐ[ν] g') (h2 : μ.map f ≪ ν) : g ∘ f 
=ᵐ[μ] g' ∘ f
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : Measu
reTheory.Measure α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
-/
theorem Measure.QuasiMeasurePreserving.ae_eq_comp {ν : Measure β} {f : α → β} {g g' : β → δ}
    (hf : QuasiMeasurePreserving f μ ν) (h : g =ᵐ[ν] g') : g ∘ f =ᵐ[μ] g' ∘ f :=
  ae_eq_comp' hf.aemeasurable h hf.absolutelyContinuous
/-
**MeasureTheory.ae_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_comp {f : α -> β} {g g' : β -> δ} (hf : AEMeasurable f μ) (h : g =ᵐ[
μ.map f] g') : g ∘ f =ᵐ[μ] g' ∘ f
参数：hf : AEMeasurable f μ；h : g =ᵐ[μ.map f] g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_comp'`：ae_eq_comp' {ν : Measure β} {f : α -> β} {g g
' : β -> δ} (hf : AEMeasurable f μ) (h : g =ᵐ[ν] g') (h2 : μ.map f ≪ ν) : g ∘ f 
=ᵐ[μ] g' ∘ f
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
theorem ae_eq_comp {f : α → β} {g g' : β → δ} (hf : AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') :
    g ∘ f =ᵐ[μ] g' ∘ f :=
  ae_eq_comp' hf h AbsolutelyContinuous.rfl

@[to_additive]
/-
**MeasureTheory.div_ae_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：div_ae_eq_one {β} [Group β] (f g : α -> β) : f / g =ᵐ[μ] 1 ↔ f =ᵐ[μ] g
参数：f g : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_one`：div_eq_one : a / b = 1 ↔ a = b
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
-/
theorem div_ae_eq_one {β} [Group β] (f g : α → β) : f / g =ᵐ[μ] 1 ↔ f =ᵐ[μ] g := by
  refine ⟨fun h ↦ h.mono fun x hx ↦ ?_, fun h ↦ h.mono fun x hx ↦ ?_⟩
  · rwa [Pi.div_apply, Pi.one_apply, div_eq_one] at hx
  · rwa [Pi.div_apply, Pi.one_apply, div_eq_one]

@[to_additive sub_nonneg_ae]
/-
**MeasureTheory.one_le_div_ae** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：one_le_div_ae {β : Type*} [Group β] [LE β] [MulRightMono β] (f g : α -> β)
 : 1 <=ᵐ[μ] g / f ↔ f <=ᵐ[μ] g
参数：f g : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_le_div'`：one_le_div' : 1 <= a / b ↔ b <= a
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
-/
lemma one_le_div_ae {β : Type*} [Group β] [LE β] [MulRightMono β] (f g : α → β) :
    1 ≤ᵐ[μ] g / f ↔ f ≤ᵐ[μ] g := by
  refine ⟨fun h ↦ h.mono fun a ha ↦ ?_, fun h ↦ h.mono fun a ha ↦ ?_⟩
  · rwa [Pi.one_apply, Pi.div_apply, one_le_div'] at ha
  · rwa [Pi.one_apply, Pi.div_apply, one_le_div']
/-
**MeasureTheory.le_ae_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：le_ae_restrict : ae μ ⊓ 𝓟 s <= ae (μ.restrict s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x
-/
theorem le_ae_restrict : ae μ ⊓ 𝓟 s ≤ ae (μ.restrict s) := fun _s hs =>
  eventually_inf_principal.2 (ae_imp_of_ae_restrict hs)

@[simp]
/-
**MeasureTheory.ae_restrict_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_eq (hs : MeasurableSet s) : ae (μ.restrict s) = ae μ ⊓ 𝓟 s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply_eq_zero'`：restrict_apply_eq_zero' (
hs : MeasurableSet s) : μ.restrict s t = 0 ↔ μ (t inter s) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ae_restrict_eq (hs : MeasurableSet s) : ae (μ.restrict s) = ae μ ⊓ 𝓟 s := by
  ext t
  simp only [mem_inf_principal, mem_ae_iff, restrict_apply_eq_zero' hs, compl_ofPred,
    Classical.not_imp, fun a => and_comm (a := a ∈ s) (b := a ∉ t)]
  rfl
/-
**MeasureTheory.ae_restrict_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_le : ae (μ.restrict s) <= ae μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
lemma ae_restrict_le : ae (μ.restrict s) ≤ ae μ :=
  ae_mono restrict_le_self
/-
**MeasureTheory.ae_restrict_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_eq_bot {s} : ae (μ.restrict s) = ⊥ ↔ μ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_bot`：ae_eq_bot : ae μ = ⊥ ↔ μ = 0
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
-/
theorem ae_restrict_eq_bot {s} : ae (μ.restrict s) = ⊥ ↔ μ s = 0 :=
  ae_eq_bot.trans restrict_eq_zero
/-
**MeasureTheory.ae_restrict_neBot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_neBot {s} : (ae <| μ.restrict s).NeBot ↔ μ s != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.ae_restrict_eq_bot`：ae_restrict_eq_bot {s} : ae (μ.restric
t s) = ⊥ ↔ μ s = 0
-/
theorem ae_restrict_neBot {s} : (ae <| μ.restrict s).NeBot ↔ μ s ≠ 0 :=
  neBot_iff.trans ae_restrict_eq_bot.not
/-
**MeasureTheory.self_mem_ae_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：self_mem_ae_restrict {s} (hs : MeasurableSet s) : s in ae (μ.restrict s)
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_eq`：ae_restrict_eq (hs : MeasurableSet s) : ae
 (μ.restrict s) = ae μ ⊓ 𝓟 s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem self_mem_ae_restrict {s} (hs : MeasurableSet s) : s ∈ ae (μ.restrict s) := by
  simp only [ae_restrict_eq hs, mem_principal, mem_inf_iff]
  exact ⟨_, univ_mem, s, Subset.rfl, (univ_inter s).symm⟩

/-- If two measurable sets are `ae_eq` then any proposition that is almost everywhere true on one
is almost everywhere true on the other -/
/-
**MeasureTheory.ae_restrict_of_ae_eq_of_ae_restrict** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：ae_restrict_of_ae_eq_of_ae_restrict {s t} (hst : s =ᵐ[μ] t) {p : α -> Prop
} : (forallᵐ x ∂μ.restrict s, p x) -> forallᵐ x ∂μ.restrict t, p x
参数：hst : s =ᵐ[μ] t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t

--- 原说明 ---
If two measurable sets are `ae_eq` then any proposition that is almost everywher
e true on one
is almost everywhere true on the other
-/
theorem ae_restrict_of_ae_eq_of_ae_restrict {s t} (hst : s =ᵐ[μ] t) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) → ∀ᵐ x ∂μ.restrict t, p x := by simp [Measure.restrict_congr_set hst]

/-- If two measurable sets are `ae_eq` then any proposition that is almost everywhere true on one
is almost everywhere true on the other -/
/-
**MeasureTheory.ae_restrict_congr_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_restrict_congr_set {s t} (hst : s =ᵐ[μ] t) {p : α -> Prop} : (forallᵐ x
 ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ.restrict t, p x
参数：hst : s =ᵐ[μ] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_of_ae_eq_of_ae_restrict`：ae_restrict_of_ae_eq_
of_ae_restrict {s t} (hst : s =ᵐ[μ] t) {p : α -> Prop} : (forallᵐ x ∂μ.restrict 
s, p x) -> forallᵐ x ∂μ.restrict t, p x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If two measurable sets are `ae_eq` then any proposition that is almost everywher
e true on one
is almost everywhere true on the other
-/
theorem ae_restrict_congr_set {s t} (hst : s =ᵐ[μ] t) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ.restrict t, p x :=
  ⟨ae_restrict_of_ae_eq_of_ae_restrict hst, ae_restrict_of_ae_eq_of_ae_restrict hst.symm⟩
/-
**MeasureTheory.NullMeasurable.measure_preimage_eq_measure_restrict_preimage_of_
ae_compl_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.NullMeasurable`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β
 : Type u_7} [inst : MeasurableSpace β]   {b : β} {f : α → β} {s : Set α},   Mea
sureTheory.NullMeasurable f (μ.restrict s) →     (f =ᵐ[μ.restrict sᶜ] fun x => b
) → ∀ {t : Set β}, MeasurableSet t → b ∉ t → μ (f ⁻¹' t) = (μ.restrict s) (f ⁻¹'
 t)
参数：μ.restrict s；f =ᵐ[μ.restrict sᶜ] fun x => b；f ⁻¹' t；μ.restrict s；f ⁻¹' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply₀`：restrict_apply₀ (ht : NullMeasura
bleSet t (μ.restrict s)) : μ.restrict s t = μ (t inter s)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.NullMeasurableSet.of_null`：of_null (h : μ s = 0) : NullMea
surableSet s μ
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma NullMeasurable.measure_preimage_eq_measure_restrict_preimage_of_ae_compl_eq_const
    {β : Type*} [MeasurableSpace β] {b : β} {f : α → β} {s : Set α}
    (f_mble : NullMeasurable f (μ.restrict s)) (hs : f =ᵐ[Measure.restrict μ sᶜ] (fun _ ↦ b))
    {t : Set β} (t_mble : MeasurableSet t) (ht : b ∉ t) :
    μ (f ⁻¹' t) = μ.restrict s (f ⁻¹' t) := by
  rw [Measure.restrict_apply₀ (f_mble t_mble)]
  rw [EventuallyEq, ae_iff, Measure.restrict_apply₀] at hs
  · apply le_antisymm _ (measure_mono inter_subset_left)
    apply (measure_mono (Eq.symm (inter_union_compl (f ⁻¹' t) s)).le).trans
    apply (measure_union_le _ _).trans
    suffices μ ((f ⁻¹' t) ∩ sᶜ) = 0 by simp [this]
    rw [← nonpos_iff_eq_zero, ← hs]
    gcongr
    exact fun x hx hfx ↦ ht (hfx ▸ hx)
  · exact NullMeasurableSet.of_null hs
/-
**MeasureTheory.nullMeasurableSet_restrict** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：nullMeasurableSet_restrict (hs : NullMeasurableSet s μ) {t : Set α} : Null
MeasurableSet t (μ.restrict s) ↔ NullMeasurableSet (t inter s) μ
参数：hs : NullMeasurableSet s μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.NullMeasurableSet.exists_measurable_superset_ae_eq`：exists
_measurable_superset_ae_eq (h : NullMeasurableSet s μ) : exists t ⊇ s, Measurabl
eSet t ∧ t =ᵐ[μ] s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_restrict_iff'₀`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α} {p : α → Prop},   MeasureTheory.Nul
lMeasurableSet s μ → …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `MeasureTheory.NullMeasurableSet.congr`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → s =ᵐ[μ] t → M…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.NullMeasurableSet.of_null`：of_null (h : μ s = 0) : NullMea
surableSet s μ
· 使用定理 `MeasureTheory.Measure.restrict_apply₀'`：restrict_apply₀' (hs : NullMeasu
rableSet s μ) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sdiff_inter_self`：sdiff_inter_self {a b : Set α} : b \ a inter a = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.NullMeasurableSet.mono_ac`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullMeas
urableSet s μ → ν.AbsolutelyC…
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_restrict`：absolutelyContinuou
s_restrict : μ.restrict s ≪ μ
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
· 使用定理 `MeasureTheory.NullMeasurableSet.union`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
-/
lemma nullMeasurableSet_restrict (hs : NullMeasurableSet s μ) {t : Set α} :
    NullMeasurableSet t (μ.restrict s) ↔ NullMeasurableSet (t ∩ s) μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨t', -, ht', t't⟩ : ∃ t' ⊇ t, MeasurableSet t' ∧ t' =ᵐ[μ.restrict s] t :=
      h.exists_measurable_superset_ae_eq
    have A : (t' ∩ s : Set α) =ᵐ[μ] (t ∩ s : Set α) := by
      have : ∀ᵐ x ∂μ, x ∈ s → (x ∈ t') = (x ∈ t) :=
        (ae_restrict_iff'₀ hs).1 t't
      filter_upwards [this] with y hy
      change (y ∈ t' ∩ s) = (y ∈ t ∩ s)
      simpa only [eq_iff_iff, mem_inter_iff, and_congr_left_iff] using hy
    obtain ⟨s', -, hs', s's⟩ : ∃ s' ⊇ s, MeasurableSet s' ∧ s' =ᵐ[μ] s :=
      hs.exists_measurable_superset_ae_eq
    have B : (t' ∩ s' : Set α) =ᵐ[μ] (t' ∩ s : Set α) :=
      ae_eq_set_inter (EventuallyEq.refl _ _) s's
    exact (ht'.inter hs').nullMeasurableSet.congr (B.trans A)
  · have A : NullMeasurableSet (t \ s) (μ.restrict s) := by
      apply NullMeasurableSet.of_null
      rw [Measure.restrict_apply₀' hs]
      simp
    have B : NullMeasurableSet (t ∩ s) (μ.restrict s) :=
      h.mono_ac absolutelyContinuous_restrict
    simpa using A.union B
/-
**MeasureTheory.nullMeasurableSet_restrict_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory`。
形式化陈述：nullMeasurableSet_restrict_of_subset {t : Set α} (ht : t subseteq s) : Nul
lMeasurableSet t (μ.restrict s) ↔ NullMeasurableSet t μ
参数：ht : t subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.NullMeasurableSet.exists_measurable_subset_ae_eq`：exists_m
easurable_subset_ae_eq (h : NullMeasurableSet s μ) : exists t subseteq s, Measur
ableSet t ∧ t =ᵐ[μ] s
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
· 使用定理 `MeasureTheory.NullMeasurableSet.congr`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → s =ᵐ[μ] t → M…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasureTheory.NullMeasurableSet.mono_ac`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullMeas
urableSet s μ → ν.AbsolutelyC…
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_restrict`：absolutelyContinuou
s_restrict : μ.restrict s ≪ μ
-/
lemma nullMeasurableSet_restrict_of_subset {t : Set α} (ht : t ⊆ s) :
    NullMeasurableSet t (μ.restrict s) ↔ NullMeasurableSet t μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mono_ac absolutelyContinuous_restrict⟩
  obtain ⟨t', t'_subs, ht', t't⟩ : ∃ t' ⊆ t, MeasurableSet t' ∧ t' =ᵐ[μ.restrict s] t :=
    h.exists_measurable_subset_ae_eq
  have : ∀ᵐ x ∂μ, x ∈ s → (x ∈ t' ↔ x ∈ t) := by
    apply ae_imp_of_ae_restrict
    filter_upwards [t't] with x hx using by simpa using! hx
  have : t' =ᵐ[μ] t := by
    filter_upwards [this] with x hx
    change (x ∈ t') = (x ∈ t)
    simp only [eq_iff_iff]
    tauto
  exact ht'.nullMeasurableSet.congr this

namespace Measure

section Subtype

/-! ### Subtype of a measure space -/

section ComapAnyMeasure

/-
**MeasureTheory.Measure.MeasurableSet.nullMeasurableSet_subtype_coe** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.Measure.MeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 : Set α} {t : Set ↑s},   MeasureTheory.NullMeasurableSet s μ → MeasurableSet t 
→ MeasureTheory.NullMeasurableSet (Subtype.val '' t) μ
参数：Subtype.val '' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.generateFrom_induction`：generateFrom_induction (C : Set 
(Set α)) (p : forall s : Set α, MeasurableSet[generateFrom C] s -> Prop) (hC : f
orall t in C, forall ht, p t…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.range_sdiff_image`：range_sdiff_image {f : α -> β} (hf : Injective f)
 (s : Set α) : range f \ f '' s = f '' sᶜ
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `MeasureTheory.NullMeasurableSet.diff`：∀ {α : Type u_2} {m0 : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasura
bleSet s μ → MeasureTheory…
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `MeasureTheory.NullMeasurableSet.iUnion`：∀ {α : Type u_2} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} {ι : Sort u_5} [Countable ι] {s : ι → Se
t α},   (∀ (i : ι), MeasureT…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasurableSpace.comap_eq_generateFrom`：comap_eq_generateFrom (m : Measur
ableSpace β) (f : α -> β) : m.comap f = generateFrom { t | exists s, MeasurableS
et s ∧ f ⁻¹' s = t }
· 使用定理 `Subtype.instMeasurableSpace.eq_1`：∀ {α : Type u_6} {p : α → Prop} [m : M
easurableSpace α],   Subtype.instMeasurableSpace = MeasurableSpace.comap Subtype
.val m
-/
theorem MeasurableSet.nullMeasurableSet_subtype_coe {t : Set s} (hs : NullMeasurableSet s μ)
    (ht : MeasurableSet t) : NullMeasurableSet ((↑) '' t) μ := by
  rw [Subtype.instMeasurableSpace, comap_eq_generateFrom] at ht
  induction t, ht using generateFrom_induction with
  | hC t' ht' =>
    obtain ⟨s', hs', rfl⟩ := ht'
    rw [Subtype.image_preimage_coe]
    exact hs.inter (hs'.nullMeasurableSet)
  | empty => simp only [image_empty, nullMeasurableSet_empty]
  | compl t' _ ht' =>
    simp only [← range_sdiff_image Subtype.coe_injective, Subtype.range_coe_subtype, ofPred_mem_eq]
    exact hs.diff ht'
  | iUnion f _ hf =>
    rw [image_iUnion]
    exact .iUnion hf
/-
**MeasureTheory.Measure.NullMeasurableSet.subtype_coe** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure.NullMeasurableSet`。
形式化陈述：∀ {α : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s
 : Set α} {t : Set ↑s},   MeasureTheory.NullMeasurableSet s μ →     MeasureTheor
y.NullMeasurableSet t (MeasureTheory.Measure.comap Subtype.val μ) →       Measur
eTheory.NullMeasurableSet (Subtype.val '' t) μ
参数：MeasureTheory.Measure.comap Subtype.val μ；Subtype.val '' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.NullMeasurableSet.image`：∀ {α : Type u_1} {β : Typ
e u_2} {s : Set α} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (f : α → β)
   (μ : MeasureTheory.Measure β),  …
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `MeasureTheory.Measure.MeasurableSet.nullMeasurableSet_subtype_coe`：∀ {α 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} {
t : Set ↑s},   MeasureTheory.NullMeasurableSet s μ → Me…
-/
theorem NullMeasurableSet.subtype_coe {t : Set s} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t (μ.comap Subtype.val)) : NullMeasurableSet (((↑) : s → α) '' t) μ :=
  NullMeasurableSet.image _ μ Subtype.coe_injective
    (fun _ => MeasurableSet.nullMeasurableSet_subtype_coe hs) ht
/-
**MeasureTheory.Measure.measure_subtype_coe_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：measure_subtype_coe_le_comap (hs : NullMeasurableSet s μ) (t : Set s) : μ 
(((↑) : s -> α) '' t) <= μ.comap Subtype.val t
参数：hs : NullMeasurableSet s μ；t : Set s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.le_comap_apply`：le_comap_apply (f : α -> β) (μ : M
easure β) (hfi : Injective f) (hf : forall s, MeasurableSet s -> NullMeasurableS
et (f '' s) μ) (s : Set α)…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `MeasureTheory.Measure.MeasurableSet.nullMeasurableSet_subtype_coe`：∀ {α 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} {
t : Set ↑s},   MeasureTheory.NullMeasurableSet s μ → Me…
-/
theorem measure_subtype_coe_le_comap (hs : NullMeasurableSet s μ) (t : Set s) :
    μ (((↑) : s → α) '' t) ≤ μ.comap Subtype.val t :=
  le_comap_apply _ _ Subtype.coe_injective (fun _ =>
    MeasurableSet.nullMeasurableSet_subtype_coe hs) _
/-
**MeasureTheory.Measure.measure_subtype_coe_eq_zero_of_comap_eq_zero** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_subtype_coe_eq_zero_of_comap_eq_zero (hs : NullMeasurableSet s μ) 
{t : Set s} (ht : μ.comap Subtype.val t = 0) : μ (((↑) : s -> α) '' t) = 0
参数：hs : NullMeasurableSet s μ；ht : μ.comap Subtype.val t = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.Measure.measure_subtype_coe_le_comap`：measure_subtype_coe_
le_comap (hs : NullMeasurableSet s μ) (t : Set s) : μ (((↑) : s -> α) '' t) <= μ
.comap Subtype.val t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem measure_subtype_coe_eq_zero_of_comap_eq_zero (hs : NullMeasurableSet s μ) {t : Set s}
    (ht : μ.comap Subtype.val t = 0) : μ (((↑) : s → α) '' t) = 0 :=
  eq_bot_iff.mpr <| (measure_subtype_coe_le_comap hs t).trans ht.le

end ComapAnyMeasure

section MeasureSpace

variable {u : Set δ} [MeasureSpace δ] {p : δ → Prop}

/-- In a measure space, one can restrict the measure to a subtype to get a new measure space.
Not registered as an instance, as there are other natural choices such as the normalized restriction
for a probability measure, or the subspace measure when restricting to a vector subspace. Enable
locally if needed with `attribute [local instance] Measure.Subtype.measureSpace`. -/
@[instance_reducible]
/-
**MeasureTheory.Measure.Subtype.measureSpace** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.Measure.Subtype`。
形式化陈述：{δ : Type u_4} → [MeasureTheory.MeasureSpace δ] → {p : δ → Prop} → Measure
Theory.MeasureSpace (Subtype p)
参数：Subtype p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a measure space, one can restrict the measure to a subtype to get a new measu
re space.
Not registered as an instance, as there are other natural choices such as the no
rmalized restriction
for a probability measure, or the subspace measure when restricting to a vector 
subspace. Enable
locally if needed with `attribute [local instance] Measure.Subtype.measureSpace`
.
-/
noncomputable def Subtype.measureSpace : MeasureSpace (Subtype p) where
  volume := Measure.comap Subtype.val volume

attribute [local instance] Subtype.measureSpace
/-
**MeasureTheory.Measure.Subtype.volume_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure.Subtype`。
形式化陈述：∀ {δ : Type u_4} {u : Set δ} [inst : MeasureTheory.MeasureSpace δ],   Meas
ureTheory.volume = MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subtype.volume_def : (volume : Measure u) = volume.comap Subtype.val :=
  rfl
/-
**MeasureTheory.Measure.Subtype.volume_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.Subtype`。
形式化陈述：∀ {δ : Type u_4} {u : Set δ} [inst : MeasureTheory.MeasureSpace δ],   Meas
ureTheory.NullMeasurableSet u MeasureTheory.volume → MeasureTheory.volume Set.un
iv = MeasureTheory.volume u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.Subtype.volume_def`：∀ {δ : Type u_4} {u : Set δ} [
inst : MeasureTheory.MeasureSpace δ],   MeasureTheory.volume = MeasureTheory.Mea
sure.comap Subtype.val Measure…
· 使用定理 `MeasureTheory.Measure.comap_apply₀`：comap_apply₀ (f : α -> β) (μ : Measu
re β) (hfi : Injective f) (hf : forall s, MeasurableSet s -> NullMeasurableSet (
f '' s) μ) (hs : NullMea…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `MeasureTheory.Measure.MeasurableSet.nullMeasurableSet_subtype_coe`：∀ {α 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} {
t : Set ↑s},   MeasureTheory.NullMeasurableSet s μ → Me…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Subtype.volume_univ (hu : NullMeasurableSet u) : volume (univ : Set u) = volume u := by
  rw [Subtype.volume_def, comap_apply₀ _ _ _ _ MeasurableSet.univ.nullMeasurableSet]
  · simp only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq]
  · exact Subtype.coe_injective
  · exact fun t => MeasurableSet.nullMeasurableSet_subtype_coe hu
/-
**MeasureTheory.Measure.volume_subtype_coe_le_volume** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：volume_subtype_coe_le_volume (hu : NullMeasurableSet u) (t : Set u) : volu
me (((↑) : u -> δ) '' t) <= volume t
参数：hu : NullMeasurableSet u；t : Set u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measure_subtype_coe_le_comap`：measure_subtype_coe_
le_comap (hs : NullMeasurableSet s μ) (t : Set s) : μ (((↑) : s -> α) '' t) <= μ
.comap Subtype.val t
-/
theorem volume_subtype_coe_le_volume (hu : NullMeasurableSet u) (t : Set u) :
    volume (((↑) : u → δ) '' t) ≤ volume t :=
  measure_subtype_coe_le_comap hu t
/-
**MeasureTheory.Measure.volume_subtype_coe_eq_zero_of_volume_eq_zero** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：volume_subtype_coe_eq_zero_of_volume_eq_zero (hu : NullMeasurableSet u) {t
 : Set u} (ht : volume t = 0) : volume (((↑) : u -> δ) '' t) = 0
参数：hu : NullMeasurableSet u；ht : volume t = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measure_subtype_coe_eq_zero_of_comap_eq_zero`：meas
ure_subtype_coe_eq_zero_of_comap_eq_zero (hs : NullMeasurableSet s μ) {t : Set s
} (ht : μ.comap Subtype.val t = 0) : μ (((↑) : s -> α) '…
-/
theorem volume_subtype_coe_eq_zero_of_volume_eq_zero (hu : NullMeasurableSet u) {t : Set u}
    (ht : volume t = 0) : volume (((↑) : u → δ) '' t) = 0 :=
  measure_subtype_coe_eq_zero_of_comap_eq_zero hu ht

end MeasureSpace

end Subtype

end Measure

end MeasureTheory

open MeasureTheory Measure

namespace MeasurableEmbedding

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α → β}

section
variable (hf : MeasurableEmbedding f)
include hf

/-
**MeasurableEmbedding.map_comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbedding`。
形式化陈述：map_comap (μ : Measure β) : (comap f μ).map f = μ.restrict (range f)
参数：μ : Measure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
-/
theorem map_comap (μ : Measure β) : (comap f μ).map f = μ.restrict (range f) := by
  ext1 t ht
  rw [hf.map_apply, comap_apply f hf.injective hf.measurableSet_image' _ (hf.measurable ht),
    image_preimage_eq_inter_range, Measure.restrict_apply ht]
/-
**MeasurableEmbedding.comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbedding
`。
形式化陈述：comap_apply (μ : Measure β) (s : Set α) : comap f μ s = μ (f '' s)
参数：μ : Measure β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
· 使用定理 `MeasurableEmbedding.map_comap`：map_comap (μ : Measure β) : (comap f μ).m
ap f = μ.restrict (range f)
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableEmbedding.measurableSet_range`：measurableSet_range (hf : Measu
rableEmbedding f) : MeasurableSet (range f)
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem comap_apply (μ : Measure β) (s : Set α) : comap f μ s = μ (f '' s) :=
  calc
    comap f μ s = comap f μ (f ⁻¹' f '' s) := by rw [hf.injective.preimage_image]
    _ = (comap f μ).map f (f '' s) := (hf.map_apply _ _).symm
    _ = μ (f '' s) := by
      rw [hf.map_comap, restrict_apply' hf.measurableSet_range,
        inter_eq_self_of_subset_left (image_subset_range _ _)]
/-
**MeasurableEmbedding.comap_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbedding`。
形式化陈述：comap_map (μ : Measure α) : (map f μ).comap f = μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
-/
theorem comap_map (μ : Measure α) : (map f μ).comap f = μ := by
  ext t _
  rw [hf.comap_apply, hf.map_apply, preimage_image_eq _ hf.injective]
/-
**MeasurableEmbedding.ae_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbedding`
。
形式化陈述：ae_map_iff {p : β -> Prop} {μ : Measure α} : (forallᵐ x ∂μ.map f, p x) ↔ f
orallᵐ x ∂μ, p (f x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_map_iff {p : β → Prop} {μ : Measure α} : (∀ᵐ x ∂μ.map f, p x) ↔ ∀ᵐ x ∂μ, p (f x) := by
  simp only [ae_iff, hf.map_apply, preimage_ofPred_eq]
/-
**MeasurableEmbedding.restrict_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbeddin
g`。
形式化陈述：restrict_map (μ : Measure α) (s : Set β) : (μ.map f).restrict s = (μ.restr
ict <| f ⁻¹' s).map f
参数：μ : Measure α；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_map (μ : Measure α) (s : Set β) :
    (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  Measure.ext fun t ht => by simp [hf.map_apply, ht, hf.measurable ht]
/-
**MeasurableEmbedding.comap_preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEmbedd
ing`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {m0 : MeasurableSpace α} {m1 : MeasurableS
pace β} {f : α → β},   MeasurableEmbedding f →     ∀ (μ : MeasureTheory.Measure 
β) (s : Set β), (MeasureTheory.Measure.comap f μ) (f ⁻¹' s) = μ (s ∩ Set.range f
)
参数：μ : MeasureTheory.Measure β；s : Set β；MeasureTheory.Measure.comap f μ；f ⁻¹' s
；s ∩ Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.map_apply`：∀ {α : Type u_1} {β : Type u_2} {m0 : Mea
surableSpace α} {m1 : MeasurableSpace β} {f : α → β},   MeasurableEmbedding f → 
∀ (μ : MeasureTheor…
· 使用定理 `MeasurableEmbedding.map_comap`：map_comap (μ : Measure β) : (comap f μ).m
ap f = μ.restrict (range f)
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableEmbedding.measurableSet_range`：measurableSet_range (hf : Measu
rableEmbedding f) : MeasurableSet (range f)
-/
protected theorem comap_preimage (μ : Measure β) (s : Set β) :
    μ.comap f (f ⁻¹' s) = μ (s ∩ range f) := by
  rw [← hf.map_apply, hf.map_comap, restrict_apply' hf.measurableSet_range]
/-
**MeasurableEmbedding.comap_restrict** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEmbedd
ing`。
形式化陈述：comap_restrict (μ : Measure β) (s : Set β) : (μ.restrict s).comap f = (μ.c
omap f).restrict (f ⁻¹' s)
参数：μ : Measure β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
-/
lemma comap_restrict (μ : Measure β) (s : Set β) :
    (μ.restrict s).comap f = (μ.comap f).restrict (f ⁻¹' s) := by
  ext t ht
  rw [Measure.restrict_apply ht, comap_apply hf, comap_apply hf,
    Measure.restrict_apply (hf.measurableSet_image.2 ht), image_inter_preimage]
/-
**MeasurableEmbedding.restrict_comap** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEmbedd
ing`。
形式化陈述：restrict_comap (μ : Measure β) (s : Set α) : (μ.comap f).restrict s = (μ.r
estrict (f '' s)).comap f
参数：μ : Measure β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasurableEmbedding.comap_restrict`：comap_restrict (μ : Measure β) (s : 
Set β) : (μ.restrict s).comap f = (μ.comap f).restrict (f ⁻¹' s)
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
-/
lemma restrict_comap (μ : Measure β) (s : Set α) :
    (μ.comap f).restrict s = (μ.restrict (f '' s)).comap f := by
  rw [comap_restrict hf, preimage_image_eq _ hf.injective]

end

/-
**MeasurableEmbedding._root_.MeasurableEquiv.restrict_map** 是 Mathlib 中的一个定理，位于命
名空间 `MeasurableEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEquiv.restrict_map (e : α ≃ᵐ β) (μ : Measure α) (s : Set β) :
    (μ.map e).restrict s = (μ.restrict <| e ⁻¹' s).map e :=
  e.measurableEmbedding.restrict_map _ _
/-
**MeasurableEmbedding._root_.MeasurableEquiv.comap_apply** 是 Mathlib 中的一个引理，位于命名
空间 `MeasurableEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEquiv.comap_apply (e : α ≃ᵐ β) (μ : Measure β) (s : Set α) :
    comap e μ s = μ (e.symm ⁻¹' s) := by
  rw [e.measurableEmbedding.comap_apply, e.image_eq_preimage_symm]

end MeasurableEmbedding

/-
**MeasureTheory.Measure.map_eq_comap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasureTheory.Measure.map_eq_comap {_ : MeasurableSpace α} {_ : Measurable
Space β} {f : α -> β} {g : β -> α} {μ : Measure α} (hf : Measurable f) (hg : Mea
surableEmbedding g) (hμg : forallᵐ a ∂μ, a in Set.range g) (hfg : forall a, f (g
 a) = a) : μ.map f = μ.comap g
参数：hf : Measurable f；hg : MeasurableEmbedding g；hμg : forallᵐ a ∂μ, a in Set.ran
ge g；hfg : forall a, f (g a) = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_sdiff_null`：measure_sdiff_null (ht : μ t = 0) : μ 
(s \ t) = μ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sdiff_compl`：sdiff_compl : x \ yᶜ = x ⊓ y
-/
lemma MeasureTheory.Measure.map_eq_comap {_ : MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β}
    {g : β → α} {μ : Measure α} (hf : Measurable f) (hg : MeasurableEmbedding g)
    (hμg : ∀ᵐ a ∂μ, a ∈ Set.range g) (hfg : ∀ a, f (g a) = a) : μ.map f = μ.comap g := by
  ext s hs
  rw [map_apply hf hs, hg.comap_apply, ← measure_sdiff_null hμg]
  congr
  simp
  grind

section Subtype

/-
**comap_subtype_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_subtype_coe_apply {_m0 : MeasurableSpace α} {s : Set α} (hs : Measur
ableSet s) (μ : Measure α) (t : Set s) : comap (↑) μ t = μ ((↑) '' t)
参数：hs : MeasurableSet s；μ : Measure α；t : Set s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
-/
theorem comap_subtype_coe_apply {_m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) (t : Set s) : comap (↑) μ t = μ ((↑) '' t) :=
  (MeasurableEmbedding.subtype_coe hs).comap_apply _ _
/-
**map_comap_subtype_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_comap_subtype_coe {m0 : MeasurableSpace α} {s : Set α} (hs : Measurabl
eSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s -> α) = μ.restrict s
参数：hs : MeasurableSet s；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEmbedding.map_comap`：map_comap (μ : Measure β) : (comap f μ).m
ap f = μ.restrict (range f)
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem map_comap_subtype_coe {m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) : (comap (↑) μ).map ((↑) : s → α) = μ.restrict s := by
  rw [(MeasurableEmbedding.subtype_coe hs).map_comap, Subtype.range_coe]
/-
**ae_restrict_iff_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_restrict_iff_subtype {m0 : MeasurableSpace α} {μ : Measure α} {s : Set 
α} (hs : MeasurableSet s) {p : α -> Prop} : (forallᵐ x ∂μ.restrict s, p x) ↔ for
allᵐ (x : s) ∂comap ((↑) : s -> α) μ, p x
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
· 使用定理 `MeasurableEmbedding.ae_map_iff`：ae_map_iff {p : β -> Prop} {μ : Measure 
α} : (forallᵐ x ∂μ.map f, p x) ↔ forallᵐ x ∂μ, p (f x)
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ae_restrict_iff_subtype {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ (x : s) ∂comap ((↑) : s → α) μ, p x := by
  rw [← map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).ae_map_iff]

variable [MeasureSpace α] {s t : Set α}

/-!
### Volume on `s : Set α`

Note the instance is provided earlier as `Subtype.measureSpace`.
-/
attribute [local instance] Subtype.measureSpace

/-
**volume_set_coe_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：volume_set_coe_def (s : Set α) : (volume : Measure s) = comap ((↑) : s -> 
α) volume
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Volume on `s : Set α`

Note the instance is provided earlier as `Subtype.measureSpace`.
-/
theorem volume_set_coe_def (s : Set α) : (volume : Measure s) = comap ((↑) : s → α) volume :=
  rfl
/-
**MeasurableSet.map_coe_volume** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.map_coe_volume {s : Set α} (hs : MeasurableSet s) : volume.m
ap ((↑) : s -> α) = restrict volume s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `volume_set_coe_def`：volume_set_coe_def (s : Set α) : (volume : Measure s
) = comap ((↑) : s -> α) volume
· 使用定理 `MeasurableEmbedding.map_comap`：map_comap (μ : Measure β) : (comap f μ).m
ap f = μ.restrict (range f)
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem MeasurableSet.map_coe_volume {s : Set α} (hs : MeasurableSet s) :
    volume.map ((↑) : s → α) = restrict volume s := by
  rw [volume_set_coe_def, (MeasurableEmbedding.subtype_coe hs).map_comap volume, Subtype.range_coe]
/-
**volume_image_subtype_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：volume_image_subtype_coe {s : Set α} (hs : MeasurableSet s) (t : Set s) : 
volume ((↑) '' t : Set α) = volume t
参数：hs : MeasurableSet s；t : Set s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_subtype_coe_apply`：comap_subtype_coe_apply {_m0 : MeasurableSpace 
α} {s : Set α} (hs : MeasurableSet s) (μ : Measure α) (t : Set s) : comap (↑) μ 
t = μ ((↑) ''…
-/
theorem volume_image_subtype_coe {s : Set α} (hs : MeasurableSet s) (t : Set s) :
    volume ((↑) '' t : Set α) = volume t :=
  (comap_subtype_coe_apply hs volume t).symm

@[simp]
/-
**volume_preimage_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：volume_preimage_coe (hs : NullMeasurableSet s) (ht : MeasurableSet t) : vo
lume (((↑) : s -> α) ⁻¹' t) = volume (t inter s)
参数：hs : NullMeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `volume_set_coe_def`：volume_set_coe_def (s : Set α) : (volume : Measure s
) = comap ((↑) : s -> α) volume
· 使用定理 `MeasureTheory.Measure.comap_apply₀`：comap_apply₀ (f : α -> β) (μ : Measu
re β) (hfi : Injective f) (hf : forall s, MeasurableSet s -> NullMeasurableSet (
f '' s) μ) (hs : NullMea…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `MeasureTheory.Measure.MeasurableSet.nullMeasurableSet_subtype_coe`：∀ {α 
: Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} {
t : Set ↑s},   MeasureTheory.NullMeasurableSet s μ → Me…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem volume_preimage_coe (hs : NullMeasurableSet s) (ht : MeasurableSet t) :
    volume (((↑) : s → α) ⁻¹' t) = volume (t ∩ s) := by
  rw [volume_set_coe_def,
    comap_apply₀ _ _ Subtype.coe_injective
      (fun h => MeasurableSet.nullMeasurableSet_subtype_coe hs)
      (measurable_subtype_coe ht).nullMeasurableSet,
    image_preimage_eq_inter_range, Subtype.range_coe]

end Subtype

section Piecewise

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α} {f g : α → β}

/-
**piecewise_ae_eq_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：piecewise_ae_eq_restrict [DecidablePred (· in s)] (hs : MeasurableSet s) :
 piecewise s f g =ᵐ[μ.restrict s] f
参数：· in s；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_eq`：ae_restrict_eq (hs : MeasurableSet s) : ae
 (μ.restrict s) = ae μ ⊓ 𝓟 s
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Set.EqOn.eventuallyEq`：Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α 
-> β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g
· 使用定理 `Set.piecewise_eqOn`：piecewise_eqOn (f g : α -> β) : EqOn (s.piecewise f 
g) f s
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem piecewise_ae_eq_restrict [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    piecewise s f g =ᵐ[μ.restrict s] f := by
  rw [ae_restrict_eq hs]
  exact (piecewise_eqOn s f g).eventuallyEq.filter_mono inf_le_right
/-
**piecewise_ae_eq_restrict_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：piecewise_ae_eq_restrict_compl [DecidablePred (· in s)] (hs : MeasurableSe
t s) : piecewise s f g =ᵐ[μ.restrict sᶜ] g
参数：· in s；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_eq`：ae_restrict_eq (hs : MeasurableSet s) : ae
 (μ.restrict s) = ae μ ⊓ 𝓟 s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Set.EqOn.eventuallyEq`：Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α 
-> β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g
· 使用定理 `Set.piecewise_eqOn_compl`：piecewise_eqOn_compl (f g : α -> β) : EqOn (s.
piecewise f g) g sᶜ
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem piecewise_ae_eq_restrict_compl [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    piecewise s f g =ᵐ[μ.restrict sᶜ] g := by
  rw [ae_restrict_eq hs.compl]
  exact (piecewise_eqOn_compl s f g).eventuallyEq.filter_mono inf_le_right
/-
**piecewise_ae_eq_of_ae_eq_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：piecewise_ae_eq_of_ae_eq_set [DecidablePred (· in s)] [DecidablePred (· in
 t)] (hst : s =ᵐ[μ] t) : s.piecewise f g =ᵐ[μ] t.piecewise f g
参数：· in s；· in t；hst : s =ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.EventuallyEq.mem_iff`：∀ {α : Type u} {s t : Set α} {l : Filter α}
, s =ᶠ[l] t → ∀ᶠ (x : α) in l, x ∈ s ↔ x ∈ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piecewise_ae_eq_of_ae_eq_set [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (hst : s =ᵐ[μ] t) : s.piecewise f g =ᵐ[μ] t.piecewise f g :=
  hst.mem_iff.mono fun x hx => by simp [piecewise, hx]

end Piecewise

section IndicatorFunction

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α} {f : α → β}

/-
**mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem [Zero β] {t : Set
 β} (ht : (0 : β) in t) (hs : MeasurableSet s) : t in Filter.map (s.indicator f)
 (ae μ) ↔ t in Filter.map f (ae <| μ.restrict s)
参数：ht : (0 : β) in t；hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.indicator_preimage`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] 
(s : Set α) (f : α → M) (B : Set M),   s.indicator f ⁻¹' B = s.ite (f ⁻¹' B) (0 
⁻¹' B)
· 使用定理 `Set.ite.eq_1`：∀ {α : Type u_1} (t s s' : Set α), t.ite s s' = s ∩ t ∪ s'
 \ t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_const`：preimage_const (b : β) (s : Set β) [Decidable (b in 
s)] : (fun _ : α => b) ⁻¹' s = if b in s then univ else ∅
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem [Zero β] {t : Set β}
    (ht : (0 : β) ∈ t) (hs : MeasurableSet s) :
    t ∈ Filter.map (s.indicator f) (ae μ) ↔ t ∈ Filter.map f (ae <| μ.restrict s) := by
  classical
  simp_rw [mem_map, mem_ae_iff]
  rw [Measure.restrict_apply' hs, Set.indicator_preimage, Set.ite]
  simp_rw [Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ ∪ sᶜ) ∩ ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ ∩ s) = 0
  simp only [ht, ← Set.compl_eq_univ_sdiff, compl_compl, if_true,
    Set.preimage_const]
  simp_rw [Set.union_inter_distrib_right, Set.compl_inter_self s, Set.union_empty]
/-
**mem_map_indicator_ae_iff_of_zero_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_map_indicator_ae_iff_of_zero_notMem [Zero β] {t : Set β} (ht : (0 : β)
 ∉ t) : t in Filter.map (s.indicator f) (ae μ) ↔ μ ((f ⁻¹' t)ᶜ union sᶜ) = 0
参数：ht : (0 : β) ∉ t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `Set.indicator_preimage`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] 
(s : Set α) (f : α → M) (B : Set M),   s.indicator f ⁻¹' B = s.ite (f ⁻¹' B) (0 
⁻¹' B)
· 使用定理 `Set.ite.eq_1`：∀ {α : Type u_1} (t s s' : Set α), t.ite s s' = s ∩ t ∪ s'
 \ t
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.preimage_const`：preimage_const (b : β) (s : Set β) [Decidable (b in 
s)] : (fun _ : α => b) ⁻¹' s = if b in s then univ else ∅
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `Set.empty_sdiff`：empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_map_indicator_ae_iff_of_zero_notMem [Zero β] {t : Set β} (ht : (0 : β) ∉ t) :
    t ∈ Filter.map (s.indicator f) (ae μ) ↔ μ ((f ⁻¹' t)ᶜ ∪ sᶜ) = 0 := by
  classical
  rw [mem_map, mem_ae_iff, Set.indicator_preimage, Set.ite, Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ ∪ sᶜ) ∩ ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ ∪ sᶜ) = 0
  simp only [ht, if_false, Set.compl_empty, Set.empty_sdiff, Set.inter_univ, Set.preimage_const]
/-
**map_restrict_ae_le_map_indicator_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_restrict_ae_le_map_indicator_ae [Zero β] (hs : MeasurableSet s) : Filt
er.map f (ae <| μ.restrict s) <= Filter.map (s.indicator f) (ae μ)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem`：mem_map_indica
tor_ae_iff_mem_map_restrict_ae_of_zero_mem [Zero β] {t : Set β} (ht : (0 : β) in
 t) (hs : MeasurableSet s) : t in Filter.map (…
· 使用定理 `mem_map_indicator_ae_iff_of_zero_notMem`：mem_map_indicator_ae_iff_of_zer
o_notMem [Zero β] {t : Set β} (ht : (0 : β) ∉ t) : t in Filter.map (s.indicator 
f) (ae μ) ↔ μ ((f ⁻¹' t)ᶜ uni…
· 使用定理 `MeasureTheory.mem_map_restrict_ae_iff`：mem_map_restrict_ae_iff {β} {s : 
Set α} {t : Set β} {f : α -> β} (hs : MeasurableSet s) : t in Filter.map f (ae (
μ.restrict s)) ↔ μ ((f ⁻¹' …
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
theorem map_restrict_ae_le_map_indicator_ae [Zero β] (hs : MeasurableSet s) :
    Filter.map f (ae <| μ.restrict s) ≤ Filter.map (s.indicator f) (ae μ) := by
  intro t
  by_cases ht : (0 : β) ∈ t
  · rw [mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem ht hs]
    exact id
  rw [mem_map_indicator_ae_iff_of_zero_notMem ht, mem_map_restrict_ae_iff hs]
  exact fun h => measure_mono_null (Set.inter_subset_left.trans Set.subset_union_left) h

variable [Zero β]
/-
**indicator_ae_eq_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indicator_ae_eq_restrict (hs : MeasurableSet s) : indicator s f =ᵐ[μ.restr
ict s] f
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `piecewise_ae_eq_restrict`：piecewise_ae_eq_restrict [DecidablePred (· in 
s)] (hs : MeasurableSet s) : piecewise s f g =ᵐ[μ.restrict s] f
-/
theorem indicator_ae_eq_restrict (hs : MeasurableSet s) : indicator s f =ᵐ[μ.restrict s] f := by
  classical exact piecewise_ae_eq_restrict hs
/-
**indicator_ae_eq_restrict_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indicator_ae_eq_restrict_compl (hs : MeasurableSet s) : indicator s f =ᵐ[μ
.restrict sᶜ] 0
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `piecewise_ae_eq_restrict_compl`：piecewise_ae_eq_restrict_compl [Decidabl
ePred (· in s)] (hs : MeasurableSet s) : piecewise s f g =ᵐ[μ.restrict sᶜ] g
-/
theorem indicator_ae_eq_restrict_compl (hs : MeasurableSet s) :
    indicator s f =ᵐ[μ.restrict sᶜ] 0 := by
  classical exact piecewise_ae_eq_restrict_compl hs
/-
**indicator_ae_eq_of_restrict_compl_ae_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indicator_ae_eq_of_restrict_compl_ae_eq_zero (hs : MeasurableSet s) (hf : 
f =ᵐ[μ.restrict sᶜ] 0) : s.indicator f =ᵐ[μ] f
参数：hs : MeasurableSet s；hf : f =ᵐ[μ.restrict sᶜ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem indicator_ae_eq_of_restrict_compl_ae_eq_zero (hs : MeasurableSet s)
    (hf : f =ᵐ[μ.restrict sᶜ] 0) : s.indicator f =ᵐ[μ] f := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [hxs, Set.indicator_of_mem]
  · simp only [hx hxs, Pi.zero_apply, Set.indicator_apply_eq_zero, imp_true_iff]
/-
**indicator_ae_eq_zero_of_restrict_ae_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indicator_ae_eq_zero_of_restrict_ae_eq_zero (hs : MeasurableSet s) (hf : f
 =ᵐ[μ.restrict s] 0) : s.indicator f =ᵐ[μ] 0
参数：hs : MeasurableSet s；hf : f =ᵐ[μ.restrict s] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem indicator_ae_eq_zero_of_restrict_ae_eq_zero (hs : MeasurableSet s)
    (hf : f =ᵐ[μ.restrict s] 0) : s.indicator f =ᵐ[μ] 0 := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [hxs, hx hxs, Set.indicator_of_mem]
  · simp [hxs]
/-
**indicator_ae_eq_of_ae_eq_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.indicator f =ᵐ[μ] t.ind
icator f
参数：hst : s =ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `piecewise_ae_eq_of_ae_eq_set`：piecewise_ae_eq_of_ae_eq_set [DecidablePre
d (· in s)] [DecidablePred (· in t)] (hst : s =ᵐ[μ] t) : s.piecewise f g =ᵐ[μ] t
.piecewise f g
-/
theorem indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.indicator f =ᵐ[μ] t.indicator f := by
  classical exact piecewise_ae_eq_of_ae_eq_set hst
/-
**indicator_meas_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indicator_meas_zero (hs : μ s = 0) : indicator s f =ᵐ[μ] 0
参数：hs : μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `indicator_ae_eq_of_ae_eq_set`：indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ
] t) : s.indicator f =ᵐ[μ] t.indicator f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
· 使用定理 `Set.indicator_empty'`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f
 : α → M), ∅.indicator f = 0
-/
theorem indicator_meas_zero (hs : μ s = 0) : indicator s f =ᵐ[μ] 0 :=
  indicator_empty' f ▸ indicator_ae_eq_of_ae_eq_set (ae_eq_empty.2 hs)
/-
**ae_eq_restrict_iff_indicator_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_eq_restrict_iff_indicator_ae_eq {g : α -> β} (hs : MeasurableSet s) : f
 =ᵐ[μ.restrict s] g ↔ s.indicator f =ᵐ[μ] s.indicator g
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem ae_eq_restrict_iff_indicator_ae_eq {g : α → β} (hs : MeasurableSet s) :
    f =ᵐ[μ.restrict s] g ↔ s.indicator f =ᵐ[μ] s.indicator g := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h] with x hx
  · by_cases hxs : x ∈ s
    · simp [hxs, hx hxs]
    · simp [hxs]
  · intro hxs
    simpa [hxs] using hx

end IndicatorFunction

section Sum

open Finset in
/-- An upper bound on a sum of restrictions of a measure `μ`. This can be used to compare
`∫ x ∈ X, f x ∂μ` with `∑ i, ∫ x ∈ (s i), f x ∂μ`, where `s` is a cover of `X`. -/
/-
**MeasureTheory.Measure.sum_restrict_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasureTheory.Measure.sum_restrict_le {_ : MeasurableSpace α} {μ : Measure
 α} {s : ι -> Set α} {M : Nat} (hs_meas : forall i, MeasurableSet (s i)) (hs : f
orall y, {i | y in s i}.encard <= M) : Measure.sum (fun i => μ.restrict (s i)) <
= M • μ.restrict (⋃ i, s i)
参数：hs_meas : forall i, MeasurableSet (s i)；hs : forall y, {i | y in s i}.encard 
<= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `Summable.tsum_le_of_sum_le`：∀ {ι : Type u_1} {α : Type u_3} {L : Summati
onFilter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [inst_2 : Topologic
alSpace α] [Orde…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Finset.measurableSet_biInter`：Finset.measurableSet_biInter {f : β -> Set
 α} (s : Finset β) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂ b
 in s, f b)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Finset.notMem_singleton`：notMem_singleton {a b : α} : a ∉ ({b} : Finset 
α) ↔ a != b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 96 条，此处仅展示前 30 条）

--- 原说明 ---
An upper bound on a sum of restrictions of a measure `μ`. This can be used to co
mpare
`∫ x ∈ X, f x ∂μ` with `∑ i, ∫ x ∈ (s i), f x ∂μ`, where `s` is a cover of `X`.
-/
lemma MeasureTheory.Measure.sum_restrict_le {_ : MeasurableSpace α}
    {μ : Measure α} {s : ι → Set α} {M : ℕ} (hs_meas : ∀ i, MeasurableSet (s i))
    (hs : ∀ y, {i | y ∈ s i}.encard ≤ M) :
    Measure.sum (fun i ↦ μ.restrict (s i)) ≤ M • μ.restrict (⋃ i, s i) := by
  classical
  refine le_iff.mpr (fun t ht ↦ le_of_eq_of_le (sum_apply _ ht) ?_)
  refine ENNReal.summable.tsum_le_of_sum_le (fun F ↦ ?_)
  -- `P` is a partition of `⋃ i ∈ F, s i` indexed by `C ∈ Cs` (nonempty subsets of `F`).
  -- `P` is a partition of `s i` when restricted to `C ∈ G i` (subsets of `F` containing `i`).
  let P (C : Finset ι) := (⋂ i ∈ C, s i) ∩ (⋂ i ∈ (F \ C), (s i)ᶜ)
  let Cs := F.powerset \ {∅}
  let G (i : ι) := { C | C ∈ F.powerset ∧ i ∈ C }
  have P_meas C : MeasurableSet (P C) :=
    measurableSet_biInter C (fun i _ ↦ hs_meas i) |>.inter <|
      measurableSet_biInter _ (fun i _ ↦ (hs_meas i).compl)
  have P_cover {i : ι} (hi : i ∈ F) : s i ⊆ ⋃ C ∈ G i, P C := by
    refine fun x hx ↦ Set.mem_biUnion (x := F.filter (x ∈ s ·)) ?_ ?_
    · exact ⟨Finset.mem_powerset.mpr (filter_subset _ F), mem_filter.mpr ⟨hi, hx⟩⟩
    · simp_rw [P, mem_inter_iff, mem_iInter, Finset.mem_sdiff, mem_filter]; tauto
  have iUnion_P : ⋃ C ∈ Cs, P C ⊆ ⋃ i, s i := by
    intro x hx
    simp_rw [Cs, Finset.mem_sdiff, mem_iUnion] at hx
    have ⟨C, ⟨_, C_nonempty⟩, hxC⟩ := hx
    have ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr <| Finset.notMem_singleton.mp C_nonempty
    exact ⟨s i, ⟨i, rfl⟩, hxC.1 (s i) ⟨i, by simp [hi]⟩⟩
  have P_subset_s {i : ι} {C : Finset ι} (hiC : i ∈ C) : P C ⊆ s i := by
    intro x hx
    simp only [P, mem_inter_iff, mem_iInter] at hx
    exact hx.1 i hiC
  have mem_C {i} (hi : i ∈ F) {C : Finset ι} {x : α} (hx : x ∈ P C) (hxs : x ∈ s i) : i ∈ C := by
    rw [mem_inter_iff, mem_iInter₂, mem_iInter₂] at hx
    exact of_not_not fun h ↦ hx.2 i (mem_sdiff.mpr ⟨hi, h⟩) hxs
  have C_subset_C {C₁ C₂} (hC₁ : C₁ ∈ Cs) {x : α} (hx : x ∈ P C₁ ∩ P C₂) : C₁ ⊆ C₂ :=
    fun i hi ↦ mem_C (mem_powerset.mp (sdiff_subset hC₁) hi) hx.2 <| P_subset_s hi hx.1
  calc ∑ i ∈ F, (μ.restrict (s i)) t
    _ ≤ ∑ i ∈ F, Measure.sum (fun (C : G i) ↦ μ.restrict (P C)) t :=
      F.sum_le_sum fun i hi ↦ (restrict_mono_set μ (P_cover hi) t).trans <|
        restrict_biUnion_le ((finite_toSet F.powerset).subset (sep_subset _ _)).countable t
    _ = ∑ i ∈ F, ∑' (C : G i), μ.restrict (P C) t := by simp_rw [Measure.sum_apply _ ht]
    _ = ∑' C, ∑ i ∈ F, (G i).indicator (fun C ↦ μ.restrict (P C) t) C := by
      rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
      congr with i
      rw [tsum_subtype (G i) (fun C ↦ (μ.restrict (P C)) t)]
    _ = ∑ C ∈ Cs, ∑ i ∈ F, (C : Set ι).indicator (fun _ ↦ (μ.restrict (P C)) t) i := by
      rw [sum_eq_tsum_indicator]
      congr with C
      by_cases hC : C ∈ F.powerset <;> by_cases hC' : C = ∅ <;>
        simp [hC, hC', Cs, G, indicator, -Finset.mem_powerset, -coe_powerset]
    _ = ∑ C ∈ Cs, {a ∈ F | a ∈ C}.card • μ.restrict (P C) t := by simp [indicator]; rfl
    _ ≤ ∑ C ∈ Cs, M • μ.restrict (P C) t := by
      refine sum_le_sum fun C hC ↦ ?_
      by_cases hPC : P C = ∅
      · simp [hPC]
      have hCM : (C : Set ι).encard ≤ M :=
        have ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hPC
        (encard_mono (mem_iInter₂.mp hx.1)).trans (hs x)
      exact nsmul_le_nsmul_left zero_le <| calc {a ∈ F | a ∈ C}.card
        _ ≤ C.card := card_mono <| fun i hi ↦ (F.mem_filter.mp hi).2
        _ = (C : Set ι).ncard := (ncard_coe_finset C).symm
        _ ≤ M := ENat.toNat_le_of_le_natCast hCM
    _ = M • (μ.restrict (⋃ C ∈ Cs, (P C)) t) := by
      rw [← smul_sum, ← Cs.tsum_subtype, μ.restrict_biUnion_finset _ P_meas, Measure.sum_apply _ ht]
      refine fun C₁ hC₁ C₂ hC₂ hC ↦ Set.disjoint_iff.mpr fun x hx ↦ hC <| ?_
      exact subset_antisymm (C_subset_C hC₁ hx) (C_subset_C hC₂ (Set.inter_comm _ _ ▸ hx))
    _ ≤ (M • μ.restrict (⋃ i, s i)) t := by
      rw [Measure.smul_apply]
      exact nsmul_le_nsmul_right (μ.restrict_mono_set iUnion_P t) M

end Sum

