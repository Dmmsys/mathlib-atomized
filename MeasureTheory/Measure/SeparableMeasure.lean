/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.SetAlgebra

/-!
# Separable measure

The goal of this file is to give a sufficient condition on the measure space `(X, μ)` and the
`NormedAddCommGroup E` for the space `MeasureTheory.Lp E p μ` to have `SecondCountableTopology` when
`1 ≤ p < ∞`. To do so we define the notion of a `MeasureTheory.MeasureDense` family and a
separable measure (`MeasureTheory.IsSeparable`).
We prove that if `X` is `MeasurableSpace.CountablyGenerated` and `μ` is s-finite, then `μ`
is separable. We then prove that if `μ` is separable and `E` is second-countable,
then `Lp E p μ` is second-countable.

A family `𝒜` of subsets of `X` is said to be **measure-dense** if it contains only measurable sets
and can approximate any measurable set with finite measure, in the sense that
for any measurable set `s` such that `μ s ≠ ∞`, `μ (s ∆ t)` can be made
arbitrarily small when `t ∈ 𝒜`. We show below that such a family can be chosen to contain only
sets with finite measure.
The term "measure-dense" is justified by the fact that the approximating condition translates
to the usual notion of density in the metric space made by constant indicators of measurable sets
equipped with the `Lᵖ` norm.

A measure `μ` is **separable** if it admits a countable and measure-dense family of sets.
The term "separable" is justified by the fact that the definition translates to the usual notion
of separability in the metric space made by constant indicators equipped with the `Lᵖ` norm.

## Main definitions

* `MeasureTheory.Measure.MeasureDense μ 𝒜`: `𝒜` is a measure-dense family if it only contains
  measurable sets and if the following condition is satisfied: if `s` is measurable with finite
  measure, then for any `ε > 0` there exists `t ∈ 𝒜` such that `μ (s ∆ t) < ε`.
* `MeasureTheory.IsSeparable`: A measure is separable if there exists a countable and
  measure-dense family.

## Main statements

* `MeasureTheory.instSecondCountableLp`: If `μ` is separable, `E` is second-countable and
  `1 ≤ p < ∞` then `Lp E p μ` is second-countable. This is in particular true if `X` is countably
  generated and `μ` is s-finite.

## Implementation notes

Through the whole file we consider a measurable space `X` equipped with a measure `μ`, and also
a normed commutative group `E`. We also consider an extended non-negative real `p` such that
`1 ≤ p < ∞`. This is registered as instances via `one_le_p : Fact (1 ≤ p)` and
`p_ne_top : Fact (p ≠ ∞)`, so the properties are accessible via `one_le_p.elim` and `p_ne_top.elim`.

Through the whole file, when we write that an extended non-negative real is finite, it is always
written `≠ ∞` rather than `< ∞`. See `Ne.lt_top` and `ne_of_lt` to switch from one to the other.

## References

* [D. L. Cohn, *Measure Theory*][cohn2013measure]

## Tags

separable measure, measure-dense, Lp space, second-countable
-/

public section

open MeasurableSpace Set ENNReal TopologicalSpace symmDiff Real

namespace MeasureTheory

variable {X E : Type*} [m : MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
variable {p : ℝ≥0∞} [one_le_p : Fact (1 ≤ p)] [p_ne_top : Fact (p ≠ ∞)] {𝒜 : Set (Set X)}

section MeasureDense

/-! ### Definition of a measure-dense family, basic properties and sufficient conditions -/

/-- A family `𝒜` of sets of a measure space is said to be measure-dense if it contains only
measurable sets and can approximate any measurable set with finite measure, in the sense that
for any measurable set `s` with finite measure the symmetric difference `s ∆ t` can be made
arbitrarily small when `t ∈ 𝒜`. We show below that such a family can be chosen to contain only
sets with finite measure.

The term "measure-dense" is justified by the fact that the approximating condition translates
to the usual notion of density in the metric space made by constant indicators of measurable sets
equipped with the `Lᵖ` norm. -/
/-
**MeasureTheory.Measure.MeasureDense** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：{X : Type u_1} → [m : MeasurableSpace X] → MeasureTheory.Measure X → Set (
Set X) → Prop
参数：Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `𝒜` of sets of a measure space is said to be measure-dense if it contai
ns only
measurable sets and can approximate any measurable set with finite measure, in t
he sense that
for any measurable set `s` with finite measure the symmetric difference `s ∆ t` 
can be made
arbitrarily small when `t ∈ 𝒜`. We show below that such a family can be chosen t
o contain only
sets with finite measure.

The term "measure-dense" is justified by the fact that the approximating conditi
on translates
to the usual notion of density in the metric space made by constant indicators o
f measurable sets
equipped with the `Lᵖ` norm.
-/
structure Measure.MeasureDense (μ : Measure X) (𝒜 : Set (Set X)) : Prop where
  /-- Each set has to be measurable. -/
  measurable : ∀ s ∈ 𝒜, MeasurableSet s
  /-- Any measurable set can be approximated by sets in the family. -/
  approx : ∀ s, MeasurableSet s → μ s ≠ ∞ → ∀ ε : ℝ, 0 < ε → ∃ t ∈ 𝒜, μ (s ∆ t) < ENNReal.ofReal ε
/-
**MeasureTheory.Measure.MeasureDense.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.MeasureDense`。
形式化陈述：∀ {X : Type u_1} [m : MeasurableSpace X] {μ : MeasureTheory.Measure X} {𝒜 
: Set (Set X)}, μ.MeasureDense 𝒜 → 𝒜.Nonempty
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MeasureDense.approx`：∀ {X : Type u_1} [m : Measura
bleSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.MeasureDense 𝒜 
→     ∀ (s : Set X), Measurable…
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem Measure.MeasureDense.nonempty (h𝒜 : μ.MeasureDense 𝒜) : 𝒜.Nonempty := by
  rcases h𝒜.approx ∅ MeasurableSet.empty (by simp) 1 (by simp) with ⟨t, ht, -⟩
  exact ⟨t, ht⟩
/-
**MeasureTheory.Measure.MeasureDense.nonempty'** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.MeasureDense`。
形式化陈述：∀ {X : Type u_1} [m : MeasurableSpace X] {μ : MeasureTheory.Measure X} {𝒜 
: Set (Set X)},   μ.MeasureDense 𝒜 → {s | s ∈ 𝒜 ∧ μ s ≠ ⊤}.Nonempty
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MeasureDense.approx`：∀ {X : Type u_1} [m : Measura
bleSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.MeasureDense 𝒜 
→     ∀ (s : Set X), Measurable…
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.bot_eq_empty`：bot_eq_empty : (⊥ : Set α) = ∅
· 使用定理 `bot_symmDiff`：bot_symmDiff : ⊥ ∆ a = a
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
-/
theorem Measure.MeasureDense.nonempty' (h𝒜 : μ.MeasureDense 𝒜) :
    {s | s ∈ 𝒜 ∧ μ s ≠ ∞}.Nonempty := by
  rcases h𝒜.approx ∅ MeasurableSet.empty (by simp) 1 (by simp) with ⟨t, ht, hμt⟩
  refine ⟨t, ht, ?_⟩
  convert! ne_top_of_lt hμt
  rw [← bot_eq_empty, bot_symmDiff]

/-- The set of measurable sets is measure-dense. -/
/-
**MeasureTheory.measureDense_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measureDense_measurableSet : μ.MeasureDense {s | MeasurableSet s} where me
asurable _ h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_self`：symmDiff_self : a ∆ a = ⊥
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
The set of measurable sets is measure-dense.
-/
theorem measureDense_measurableSet : μ.MeasureDense {s | MeasurableSet s} where
  measurable _ h := h
  approx s hs _ ε ε_pos := ⟨s, hs, by simpa⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.Measure.MeasureDense.completion** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure.MeasureDense`。
形式化陈述：∀ {X : Type u_1} [m : MeasurableSpace X] {μ : MeasureTheory.Measure X} {𝒜 
: Set (Set X)},   μ.MeasureDense 𝒜 → μ.completion.MeasureDense 𝒜
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasureTheory.Measure.MeasureDense.measurable`：∀ {X : Type u_1} [m : Mea
surableSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.MeasureDens
e 𝒜 → ∀ s ∈ 𝒜, MeasurableSet s
· 使用定理 `MeasureTheory.Measure.MeasureDense.approx`：∀ {X : Type u_1} [m : Measura
bleSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.MeasureDense 𝒜 
→     ∀ (s : Set X), Measurable…
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.completion_apply`：completion_apply {_ : Measurable
Space α} (μ : Measure α) (s : Set α) : μ.completion s = μ s
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_set_symmDiff`：ae_eq_set_symmDiff {s' t' : Set α} (h 
: s =ᵐ[μ] t) (h' : s' =ᵐ[μ] t') : s ∆ s' =ᵐ[μ] t ∆ t'
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.NullMeasurableSet.toMeasurable_ae_eq`：toMeasurable_ae_eq (
h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem Measure.MeasureDense.completion (h𝒜 : μ.MeasureDense 𝒜) : μ.completion.MeasureDense 𝒜 where
  measurable s hs := (h𝒜.measurable s hs).nullMeasurableSet
  approx s hs hμs ε ε_pos := by
    obtain ⟨t, ht, hμst⟩ :=
      h𝒜.approx (toMeasurable μ s) (measurableSet_toMeasurable μ s) (by simpa) ε ε_pos
    refine ⟨t, ht, ?_⟩
    convert! hμst using 1
    rw [completion_apply]
    exact measure_congr <| ae_eq_set_symmDiff (NullMeasurableSet.toMeasurable_ae_eq hs).symm
      Filter.EventuallyEq.rfl

/-- If a family of sets `𝒜` is measure-dense in `X`, then any measurable set with finite measure
can be approximated by sets in `𝒜` with finite measure. -/
/-
**MeasureTheory.Measure.MeasureDense.fin_meas_approx** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.MeasureDense`。
形式化陈述：∀ {X : Type u_1} [m : MeasurableSpace X] {μ : MeasureTheory.Measure X} {𝒜 
: Set (Set X)},   μ.MeasureDense 𝒜 →     ∀ {s : Set X}, MeasurableSet s → μ s ≠ 
⊤ → ∀ (ε : ℝ), 0 < ε → ∃ t ∈ 𝒜, μ t ≠ ⊤ ∧ μ (symmDiff s t) < ENNReal.ofReal ε
参数：Set X；ε : ℝ；symmDiff s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MeasureDense.approx`：∀ {X : Type u_1} [m : Measura
bleSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.MeasureDense 𝒜 
→     ∀ (s : Set X), Measurable…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.measure_ne_top_iff_of_symmDiff`：measure_ne_top_iff_of_symm
Diff (hμst : μ (s ∆ t) != ∞) : μ s != ∞ ↔ μ t != ∞
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤

--- 原说明 ---
If a family of sets `𝒜` is measure-dense in `X`, then any measurable set with fi
nite measure
can be approximated by sets in `𝒜` with finite measure.
-/
lemma Measure.MeasureDense.fin_meas_approx (h𝒜 : μ.MeasureDense 𝒜) {s : Set X}
    (ms : MeasurableSet s) (hμs : μ s ≠ ∞) (ε : ℝ) (ε_pos : 0 < ε) :
    ∃ t ∈ 𝒜, μ t ≠ ∞ ∧ μ (s ∆ t) < ENNReal.ofReal ε := by
  rcases h𝒜.approx s ms hμs ε ε_pos with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, (measure_ne_top_iff_of_symmDiff <| ne_top_of_lt ht).1 hμs, ht⟩

variable (p) in
/-- If `𝒜` is a measure-dense family of sets and `c : E`, then the set of constant indicators
with constant `c` whose underlying set is in `𝒜` is dense in the set of constant indicators
which are in `Lp E p μ` when `1 ≤ p < ∞`. -/
/-
**MeasureTheory.Measure.MeasureDense.indicatorConstLp_subset_closure** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure.MeasureDense`。
形式化陈述：∀ {X : Type u_1} {E : Type u_2} [m : MeasurableSpace X] [inst : NormedAddC
ommGroup E] {μ : MeasureTheory.Measure X}   (p : ENNReal) [one_le_p : Fact (1 ≤ 
p)] [p_ne_top : Fact (p ≠ ⊤)] {𝒜 : Set (Set X)} (h𝒜 : μ.MeasureDense 𝒜) (c : E),
   {x | ∃ s, ∃ (hs : MeasurableSet s) (hμs : μ s ≠ ⊤), MeasureTheory.indicatorCo
nstLp p hs hμs c = x} ⊆     closure {x | ∃ s, ∃ (hs : s ∈ 𝒜) (hμs : μ s ≠ ⊤), Me
asureTheory.indicatorConstLp p ⋯ hμs c = x}
参数：p : ENNReal；1 ≤ p；p ≠ ⊤；Set X；h𝒜 : μ.MeasureDense 𝒜；c : E；hs : MeasurableSet 
s；hμs : μ s ≠ ⊤；hs : s ∈ 𝒜；hμs : μ s ≠ ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.MeasureDense.measurable`：∀ {X : Type u_1} [m : Mea
surableSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.MeasureDens
e 𝒜 → ∀ s ∈ 𝒜, MeasurableSet s
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `MeasureTheory.Measure.MeasureDense.nonempty'`：∀ {X : Type u_1} [m : Meas
urableSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.MeasureDense
 𝒜 → {s | s ∈ 𝒜 ∧ μ s ≠ ⊤}.Nonempt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_zero`：∀ {α : Type u_1} (M : Type u_3) [inst : Zero M] (s :
 Set α), (s.indicator fun x => 0) = fun x => 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MemLp.toLp.congr_simp`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f f_1 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `MeasureTheory.Measure.MeasureDense.fin_meas_approx`：∀ {X : Type u_1} [m 
: MeasurableSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.Measur
eDense 𝒜 →     ∀ {s : Set X}, Measurable…
· 使用定理 `MeasurableSet.symmDiff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ 
: Set α},   MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (symmDiff s₁ s₂)
· 使用定理 `MeasureTheory.dist_indicatorConstLp_eq_norm`：dist_indicatorConstLp_eq_no
rm {t : Set α} {ht : MeasurableSet t} {hμt : μ t != ∞} : dist (indicatorConstLp 
p hs hμs c) (indicatorConstLp p h…
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
If `𝒜` is a measure-dense family of sets and `c : E`, then the set of constant i
ndicators
with constant `c` whose underlying set is in `𝒜` is dense in the set of constant
 indicators
which are in `Lp E p μ` when `1 ≤ p < ∞`.
-/
theorem Measure.MeasureDense.indicatorConstLp_subset_closure (h𝒜 : μ.MeasureDense 𝒜) (c : E) :
    {indicatorConstLp p hs hμs c | (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)} ⊆
    closure {indicatorConstLp p (h𝒜.measurable s hs) hμs c |
      (s : Set X) (hs : s ∈ 𝒜) (hμs : μ s ≠ ∞)} := by
  obtain rfl | hc := eq_or_ne c 0
  · refine Subset.trans ?_ subset_closure
    rintro - ⟨s, ms, hμs, rfl⟩
    obtain ⟨t, ht, hμt⟩ := h𝒜.nonempty'
    refine ⟨t, ht, hμt, ?_⟩
    simp_rw [indicatorConstLp]
    simp
  · have p_pos : 0 < p := lt_of_lt_of_le (by simp) one_le_p.elim
    rintro - ⟨s, ms, hμs, rfl⟩
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    have aux : 0 < (ε / ‖c‖) ^ p.toReal := rpow_pos_of_pos (div_pos hε (norm_pos_iff.2 hc)) _
    obtain ⟨t, ht, hμt, hμst⟩ := h𝒜.fin_meas_approx ms hμs ((ε / ‖c‖) ^ p.toReal) aux
    refine ⟨indicatorConstLp p (h𝒜.measurable t ht) hμt c,
      ⟨t, ht, hμt, rfl⟩, ?_⟩
    rw [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp p_pos.ne.symm p_ne_top.elim]
    calc
      ‖c‖ * μ.real (s ∆ t) ^ (1 / p.toReal)
        < ‖c‖ * (ENNReal.ofReal ((ε / ‖c‖) ^ p.toReal)).toReal ^ (1 / p.toReal) := by
          have := toReal_pos p_pos.ne.symm p_ne_top.elim
          rw [measureReal_def]
          gcongr
          exact ofReal_ne_top
      _ = ε := by
        rw [toReal_ofReal (by positivity),
          one_div, Real.rpow_rpow_inv (by positivity) (toReal_pos p_pos.ne.symm p_ne_top.elim).ne',
          mul_div_cancel₀ _ (norm_ne_zero_iff.2 hc)]

/-- If a family of sets `𝒜` is measure-dense in `X`, then it is also the case for the sets in `𝒜`
with finite measure. -/
/-
**MeasureTheory.Measure.MeasureDense.fin_meas** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.MeasureDense`。
形式化陈述：∀ {X : Type u_1} [m : MeasurableSpace X] {μ : MeasureTheory.Measure X} {𝒜 
: Set (Set X)},   μ.MeasureDense 𝒜 → μ.MeasureDense {s | s ∈ 𝒜 ∧ μ s ≠ ⊤}
参数：Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MeasureDense.measurable`：∀ {X : Type u_1} [m : Mea
surableSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.MeasureDens
e 𝒜 → ∀ s ∈ 𝒜, MeasurableSet s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.MeasureDense.fin_meas_approx`：∀ {X : Type u_1} [m 
: MeasurableSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.Measur
eDense 𝒜 →     ∀ {s : Set X}, Measurable…

--- 原说明 ---
If a family of sets `𝒜` is measure-dense in `X`, then it is also the case for th
e sets in `𝒜`
with finite measure.
-/
theorem Measure.MeasureDense.fin_meas (h𝒜 : μ.MeasureDense 𝒜) :
    μ.MeasureDense {s | s ∈ 𝒜 ∧ μ s ≠ ∞} where
  measurable s h := h𝒜.measurable s h.1
  approx s ms hμs ε ε_pos := by
    rcases Measure.MeasureDense.fin_meas_approx h𝒜 ms hμs ε ε_pos with ⟨t, t_mem, hμt, hμst⟩
    exact ⟨t, ⟨t_mem, hμt⟩, hμst⟩

variable (μ) in
/-- If a measurable space equipped with a finite measure is generated by an algebra of sets, then
this algebra of sets is measure-dense. -/
/-
**MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.MeasureDense`。
形式化陈述：∀ {X : Type u_1} [m : MeasurableSpace X] (μ : MeasureTheory.Measure X) {𝒜 
: Set (Set X)}   [MeasureTheory.IsFiniteMeasure μ],   MeasureTheory.IsSetAlgebra
 𝒜 → m = MeasurableSpace.generateFrom 𝒜 → μ.MeasureDense 𝒜
参数：μ : MeasureTheory.Measure X；Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.generateFrom_induction`：generateFrom_induction (C : Set 
(Set α)) (p : forall s : Set α, MeasurableSet[generateFrom C] s -> Prop) (hC : f
orall t in C, forall ht, p t…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `symmDiff_self`：symmDiff_self : a ∆ a = ⊥
· 使用定理 `MeasureTheory.measureReal_empty`：∀ {α : Type u_1} {x : MeasurableSpace α
} {μ : MeasureTheory.Measure α}, μ.real ∅ = 0
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.IsSetAlgebra.empty_mem`：∀ {α : Type u_1} {𝒜 : Set (Set α)}
, MeasureTheory.IsSetAlgebra 𝒜 → ∅ ∈ 𝒜
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.IsSetAlgebra.compl_mem`：∀ {α : Type u_1} {𝒜 : Set (Set α)}
, MeasureTheory.IsSetAlgebra 𝒜 → ∀ ⦃s : Set α⦄, s ∈ 𝒜 → sᶜ ∈ 𝒜
· 使用定理 `compl_symmDiff_compl`：compl_symmDiff_compl : aᶜ ∆ bᶜ = a ∆ b
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.tendsto_measure_iUnion_accumulate`：tendsto_measure_iUnion_
accumulate {α ι : Type*} [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] 
{_ : MeasurableSpace α} {μ : Measure …
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.tendsto_atTop`：tendsto_atTop [Nonempty β] [SemilatticeSup β] {u :
 β -> α} {a : α} : Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N
, dist (u …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ENNReal.tendsto_toReal_iff`：tendsto_toReal_iff {ι} {fi : Filter ι} {f : 
ι -> Real>=0∞} (hf : forall i, f i != ∞) {x : Real>=0∞} (hx : x != ∞) : Tendsto 
(fun n => (f n).…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
（共 156 条，此处仅展示前 30 条）

--- 原说明 ---
If a measurable space equipped with a finite measure is generated by an algebra 
of sets, then
this algebra of sets is measure-dense.
-/
theorem Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite [IsFiniteMeasure μ]
    (h𝒜 : IsSetAlgebra 𝒜) (hgen : m = MeasurableSpace.generateFrom 𝒜) : μ.MeasureDense 𝒜 where
  measurable s hs := hgen ▸ measurableSet_generateFrom hs
  approx s ms := by
    -- We want to show that any measurable set can be approximated by sets in `𝒜`. To do so, it is
    -- enough to show that such sets constitute a `σ`-algebra containing `𝒜`. This is contained in
    -- the theorem `generateFrom_induction`.
    have : MeasurableSet s ∧ ∀ (ε : ℝ), 0 < ε → ∃ t ∈ 𝒜, μ.real (s ∆ t) < ε := by
      rw [hgen] at ms
      induction s, ms using generateFrom_induction with
      -- If `t ∈ 𝒜`, then `μ (t ∆ t) = 0` which is less than any `ε > 0`.
      | hC t t_mem _ =>
        exact ⟨hgen ▸ measurableSet_generateFrom t_mem, fun ε ε_pos ↦ ⟨t, t_mem, by simpa⟩⟩
      -- `∅ ∈ 𝒜` and `μ (∅ ∆ ∅) = 0` which is less than any `ε > 0`.
      | empty => exact ⟨MeasurableSet.empty, fun ε ε_pos ↦ ⟨∅, h𝒜.empty_mem, by simpa⟩⟩
      -- If `s` is measurable and `t ∈ 𝒜` such that `μ (s ∆ t) < ε`, then `tᶜ ∈ 𝒜` and
      -- `μ (sᶜ ∆ tᶜ) = μ (s ∆ t) < ε` so `sᶜ` can be approximated.
      | compl t _ ht =>
        refine ⟨ht.1.compl, fun ε ε_pos ↦ ?_⟩
        obtain ⟨u, u_mem, hμtcu⟩ := ht.2 ε ε_pos
        exact ⟨uᶜ, h𝒜.compl_mem u_mem, by rwa [compl_symmDiff_compl]⟩
      -- Let `(fₙ)` be a sequence of measurable sets and `ε > 0`.
      | iUnion f _ hf =>
        refine ⟨MeasurableSet.iUnion (fun n ↦ (hf n).1), fun ε ε_pos ↦ ?_⟩
        -- We have  `μ (⋃ n ≤ N, fₙ) ⟶ μ (⋃ n, fₙ)`.
        have := tendsto_measure_iUnion_accumulate (μ := μ) (f := f)
        rw [← tendsto_toReal_iff (fun _ ↦ measure_ne_top _ _) (measure_ne_top _ _)] at this
        -- So there exists `N` such that `μ (⋃ n, fₙ) - μ (⋃ n ≤ N, fₙ) < ε/2`.
        rcases Metric.tendsto_atTop.1 this (ε / 2) (by linarith [ε_pos]) with ⟨N, hN⟩
        -- For any `n ≤ N` there exists `gₙ ∈ 𝒜` such that `μ (fₙ ∆ gₙ) < ε/(2*(N+1))`.
        choose g g_mem hg using fun n ↦ (hf n).2 (ε / (2 * (N + 1))) (div_pos ε_pos (by linarith))
        -- Therefore we have
        -- `μ ((⋃ n, fₙ) ∆ (⋃ n ≤ N, gₙ))`
        --   `≤ μ ((⋃ n, fₙ) ∆ (⋃ n ≤ N, fₙ)) + μ ((⋃ n ≤ N, fₙ) ∆ (⋃ n ≤ N, gₙ))`
        --   `< ε/2 + ∑ n ≤ N, μ (fₙ ∆ gₙ)` (see `biSup_symmDiff_biSup_le`)
        --   `< ε/2 + (N+1)*ε/(2*(N+1)) = ε/2`.
        refine ⟨⋃ n ∈ Finset.range (N + 1), g n, h𝒜.biUnion_mem _ (fun i _ ↦ g_mem i), ?_⟩
        calc
          μ.real ((⋃ n, f n) ∆ (⋃ n ∈ (Finset.range (N + 1)), g n))
            ≤ (μ ((⋃ n, f n) \ ((⋃ n ∈ (Finset.range (N + 1)), f n)) ∪
              ((⋃ n ∈ (Finset.range (N + 1)), f n) ∆
              (⋃ n ∈ (Finset.range (N + 1)), g ↑n)))).toReal :=
                toReal_mono (measure_ne_top _ _)
                  (measure_mono <| symmDiff_of_ge (iUnion_subset <|
                  fun i ↦ iUnion_subset (fun _ ↦ subset_iUnion f i)) ▸ symmDiff_triangle ..)
          _ ≤ (μ ((⋃ n, f n) \
              ((⋃ n ∈ (Finset.range (N + 1)), f n)))).toReal +
              (μ ((⋃ n ∈ (Finset.range (N + 1)), f n) ∆
              (⋃ n ∈ (Finset.range (N + 1)), g ↑n))).toReal := by
                rw [← toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
                exact toReal_mono (add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) <|
                  measure_union_le _ _
          _ < ε := by
                rw [← add_halves ε]
                apply _root_.add_lt_add
                · rw [measure_sdiff (h_fin := measure_ne_top _ _),
                    toReal_sub_of_le (ha := measure_ne_top _ _)]
                  · apply lt_of_le_of_lt (sub_le_dist ..)
                    simp only [Finset.mem_range, Nat.lt_add_one_iff]
                    exact (dist_comm (α := ℝ) .. ▸ hN N (le_refl N))
                  · exact measure_mono <| iUnion_subset <|
                      fun i ↦ iUnion_subset fun _ ↦ subset_iUnion f i
                  · exact iUnion_subset <| fun i ↦ iUnion_subset (fun _ ↦ subset_iUnion f i)
                  · exact MeasurableSet.biUnion (countable_coe_iff.1 inferInstance)
                      (fun n _ ↦ (hf n).1.nullMeasurableSet)
                · calc
                    (μ ((⋃ n ∈ (Finset.range (N + 1)), f n) ∆
                    (⋃ n ∈ (Finset.range (N + 1)), g ↑n))).toReal
                      ≤ μ.real (⋃ n ∈ (Finset.range (N + 1)), f n ∆ g n) :=
                          toReal_mono (measure_ne_top _ _) (measure_mono biSup_symmDiff_biSup_le)
                    _ ≤ ∑ n ∈ Finset.range (N + 1), μ.real (f n ∆ g n) := by
                          simp_rw [measureReal_def, ← toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
                          exact toReal_mono (ne_of_lt <| sum_lt_top.2 fun _ _ ↦ measure_lt_top μ _)
                            (measure_biUnion_finset_le _ _)
                    _ < ∑ n ∈ Finset.range (N + 1), (ε / (2 * (N + 1))) :=
                          Finset.sum_lt_sum (fun i _ ↦ le_of_lt (hg i)) ⟨0, by simp, hg 0⟩
                    _ ≤ ε / 2 := by
                          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                            Nat.cast_add, Nat.cast_one]
                          rw [div_mul_eq_div_mul_one_div, ← mul_assoc, mul_comm ((N : ℝ) + 1),
                            mul_assoc]
                          exact mul_le_of_le_one_right (by linarith [ε_pos]) <|
                            le_of_eq <| mul_one_div_cancel <| Nat.cast_add_one_ne_zero _
    rintro - ε ε_pos
    rcases this.2 ε ε_pos with ⟨t, t_mem, hμst⟩
    exact ⟨t, t_mem, (lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 hμst⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- If a measure space `X` is generated by an algebra of sets which contains a monotone countable
family of sets with finite measure spanning `X` (thus the measure is `σ`-finite), then this algebra
of sets is measure-dense. -/
/-
**MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.MeasureDense`。
形式化陈述：∀ {X : Type u_1} [m : MeasurableSpace X] {μ : MeasureTheory.Measure X} {𝒜 
: Set (Set X)},   MeasureTheory.IsSetAlgebra 𝒜 → ∀ (S : μ.FiniteSpanningSetsIn 𝒜
), m = MeasurableSpace.generateFrom 𝒜 → μ.MeasureDense 𝒜
参数：Set X；S : μ.FiniteSpanningSetsIn 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.IsSetAlgebra.biUnion_mem`：biUnion_mem {ι : Type*} (h𝒜 : Is
SetAlgebra 𝒜) {s : ι -> Set α} (S : Finset ι) (hs : forall i in S, s i in 𝒜) : ⋃
 i in S, s i in 𝒜
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.set_mem`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : 
μ.FiniteSpanningSetsIn C) (i : ℕ), self.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `MeasureTheory.measure_biUnion_lt_top`：measure_biUnion_lt_top {s : Set β}
 {f : β -> Set α} (hs : s.Finite) (hfin : forall i in s, μ (f i) < ∞) : μ (⋃ i i
n s, f i) < ∞
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.finite`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : μ
.FiniteSpanningSetsIn C) (i : ℕ), μ (se…
· 使用定理 `Set.iUnion_accumulate`：iUnion_accumulate [Preorder α] : ⋃ x, accumulate 
s x = ⋃ x, s x
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.spanning`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self :
 μ.FiniteSpanningSetsIn C), ⋃ i, self.set…
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `MeasureTheory.tendsto_measure_iUnion_atTop`：tendsto_measure_iUnion_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hm : M
onotone s) : Tendsto (μ ∘ s) atT…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.tendsto_atTop`：tendsto_atTop [Nonempty β] [SemilatticeSup β] {u :
 β -> α} {a : α} : Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N
, dist (u …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
（共 117 条，此处仅展示前 30 条）

--- 原说明 ---
If a measure space `X` is generated by an algebra of sets which contains a monot
one countable
family of sets with finite measure spanning `X` (thus the measure is `σ`-finite)
, then this algebra
of sets is measure-dense.
-/
theorem Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite (h𝒜 : IsSetAlgebra 𝒜)
    (S : μ.FiniteSpanningSetsIn 𝒜) (hgen : m = MeasurableSpace.generateFrom 𝒜) :
    μ.MeasureDense 𝒜 where
  measurable s hs := hgen ▸ measurableSet_generateFrom hs
  approx s ms hμs ε ε_pos := by
    -- We use partial unions of (Sₙ) to get a monotone family spanning `X`.
    let T := accumulate S.set
    have T_mem (n) : T n ∈ 𝒜 := by
      simpa using! h𝒜.biUnion_mem {k | k ≤ n}.toFinset (fun k _ ↦ S.set_mem k)
    have T_finite (n) : μ (T n) < ∞ := by
      simpa using! measure_biUnion_lt_top {k | k ≤ n}.toFinset.finite_toSet
        (fun k _ ↦ S.finite k)
    have T_spanning : ⋃ n, T n = univ := S.spanning ▸ iUnion_accumulate
    -- We use the fact that we already know this is true for finite measures. As `⋃ n, T n = X`,
    -- we have that `μ ((T n) ∩ s) ⟶ μ s`.
    have mono : Monotone (fun n ↦ (T n) ∩ s) := fun m n hmn ↦ inter_subset_inter_left s
        (biUnion_subset_biUnion_left fun k hkm ↦ Nat.le_trans hkm hmn)
    have := tendsto_measure_iUnion_atTop (μ := μ) mono
    rw [← tendsto_toReal_iff] at this
    · -- We can therefore choose `N` such that `μ s - μ ((S N) ∩ s) < ε/2`.
      rcases Metric.tendsto_atTop.1 this (ε / 2) (by linarith [ε_pos]) with ⟨N, hN⟩
      have : Fact (μ (T N) < ∞) := Fact.mk <| T_finite N
      -- Then we can apply the previous result to the measure `μ ((S N) ∩ •)`.
      -- There exists `t ∈ 𝒜` such that `μ ((S N) ∩ (s ∆ t)) < ε/2`.
      rcases (Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
        (μ.restrict (T N)) h𝒜 hgen).approx s ms
        (ne_of_lt (lt_of_le_of_lt (μ.restrict_apply_le _ s) hμs.lt_top))
        (ε / 2) (by linarith [ε_pos])
        with ⟨t, t_mem, ht⟩
      -- We can then use `t ∩ (S N)`, because `S N ∈ 𝒜` by hypothesis.
      -- `μ (s ∆ (t ∩ S N))`
      --   `≤ μ (s ∆ (s ∩ S N)) + μ ((s ∩ S N) ∆ (t ∩ S N))`
      --   `= μ s - μ (s ∩ S N) + μ (s ∆ t) ∩ S N) < ε`.
      refine ⟨t ∩ T N, h𝒜.inter_mem t_mem (T_mem N), ?_⟩
      calc
        μ (s ∆ (t ∩ T N))
          ≤ μ (s \ (s ∩ T N)) + μ ((s ∆ t) ∩ T N) := by
              rw [← symmDiff_of_le (inter_subset_left ..), symmDiff_comm _ s,
                inter_symmDiff_distrib_right]
              exact measure_symmDiff_le _ _ _
        _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
              apply ENNReal.add_lt_add
              · rw [measure_sdiff
                    (inter_subset_left ..)
                    (ms.inter (hgen ▸ measurableSet_generateFrom (T_mem N))).nullMeasurableSet
                    (ne_top_of_le_ne_top hμs (measure_mono (inter_subset_left ..))),
                  lt_ofReal_iff_toReal_lt (sub_ne_top hμs),
                  toReal_sub_of_le (measure_mono (inter_subset_left ..)) hμs]
                apply lt_of_le_of_lt (sub_le_dist ..)
                nth_rw 1 [← univ_inter s]
                rw [inter_comm s, dist_comm, ← T_spanning, iUnion_inter _ T]
                apply hN N (le_refl _)
              · rwa [← μ.restrict_apply' (hgen ▸ measurableSet_generateFrom (T_mem N))]
        _ = ENNReal.ofReal ε := by
              rw [← ofReal_add (by linarith [ε_pos]) (by linarith [ε_pos]), add_halves]
    · exact fun n ↦ ne_top_of_le_ne_top hμs (measure_mono (inter_subset_right ..))
    · exact ne_top_of_le_ne_top hμs
        (measure_mono (iUnion_subset (fun i ↦ inter_subset_right ..)))

end MeasureDense

section IsSeparable

/-! ### Definition of a separable measure space, sufficient condition -/

/-- A measure `μ` is separable if there exists a countable and measure-dense family of sets.

The term "separable" is justified by the fact that the definition translates to the usual notion
of separability in the metric space made by constant indicators equipped with the `Lᵖ` norm. -/
/-
**MeasureTheory.IsSeparable** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{X : Type u_1} → [m : MeasurableSpace X] → MeasureTheory.Measure X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is separable if there exists a countable and measure-dense family 
of sets.

The term "separable" is justified by the fact that the definition translates to 
the usual notion
of separability in the metric space made by constant indicators equipped with th
e `Lᵖ` norm.
-/
class IsSeparable (μ : Measure X) : Prop where
  exists_countable_measureDense : ∃ 𝒜, 𝒜.Countable ∧ μ.MeasureDense 𝒜

variable (μ)

/-- By definition, a separable measure admits a countable and measure-dense family of sets. -/
/-
**MeasureTheory.exists_countable_measureDense** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：exists_countable_measureDense [IsSeparable μ] : exists 𝒜, 𝒜.Countable ∧ μ.
MeasureDense 𝒜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsSeparable.exists_countable_measureDense`：∀ {X : Type u_1
} {m : MeasurableSpace X} {μ : MeasureTheory.Measure X} [self : MeasureTheory.Is
Separable μ],   ∃ 𝒜, 𝒜.Countable ∧ μ.MeasureD…

--- 原说明 ---
By definition, a separable measure admits a countable and measure-dense family o
f sets.
-/
theorem exists_countable_measureDense [IsSeparable μ] :
    ∃ 𝒜, 𝒜.Countable ∧ μ.MeasureDense 𝒜 :=
  IsSeparable.exists_countable_measureDense

/-- If a measurable space is countably generated and equipped with a `σ`-finite measure, then the
measure is separable. This is not an instance because it is used below to prove the more
general case where `μ` is s-finite. -/
/-
**MeasureTheory.isSeparable_of_sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：isSeparable_of_sigmaFinite [CountablyGenerated X] [SigmaFinite μ] : IsSepa
rable μ where exists_countable_measureDense
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasurableSpace.countable_countableGeneratingSet`：countable_countableGen
eratingSet [MeasurableSpace α] [h : CountablyGenerated α] : Set.Countable (count
ableGeneratingSet α)
· 使用引理 `MeasurableSpace.generateFrom_countableGeneratingSet`：generateFrom_counta
bleGeneratingSet [m : MeasurableSpace α] [h : CountablyGenerated α] : generateFr
om (countableGeneratingSet α) = m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.countable_union`：countable_union {s t : Set α} : (s union t).Countab
le ↔ s.Countable ∧ t.Countable
· 使用定理 `Set.countable_iff_exists_subset_range`：countable_iff_exists_subset_range
 [Nonempty α] {s : Set α} : s.Countable ↔ exists f : Nat -> α, s subseteq range 
f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.countable_generateSetAlgebra`：countable_generateSetAlgebra
 (h : 𝒜.Countable) : (generateSetAlgebra 𝒜).Countable
· 使用定理 `MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFin
ite`：∀ {X : Type u_1} [m : MeasurableSpace X] {μ : MeasureTheory.Measure X} {𝒜 :
 Set (Set X)},   MeasureTheory.IsSetAlgebra 𝒜 → ∀ (S : μ.FiniteSp…
· 使用定理 `MeasureTheory.isSetAlgebra_generateSetAlgebra`：isSetAlgebra_generateSetA
lgebra : IsSetAlgebra (generateSetAlgebra 𝒜) where empty_mem
· 使用定理 `MeasureTheory.self_subset_generateSetAlgebra`：self_subset_generateSetAlg
ebra : 𝒜 subseteq generateSetAlgebra 𝒜
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.finite`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : μ
.FiniteSpanningSetsIn C) (i : ℕ), μ (se…
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.spanning`：∀ {α : Type u_1} {m
0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self :
 μ.FiniteSpanningSetsIn C), ⋃ i, self.set…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.generateFrom_mono`：generateFrom_mono {s t : Set (Set α)}
 (h : s subseteq t) : generateFrom s <= generateFrom t
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.generateSetAlgebra_mono`：generateSetAlgebra_mono {ℬ : Set 
(Set α)} (h : 𝒜 subseteq ℬ) : generateSetAlgebra 𝒜 subseteq generateSetAlgebra ℬ
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.set_mem`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : 
μ.FiniteSpanningSetsIn C) (i : ℕ), self.…
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)

--- 原说明 ---
If a measurable space is countably generated and equipped with a `σ`-finite meas
ure, then the
measure is separable. This is not an instance because it is used below to prove 
the more
general case where `μ` is s-finite.
-/
theorem isSeparable_of_sigmaFinite [CountablyGenerated X] [SigmaFinite μ] :
    IsSeparable μ where
  exists_countable_measureDense := by
    have h := countable_countableGeneratingSet (α := X)
    have hgen := generateFrom_countableGeneratingSet (α := X)
    let 𝒜 := (countableGeneratingSet X) ∪ {μ.toFiniteSpanningSetsIn.set n | n : ℕ}
    have count_𝒜 : 𝒜.Countable :=
      countable_union.2 ⟨h, countable_iff_exists_subset_range.2
        ⟨μ.toFiniteSpanningSetsIn.set, fun _ hx ↦ hx⟩⟩
    refine ⟨generateSetAlgebra 𝒜, countable_generateSetAlgebra count_𝒜,
      Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite isSetAlgebra_generateSetAlgebra
      { set := μ.toFiniteSpanningSetsIn.set
        set_mem := fun n ↦ self_subset_generateSetAlgebra (𝒜 := 𝒜) <| Or.inr ⟨n, rfl⟩
        finite := μ.toFiniteSpanningSetsIn.finite
        spanning := μ.toFiniteSpanningSetsIn.spanning }
      (le_antisymm ?_ (generateFrom_le (fun s hs ↦ ?_)))⟩
    · rw [← hgen]
      exact generateFrom_mono <| le_trans self_subset_generateSetAlgebra <|
        generateSetAlgebra_mono <| subset_union_left ..
    · induction hs with
      | base t t_mem =>
        rcases t_mem with t_mem | ⟨n, rfl⟩
        · exact hgen ▸ measurableSet_generateFrom t_mem
        · exact μ.toFiniteSpanningSetsIn.set_mem n
      | empty => exact MeasurableSet.empty
      | compl t _ t_mem => exact MeasurableSet.compl t_mem
      | union t u _ _ t_mem u_mem => exact MeasurableSet.union t_mem u_mem

/-- If a measurable space is countably generated and equipped with an s-finite measure, then the
measure is separable. -/
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a measurable space is countably generated and equipped with an s-finite measu
re, then the
measure is separable.
-/
instance [CountablyGenerated X] [SFinite μ] : IsSeparable μ where
  exists_countable_measureDense := by
    have := isSeparable_of_sigmaFinite (μ.restrict μ.sigmaFiniteSet)
    rcases exists_countable_measureDense (μ.restrict μ.sigmaFiniteSet) with ⟨𝒜, count_𝒜, h𝒜⟩
    let ℬ := {s ∩ μ.sigmaFiniteSet | s ∈ 𝒜}
    refine ⟨ℬ, count_𝒜.image (fun s ↦ s ∩ μ.sigmaFiniteSet), ?_, ?_⟩
    · rintro - ⟨s, s_mem, rfl⟩
      exact (h𝒜.measurable s s_mem).inter measurableSet_sigmaFiniteSet
    · intro s ms hμs ε ε_pos
      rcases restrict_compl_sigmaFiniteSet_eq_zero_or_top μ s with hs | hs
      · have : (μ.restrict μ.sigmaFiniteSet) s ≠ ∞ :=
          ne_top_of_le_ne_top hμs <| μ.restrict_le_self _
        rcases h𝒜.approx s ms this ε ε_pos with ⟨t, t_mem, ht⟩
        refine ⟨t ∩ μ.sigmaFiniteSet, ⟨t, t_mem, rfl⟩, ?_⟩
        have : μ (s ∆ (t ∩ μ.sigmaFiniteSet) \ μ.sigmaFiniteSet) = 0 := by
          rw [sdiff_eq_compl_inter, inter_symmDiff_distrib_left, ← ENNReal.bot_eq_zero, eq_bot_iff]
          calc
            μ ((μ.sigmaFiniteSetᶜ ∩ s) ∆ (μ.sigmaFiniteSetᶜ ∩ (t ∩ μ.sigmaFiniteSet)))
              ≤ μ ((μ.sigmaFiniteSetᶜ ∩ s) ∪ (μ.sigmaFiniteSetᶜ ∩ (t ∩ μ.sigmaFiniteSet))) :=
                measure_mono symmDiff_subset_union
            _ ≤ μ (μ.sigmaFiniteSetᶜ ∩ s) + μ (μ.sigmaFiniteSetᶜ ∩ (t ∩ μ.sigmaFiniteSet)) :=
                measure_union_le _ _
            _ = 0 := by
                rw [inter_comm, ← μ.restrict_apply ms, hs, ← inter_assoc, inter_comm,
                  ← inter_assoc, inter_compl_self, empty_inter, measure_empty, zero_add]
        rwa [← measure_inter_add_sdiff _ measurableSet_sigmaFiniteSet, this, add_zero,
          inter_symmDiff_distrib_right, inter_assoc, inter_self, ← inter_symmDiff_distrib_right,
          ← μ.restrict_apply' measurableSet_sigmaFiniteSet]
      · refine False.elim <| hμs ?_
        rw [eq_top_iff, ← hs]
        exact μ.restrict_le_self _
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hμ : IsSeparable μ] : IsSeparable μ.completion := by
  obtain ⟨𝒜, count_𝒜, h𝒜⟩ := exists_countable_measureDense μ
  exact ⟨𝒜, count_𝒜, h𝒜.completion⟩

end IsSeparable

section SecondCountableLp

/-! ### A sufficient condition for $L^p$ spaces to be second-countable -/

/-- If the measure `μ` is separable (in particular if `X` is countably generated and `μ` is
`s`-finite), if `E` is a second-countable `NormedAddCommGroup`, and if `1 ≤ p < +∞`,
then the associated `Lᵖ` space is second-countable. -/
/-
**MeasureTheory.Lp.SecondCountableTopology** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Lp`。
形式化陈述：∀ {X : Type u_1} {E : Type u_2} [m : MeasurableSpace X] [inst : NormedAddC
ommGroup E] {μ : MeasureTheory.Measure X}   {p : ENNReal} [one_le_p : Fact (1 ≤ 
p)] [p_ne_top : Fact (p ≠ ⊤)] [MeasureTheory.IsSeparable μ]   [TopologicalSpace.
SeparableSpace E], SecondCountableTopology ↥(MeasureTheory.Lp E p μ)
参数：1 ≤ p；p ≠ ⊤；MeasureTheory.Lp E p μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `MeasureTheory.exists_countable_measureDense`：exists_countable_measureDen
se [IsSeparable μ] : exists 𝒜, 𝒜.Countable ∧ μ.MeasureDense 𝒜
· 使用定理 `MeasureTheory.Measure.MeasureDense.fin_meas`：∀ {X : Type u_1} [m : Measu
rableSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.MeasureDense 
𝒜 → μ.MeasureDense {s | s ∈ 𝒜 ∧ μ…
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `TopologicalSpace.exists_countable_dense`：exists_countable_dense [Separab
leSpace α] : exists s : Set α, s.Countable ∧ Dense s
· 使用定理 `MeasureTheory.Measure.MeasureDense.measurable`：∀ {X : Type u_1} [m : Mea
surableSpace X] {μ : MeasureTheory.Measure X} {𝒜 : Set (Set X)},   μ.MeasureDens
e 𝒜 → ∀ s ∈ 𝒜, MeasurableSet s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableSigma`：∀ {α : Type u} {π : α → Type w} [Countable α] [∀ (a 
: α), Countable (π a)], Countable (Sigma π)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `instCountableForallOfFinite`：∀ {α : Sort u} {π : α → Sort w} [Finite α] 
[∀ (a : α), Countable (π a)], Countable ((a : α) → π a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Lp.induction`：∀ {α : Type u_1} {E : Type u_4} [inst : Meas
urableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheor
y.Measure α} [_i…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `SeminormedAddCommGroup.mem_closure_iff`：∀ {E : Type u_4} [inst : Seminor
medAddCommGroup E] {a : E} {s : Set E},   a ∈ closure s ↔ ∀ (ε : ℝ), 0 < ε → ∃ b
 ∈ s, ‖a - b‖ < ε
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
（共 150 条，此处仅展示前 30 条）

--- 原说明 ---
If the measure `μ` is separable (in particular if `X` is countably generated and
 `μ` is
`s`-finite), if `E` is a second-countable `NormedAddCommGroup`, and if `1 ≤ p < 
+∞`,
then the associated `Lᵖ` space is second-countable.
-/
instance Lp.SecondCountableTopology [IsSeparable μ] [TopologicalSpace.SeparableSpace E] :
    SecondCountableTopology (Lp E p μ) := by
  -- It is enough to show that the space is separable, i.e. admits a countable and dense subset.
  refine @UniformSpace.secondCountable_of_separable _ _ _ ?_
  -- There exists a countable and measure-dense family, and we can keep only the sets with finite
  -- measure while preserving the two properties. This family is denoted `𝒜₀`.
  rcases exists_countable_measureDense μ with ⟨𝒜, count_𝒜, h𝒜⟩
  have h𝒜₀ := Measure.MeasureDense.fin_meas h𝒜
  set 𝒜₀ := {s | s ∈ 𝒜 ∧ μ s ≠ ∞}
  have count_𝒜₀ : 𝒜₀.Countable := count_𝒜.mono fun _ ⟨h, _⟩ ↦ h
  -- `1 ≤ p` so `p ≠ 0`, we prove it now as it is often needed.
  have p_ne_zero : p ≠ 0 := ne_of_gt <| lt_of_lt_of_le (by simp) one_le_p.elim
  -- `E` is second-countable, therefore separable and admits a countable and dense subset `u`.
  rcases exists_countable_dense E with ⟨u, countable_u, dense_u⟩
  -- The countable and dense subset of `Lᵖ` we are going to build is the set of finite sums of
  -- constant indicators with support in `𝒜₀`, and is denoted `D`. To make manipulations easier,
  -- we define the function `key` which given an integer `n` and two families of `n` elements
  -- in `u` and `𝒜₀` associates the corresponding sum.
  let key (n : ℕ) (d : Fin n → u) (s : Fin n → 𝒜₀) : (Lp E p μ) :=
    ∑ i, indicatorConstLp p (h𝒜₀.measurable (s i) (Subtype.mem (s i))) (s i).2.2 (d i : E)
  let D := {s : Lp E p μ | ∃ n d t, s = key n d t}
  refine ⟨D, ?_, ?_⟩
  · -- Countability directly follows from countability of `u` and `𝒜₀`. The function `f` below
    -- is the uncurried version of `key`, which is easier to manipulate as countability of the
    -- domain is automatically inferred.
    let f (nds : Σ n : ℕ, (Fin n → u) × (Fin n → 𝒜₀)) : Lp E p μ := key nds.1 nds.2.1 nds.2.2
    have := count_𝒜₀.to_subtype
    have := countable_u.to_subtype
    have : D ⊆ range f := by
      rintro - ⟨n, d, s, rfl⟩
      use ⟨n, (d, s)⟩
    exact (countable_range f).mono this
  · -- Let's turn to the density. Thanks to the density of simple functions in `Lᵖ`, it is enough
    -- to show that the closure of `D` contains constant indicators which are in `Lᵖ` (i. e. the
    -- set has finite measure), is closed by sum and closed.
    -- This is given by `Lp.induction`.
    refine Lp.induction p_ne_top.elim (motive := fun f ↦ f ∈ closure D) ?_ ?_ isClosed_closure
    · intro a s ms hμs
      -- We want to approximate `a • 𝟙ₛ`.
      apply ne_of_lt at hμs
      rw [SeminormedAddCommGroup.mem_closure_iff]
      intro ε ε_pos
      have μs_pow_nonneg : 0 ≤ μ.real s ^ (1 / p.toReal) := by positivity
      -- To do so, we first pick `b ∈ u` such that `‖a - b‖ < ε / (3 * (1 + (μ s)^(1/p)))`.
      have approx_a_pos : 0 < ε / (3 * (1 + μ.real s ^ (1 / p.toReal))) :=
        div_pos ε_pos (by linarith [μs_pow_nonneg])
      have ⟨b, b_mem, hb⟩ := SeminormedAddCommGroup.mem_closure_iff.1 (dense_u a) _ approx_a_pos
      -- Then we pick `t ∈ 𝒜₀` such that `‖b • 𝟙ₛ - b • 𝟙ₜ‖ < ε / 3`.
      rcases SeminormedAddCommGroup.mem_closure_iff.1
        (h𝒜₀.indicatorConstLp_subset_closure p b ⟨s, ms, hμs, rfl⟩)
          (ε / 3) (by linarith [ε_pos]) with ⟨-, ⟨t, ht, hμt, rfl⟩, hst⟩
      have mt := h𝒜₀.measurable t ht
      -- We now show that `‖a • 𝟙ₛ - b • 𝟙ₜ‖ₚ < ε`, as follows:
      -- `‖a • 𝟙ₛ - b • 𝟙ₜ‖ₚ`
      --   `= ‖a • 𝟙ₛ - b • 𝟙ₛ + b • 𝟙ₛ - b • 𝟙ₜ‖ₚ`
      --   `≤ ‖a - b‖ * ‖𝟙ₛ‖ₚ + ε / 3`
      --   `= ‖a - b‖ * (μ s)^(1/p) + ε / 3`
      --   `< ε * (μ s)^(1/p) / (3 * (1 + (μ s)^(1/p))) + ε / 3`
      --   `≤ ε / 3 + ε / 3 < ε`.
      refine ⟨indicatorConstLp p mt hμt b,
        ⟨1, fun _ ↦ ⟨b, b_mem⟩, fun _ ↦ ⟨t, ht⟩, by simp [key]⟩, ?_⟩
      rw [Lp.simpleFunc.coe_indicatorConst,
        ← sub_add_sub_cancel _ (indicatorConstLp p ms hμs b), ← add_halves ε]
      refine lt_of_le_of_lt (b := ε / 3 + ε / 3) (norm_add_le_of_le ?_ hst.le) (by linarith [ε_pos])
      rw [indicatorConstLp_sub, norm_indicatorConstLp p_ne_zero p_ne_top.elim]
      calc
        ‖a - b‖ * μ.real s ^ (1 / p.toReal)
          ≤ (ε / (3 * (1 + μ.real s ^ (1 / p.toReal)))) * μ.real s ^ (1 / p.toReal) :=
              mul_le_mul_of_nonneg_right (le_of_lt hb) μs_pow_nonneg
        _ ≤ ε / 3 := by
            rw [← mul_one (ε / 3), div_mul_eq_div_mul_one_div, mul_assoc, one_div_mul_eq_div]
            exact mul_le_mul_of_nonneg_left
              ((div_le_one (by linarith [μs_pow_nonneg])).2 (by linarith))
              (by linarith [ε_pos])
    · -- Now we have to show that the closure of `D` is closed by sum. Let `f` and `g` be two
      -- functions in `Lᵖ` which are also in the closure of `D`.
      rintro f g hf hg - f_mem g_mem
      rw [SeminormedAddCommGroup.mem_closure_iff] at *
      intro ε ε_pos
      -- For `ε > 0`, there exists `bf, bg ∈ D` such that `‖f - bf‖ₚ < ε/2` and `‖g - bg‖ₚ < ε/2`.
      rcases f_mem (ε / 2) (by linarith [ε_pos]) with ⟨bf, ⟨nf, df, sf, bf_eq⟩, hbf⟩
      rcases g_mem (ε / 2) (by linarith [ε_pos]) with ⟨bg, ⟨ng, dg, sg, bg_eq⟩, hbg⟩
      -- It is obvious that `D` is closed by sum, it suffices to concatenate the family of
      -- elements of `u` and the family of elements of `𝒜₀`.
      let d := fun i : Fin (nf + ng) ↦ if h : i < nf
        then df (Fin.castLT i h)
        else dg (Fin.subNat nf (Fin.cast (Nat.add_comm ..) i) (le_of_not_gt h))
      let s := fun i : Fin (nf + ng) ↦ if h : i < nf
        then sf (Fin.castLT i h)
        else sg (Fin.subNat nf (Fin.cast (Nat.add_comm ..) i) (le_of_not_gt h))
      -- So we can use `bf + bg`.
      refine ⟨bf + bg, ⟨nf + ng, d, s, ?_⟩, ?_⟩
      · simp [key, d, s, Fin.sum_univ_add, bf_eq, bg_eq]
      · -- We have
        -- `‖f + g - (bf + bg)‖ₚ`
        --   `≤ ‖f - bf‖ₚ + ‖g - bg‖ₚ`
        --   `< ε/2 + ε/2 = ε`.
        calc
          ‖MemLp.toLp f hf + MemLp.toLp g hg - (bf + bg)‖
            = ‖(MemLp.toLp f hf) - bf + ((MemLp.toLp g hg) - bg)‖ := by congr; abel
          _ ≤ ‖(MemLp.toLp f hf) - bf‖ + ‖(MemLp.toLp g hg) - bg‖ := norm_add_le ..
          _ < ε := by linarith [hbf, hbg]

end SecondCountableLp

end MeasureTheory

