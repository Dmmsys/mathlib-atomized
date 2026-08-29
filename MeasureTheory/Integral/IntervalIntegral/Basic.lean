/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Topology
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Integral over an interval

In this file we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ` if `a ≤ b` and
`-∫ x in Ioc b a, f x ∂μ` if `b ≤ a`.

## Implementation notes

### Avoiding `if`, `min`, and `max`

In order to avoid `if`s in the definition, we define `IntervalIntegrable f μ a b` as
`IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ`. For any `a`, `b` one of these
intervals is empty and the other coincides with `Set.uIoc a b = Set.Ioc (min a b) (max a b)`.

Similarly, we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
Again, for any `a`, `b` one of these integrals is zero, and the other gives the expected result.

This way some properties can be translated from integrals over sets without dealing with
the cases `a ≤ b` and `b ≤ a` separately.

### Choice of the interval

We use integral over `Set.uIoc a b = Set.Ioc (min a b) (max a b)` instead of one of the other
three possible intervals with the same endpoints for two reasons:

* this way `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ` holds whenever
  `f` is integrable on each interval; in particular, it works even if the measure `μ` has an atom
  at `b`; this rules out `Set.Ioo` and `Set.Icc` intervals;
* with this definition for a probability measure `μ`, the integral `∫ x in a..b, 1 ∂μ` equals
  the difference $F_μ(b)-F_μ(a)$, where $F_μ(a)=μ(-∞, a]$ is the
  [cumulative distribution function](https://en.wikipedia.org/wiki/Cumulative_distribution_function)
  of `μ`.

## Tags

integral
-/

@[expose] public section


noncomputable section

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {ι 𝕜 ε ε' E F A : Type*} [NormedAddCommGroup E]
  [TopologicalSpace ε] [ENormedAddMonoid ε] [TopologicalSpace ε'] [ENormedAddMonoid ε']

/-!
### Integrability on an interval
-/


/--
Definition of `IntervalIntegrable` / `IntervalIntegrable` 的定义

English:
definition IntervalIntegrable
  signature: (f : Real -> ε) (μ : Measure Real) (a b : Real)
  body: IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ

中文:
定义 IntervalIntegrable
  签名: (f : 实数 -> ε) (μ : Measure 实数) (a b : 实数)
  定义体: IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ

Depends on / 依赖: IntegrableOn
-/
def IntervalIntegrable (f : Real -> ε) (μ : Measure Real) (a b : Real) : Prop :=
  IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ

/-!
## Basic iff's for `IntervalIntegrable`
-/
section

variable [PseudoMetrizableSpace ε] {f : Real -> ε} {a b : Real} {μ : Measure Real}

/--
theorem `intervalIntegrable_iff` / 定理 `intervalIntegrable_iff`

English:
theorem intervalIntegrable_iff
  statement: IntervalIntegrable f μ a b ↔ IntegrableOn f (Ι a b) μ
  proof: by
  rw [uIoc_eq_union]; rw [integrableOn_union]; rw [IntervalIntegrable]

中文:
定理 intervalIntegrable_iff
  结论: 整数erval整数egrable f μ a b ↔ 整数egrableOn f (Ι a b) μ
  证明: by
  rw [uIoc_eq_union]; rw [integrableOn_union]; rw [IntervalIntegrable]

Depends on / 依赖: IntervalIntegrable, integrableOn_union, uIoc_eq_union
-/
theorem intervalIntegrable_iff : IntervalIntegrable f μ a b ↔ IntegrableOn f (Ι a b) μ := by
  rw [uIoc_eq_union]; rw [integrableOn_union]; rw [IntervalIntegrable]

/--
theorem `IntervalIntegrable.def'` / 定理 `IntervalIntegrable.def'`

English:
theorem IntervalIntegrable.def'
  given: (h : IntervalIntegrable f μ a b)
  statement: IntegrableOn f (Ι a b) μ
  proof: intervalIntegrable_iff.mp h

中文:
定理 IntervalIntegrable.def'
  条件: (h : 整数erval整数egrable f μ a b)
  结论: 整数egrableOn f (Ι a b) μ
  证明: intervalIntegrable_iff.mp h

Depends on / 依赖: intervalIntegrable_iff, intervalIntegrable_iff.mp
-/
theorem IntervalIntegrable.def' (h : IntervalIntegrable f μ a b) : IntegrableOn f (Ι a b) μ :=
  intervalIntegrable_iff.mp h

/--
theorem `intervalIntegrable_congr_ae` / 定理 `intervalIntegrable_congr_ae`

English:
theorem intervalIntegrable_congr_ae
  given: {g : Real -> ε} (h : f =ᵐ[μ.restrict (Ι a b)] g)
  proof: by
  rw [intervalIntegrable_iff]; rw [integrableOn_congr_fun_ae h]; rw [intervalIntegrable_iff]

中文:
定理 intervalIntegrable_congr_ae
  条件: {g : 实数 -> ε} (h : f =ᵐ[μ.restrict (Ι a b)] g)
  证明: by
  rw [intervalIntegrable_iff]; rw [integrableOn_congr_fun_ae h]; rw [intervalIntegrable_iff]

Depends on / 依赖: integrableOn_congr_fun_ae, intervalIntegrable_iff
-/
theorem intervalIntegrable_congr_ae {g : Real -> ε} (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b := by
  rw [intervalIntegrable_iff]; rw [integrableOn_congr_fun_ae h]; rw [intervalIntegrable_iff]

/--
theorem `intervalIntegrable_congr_uIoo` / 定理 `intervalIntegrable_congr_uIoo`

English:
theorem intervalIntegrable_congr_uIoo
  given: [NullSingletonClass μ] {g : Real -> ε} (h : EqOn f g (uIoo a b))
  proof: by
  apply intervalIntegrable_congr_ae
  rw [uIoc]; rw [← restrict_Ioo_eq_restrict_Ioc]
  apply ae_restrict_of_forall_mem measurableSet_Ioo h

中文:
定理 intervalIntegrable_congr_uIoo
  条件: [NullSingletonClass μ] {g : 实数 -> ε} (h : EqOn f g (uIoo a b))
  证明: by
  apply intervalIntegrable_congr_ae
  rw [uIoc]; rw [← restrict_Ioo_eq_restrict_Ioc]
  apply ae_restrict_of_forall_mem measurableSet_Ioo h

Depends on / 依赖: ae_restrict_of_forall_mem, intervalIntegrable_congr_ae, measurableSet_Ioo, restrict_Ioo_eq_restrict_Ioc
-/
theorem intervalIntegrable_congr_uIoo [NullSingletonClass μ] {g : Real -> ε} (h : EqOn f g (uIoo a b)) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b := by
  apply intervalIntegrable_congr_ae
  rw [uIoc]; rw [← restrict_Ioo_eq_restrict_Ioc]
  apply ae_restrict_of_forall_mem measurableSet_Ioo h

/--
theorem `IntervalIntegrable.congr_ae` / 定理 `IntervalIntegrable.congr_ae`

English:
theorem IntervalIntegrable.congr_ae
  statement: {g : Real -> ε} (hf : IntervalIntegrable f μ a b)
  proof: by
  rwa [← intervalIntegrable_congr_ae h]

中文:
定理 IntervalIntegrable.congr_ae
  结论: {g : 实数 -> ε} (hf : 整数erval整数egrable f μ a b)
  证明: by
  rwa [← intervalIntegrable_congr_ae h]

Depends on / 依赖: intervalIntegrable_congr_ae
-/
theorem IntervalIntegrable.congr_ae {g : Real -> ε} (hf : IntervalIntegrable f μ a b)
    (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    IntervalIntegrable g μ a b := by
  rwa [← intervalIntegrable_congr_ae h]

/--
theorem `IntervalIntegrable.congr_uIoo` / 定理 `IntervalIntegrable.congr_uIoo`

English:
theorem IntervalIntegrable.congr_uIoo
  statement: [NullSingletonClass μ] {g : Real -> ε}
  proof: .mp hf intervalIntegrable_congr_uIoo h

中文:
定理 IntervalIntegrable.congr_uIoo
  结论: [NullSingletonClass μ] {g : 实数 -> ε}
  证明: .mp hf intervalIntegrable_congr_uIoo h

Depends on / 依赖: intervalIntegrable_congr_uIoo
-/
theorem IntervalIntegrable.congr_uIoo [NullSingletonClass μ] {g : Real -> ε}
    (hf : IntervalIntegrable f μ a b) (h : EqOn f g (uIoo a b)) : IntervalIntegrable g μ a b :=
.mp hf intervalIntegrable_congr_uIoo h

/--
theorem `intervalIntegrable_congr` / 定理 `intervalIntegrable_congr`

English:
theorem intervalIntegrable_congr
  given: {g : Real -> ε} (h : EqOn f g (Ι a b))
  proof: intervalIntegrable_congr_ae (ae_restrict_mem measurableSet_uIoc).mono h

alias ⟨IntervalIntegrable.congr, _⟩ := intervalIntegrable_congr

中文:
定理 intervalIntegrable_congr
  条件: {g : 实数 -> ε} (h : EqOn f g (Ι a b))
  证明: intervalIntegrable_congr_ae (ae_restrict_mem measurableSet_uIoc).mono h

alias ⟨IntervalIntegrable.congr, _⟩ := intervalIntegrable_congr

Depends on / 依赖: ae_restrict_mem, intervalIntegrable_congr_ae, measurableSet_uIoc
-/
theorem intervalIntegrable_congr {g : Real -> ε} (h : EqOn f g (Ι a b)) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b :=
intervalIntegrable_congr_ae (ae_restrict_mem measurableSet_uIoc).mono h

alias ⟨IntervalIntegrable.congr, _⟩ := intervalIntegrable_congr

/--
theorem `IntervalIntegrable.congr_codiscreteWithin` / 定理 `IntervalIntegrable.congr_codiscreteWithin`

English:
theorem IntervalIntegrable.congr_codiscreteWithin
  statement: {g : Real -> ε} [NullSingletonClass μ]
  proof: hf.congr_ae (ae_restrict_le_codiscreteWithin measurableSet_Ioc h)

中文:
定理 IntervalIntegrable.congr_codiscreteWithin
  结论: {g : 实数 -> ε} [NullSingletonClass μ]
  证明: hf.congr_ae (ae_restrict_le_codiscreteWithin measurableSet_Ioc h)

Depends on / 依赖: ae_restrict_le_codiscreteWithin, congr_ae, hf.congr_ae, measurableSet_Ioc
-/
theorem IntervalIntegrable.congr_codiscreteWithin {g : Real -> ε} [NullSingletonClass μ]
    (h : f =ᶠ[codiscreteWithin (Ι a b)] g) (hf : IntervalIntegrable f μ a b) :
    IntervalIntegrable g μ a b :=
  hf.congr_ae (ae_restrict_le_codiscreteWithin measurableSet_Ioc h)

/--
theorem `intervalIntegrable_congr_codiscreteWithin` / 定理 `intervalIntegrable_congr_codiscreteWithin`

English:
theorem intervalIntegrable_congr_codiscreteWithin
  statement: {g : Real -> ε} [NullSingletonClass μ]
  proof: ⟨(IntervalIntegrable.congr_codiscreteWithin h ·),
    (IntervalIntegrable.congr_codiscreteWithin h.symm ·)⟩

中文:
定理 intervalIntegrable_congr_codiscreteWithin
  结论: {g : 实数 -> ε} [NullSingletonClass μ]
  证明: ⟨(IntervalIntegrable.congr_codiscreteWithin h ·),
    (IntervalIntegrable.congr_codiscreteWithin h.symm ·)⟩

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.congr_codiscreteWithin, congr_codiscreteWithin, h.symm
-/
theorem intervalIntegrable_congr_codiscreteWithin {g : Real -> ε} [NullSingletonClass μ]
    (h : f =ᶠ[codiscreteWithin (Ι a b)] g) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b :=
  ⟨(IntervalIntegrable.congr_codiscreteWithin h ·),
    (IntervalIntegrable.congr_codiscreteWithin h.symm ·)⟩

/--
theorem `intervalIntegrable_iff_integrableOn_Ioc_of_le` / 定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`

English:
theorem intervalIntegrable_iff_integrableOn_Ioc_of_le
  given: (hab : a <= b)
  proof: by
  rw [intervalIntegrable_iff]; rw [uIoc_of_le hab]

中文:
定理 intervalIntegrable_iff_integrableOn_Ioc_of_le
  条件: (hab : a <= b)
  证明: by
  rw [intervalIntegrable_iff]; rw [uIoc_of_le hab]

Depends on / 依赖: intervalIntegrable_iff, uIoc_of_le
-/
theorem intervalIntegrable_iff_integrableOn_Ioc_of_le (hab : a <= b) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioc a b) μ := by
  rw [intervalIntegrable_iff]; rw [uIoc_of_le hab]

/--
theorem `intervalIntegrable_iff'` / 定理 `intervalIntegrable_iff'`

English:
theorem intervalIntegrable_iff'
  given: [NullSingletonClass μ] (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
  proof: by
  rw [intervalIntegrable_iff]; rw [← Icc_min_max]; rw [uIoc]; rw [integrableOn_Icc_iff_integrableOn_Ioc h]

中文:
定理 intervalIntegrable_iff'
  条件: [NullSingletonClass μ] (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
  证明: by
  rw [intervalIntegrable_iff]; rw [← Icc_min_max]; rw [uIoc]; rw [integrableOn_Icc_iff_integrableOn_Ioc h]

Depends on / 依赖: Icc_min_max, IntegrableOn, IntervalIntegrable, finiteness, integrableOn_Icc_iff_integrableOn_Ioc, intervalIntegrable_iff
-/
theorem intervalIntegrable_iff' [NullSingletonClass μ] (h : ‖f (min a b)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (uIcc a b) μ := by
  rw [intervalIntegrable_iff]; rw [← Icc_min_max]; rw [uIoc]; rw [integrableOn_Icc_iff_integrableOn_Ioc h]

/--
theorem `intervalIntegrable_iff_integrableOn_Icc_of_le` / 定理 `intervalIntegrable_iff_integrableOn_Icc_of_le`

English:
theorem intervalIntegrable_iff_integrableOn_Icc_of_le
  statement: [NullSingletonClass μ]
  proof: by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]; rw [integrableOn_Icc_iff_integrableOn_Ioc ha]

中文:
定理 intervalIntegrable_iff_integrableOn_Icc_of_le
  结论: [NullSingletonClass μ]
  证明: by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]; rw [integrableOn_Icc_iff_integrableOn_Ioc ha]

Depends on / 依赖: IntegrableOn, IntervalIntegrable, finiteness, integrableOn_Icc_iff_integrableOn_Ioc, intervalIntegrable_iff_integrableOn_Ioc_of_le
-/
theorem intervalIntegrable_iff_integrableOn_Icc_of_le [NullSingletonClass μ]
    (hab : a <= b) (ha : ‖f a‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Icc a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]; rw [integrableOn_Icc_iff_integrableOn_Ioc ha]

/--
theorem `intervalIntegrable_iff_integrableOn_Ico_of_le` / 定理 `intervalIntegrable_iff_integrableOn_Ico_of_le`

English:
theorem intervalIntegrable_iff_integrableOn_Ico_of_le
  statement: [NullSingletonClass μ]
  proof: by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha]; rw [integrableOn_Icc_iff_integrableOn_Ico hb]

中文:
定理 intervalIntegrable_iff_integrableOn_Ico_of_le
  结论: [NullSingletonClass μ]
  证明: by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha]; rw [integrableOn_Icc_iff_integrableOn_Ico hb]

Depends on / 依赖: IntegrableOn, IntervalIntegrable, finiteness, integrableOn_Icc_iff_integrableOn_Ico, intervalIntegrable_iff_integrableOn_Icc_of_le
-/
theorem intervalIntegrable_iff_integrableOn_Ico_of_le [NullSingletonClass μ]
    (hab : a <= b) (ha : ‖f a‖ₑ != ∞ := by finiteness) (hb : ‖f b‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ico a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha]; rw [integrableOn_Icc_iff_integrableOn_Ico hb]

/--
theorem `intervalIntegrable_iff_integrableOn_Ioo_of_le` / 定理 `intervalIntegrable_iff_integrableOn_Ioo_of_le`

English:
theorem intervalIntegrable_iff_integrableOn_Ioo_of_le
  statement: [NullSingletonClass μ]
  proof: by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha]; rw [integrableOn_Icc_iff_integrableOn_Ioo ha hb]

omit [PseudoMetrizableSpace ε] in

中文:
定理 intervalIntegrable_iff_integrableOn_Ioo_of_le
  结论: [NullSingletonClass μ]
  证明: by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha]; rw [integrableOn_Icc_iff_integrableOn_Ioo ha hb]

omit [PseudoMetrizableSpace ε] in

Depends on / 依赖: IntegrableOn, IntervalIntegrable, finiteness, integrableOn_Icc_iff_integrableOn_Ioo, intervalIntegrable_iff_integrableOn_Icc_of_le
-/
theorem intervalIntegrable_iff_integrableOn_Ioo_of_le [NullSingletonClass μ]
    (hab : a <= b) (ha : ‖f a‖ₑ != ∞ := by finiteness) (hb : ‖f b‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioo a b) μ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab ha]; rw [integrableOn_Icc_iff_integrableOn_Ioo ha hb]

omit [PseudoMetrizableSpace ε] in
/--
theorem `MeasureTheory.Integrable.intervalIntegrable` / 定理 `MeasureTheory.Integrable.intervalIntegrable`

English:
theorem MeasureTheory.Integrable.intervalIntegrable
  given: (hf : Integrable f μ)
  proof: ⟨hf.integrableOn, hf.integrableOn⟩

omit [PseudoMetrizableSpace ε] in

中文:
定理 MeasureTheory.Integrable.intervalIntegrable
  条件: (hf : 整数egrable f μ)
  证明: ⟨hf.integrableOn, hf.integrableOn⟩

omit [PseudoMetrizableSpace ε] in

Depends on / 依赖: hf.integrableOn, integrableOn
-/
theorem MeasureTheory.Integrable.intervalIntegrable (hf : Integrable f μ) :
    IntervalIntegrable f μ a b :=
  ⟨hf.integrableOn, hf.integrableOn⟩

omit [PseudoMetrizableSpace ε] in
/--
theorem `MeasureTheory.IntegrableOn.intervalIntegrable` / 定理 `MeasureTheory.IntegrableOn.intervalIntegrable`

English:
theorem MeasureTheory.IntegrableOn.intervalIntegrable
  given: (hf : IntegrableOn f [[a, b]] μ)
  proof: ⟨hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc),
    hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc')⟩

中文:
定理 MeasureTheory.IntegrableOn.intervalIntegrable
  条件: (hf : 整数egrableOn f [[a, b]] μ)
  证明: ⟨hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc),
    hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc')⟩

Depends on / 依赖: Icc_subset_uIcc, Ioc_subset_Icc_self, Ioc_subset_Icc_self.trans, hf.mono_set, mono_set
-/
theorem MeasureTheory.IntegrableOn.intervalIntegrable (hf : IntegrableOn f [[a, b]] μ) :
    IntervalIntegrable f μ a b :=
  ⟨hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc),
    hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc')⟩

/--
theorem `intervalIntegrable_const_iff` / 定理 `intervalIntegrable_const_iff`

English:
theorem intervalIntegrable_const_iff
  given: {c : ε} (hc : ‖c‖ₑ != ⊤ := by finiteness)
  proof: by
  simp [intervalIntegrable_iff, integrableOn_const_iff hc]

@[simp]

中文:
定理 intervalIntegrable_const_iff
  条件: {c : ε} (hc : ‖c‖ₑ != ⊤ := by finiteness)
  证明: by
  simp [intervalIntegrable_iff, integrableOn_const_iff hc]

@[simp]

Depends on / 依赖: IntervalIntegrable, finiteness, integrableOn_const_iff, intervalIntegrable_iff
-/
theorem intervalIntegrable_const_iff {c : ε} (hc : ‖c‖ₑ != ⊤ := by finiteness) :
    IntervalIntegrable (fun _ => c) μ a b ↔ c = 0 ∨ μ (Ι a b) < ∞ := by
  simp [intervalIntegrable_iff, integrableOn_const_iff hc]

@[simp]
/--
theorem `intervalIntegrable_const` / 定理 `intervalIntegrable_const`

English:
theorem intervalIntegrable_const
  given: [IsLocallyFiniteMeasure μ] {c : E}
  proof: .2 Or.inr measure_Ioc_lt_top intervalIntegrable_const_iff (by simp)

中文:
定理 intervalIntegrable_const
  条件: [IsLocallyFiniteMeasure μ] {c : E}
  证明: .2 Or.inr measure_Ioc_lt_top intervalIntegrable_const_iff (by simp)

Depends on / 依赖: Or.inr, intervalIntegrable_const_iff, measure_Ioc_lt_top
-/
theorem intervalIntegrable_const [IsLocallyFiniteMeasure μ] {c : E} :
    IntervalIntegrable (fun _ => c) μ a b :=
.2 Or.inr measure_Ioc_lt_top intervalIntegrable_const_iff (by simp)

/--
theorem `IntervalIntegrable.zero` / 定理 `IntervalIntegrable.zero`

English:
theorem IntervalIntegrable.zero
  statement: IntervalIntegrable (0 : Real -> E) μ a b
  proof: (intervalIntegrable_const_iff <| by finiteness).mpr .inl rfl

中文:
定理 IntervalIntegrable.zero
  结论: 整数erval整数egrable (0 : 实数 -> E) μ a b
  证明: (intervalIntegrable_const_iff <| by finiteness).mpr .inl rfl
-/
protected theorem IntervalIntegrable.zero : IntervalIntegrable (0 : Real -> E) μ a b :=
(intervalIntegrable_const_iff <| by finiteness).mpr .inl rfl

end

/-!
## Basic properties of interval integrability
- interval integrability is symmetric, reflexive, transitive
- monotonicity and strong measurability of the interval integral
- if `f` is interval integrable, so are its absolute value and norm
- arithmetic properties
-/
namespace IntervalIntegrable

section

variable {f : Real -> ε} {a b c d : Real} {μ ν : Measure Real}

@[symm]
nonrec theorem symm (h : IntervalIntegrable f μ a b) : IntervalIntegrable f μ b a :=
  h.symm

/--
theorem `symm_iff` / 定理 `symm_iff`

English:
theorem symm_iff
  statement: IntervalIntegrable f μ a b ↔ IntervalIntegrable f μ b a
  proof: ⟨.symm, .symm⟩

@[refl, simp]

中文:
定理 symm_iff
  结论: 整数erval整数egrable f μ a b ↔ 整数erval整数egrable f μ b a
  证明: ⟨.symm, .symm⟩

@[refl, simp]
-/
theorem symm_iff : IntervalIntegrable f μ a b ↔ IntervalIntegrable f μ b a := ⟨.symm, .symm⟩

@[refl, simp]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  statement: IntervalIntegrable f μ a a
  proof: by constructor <;> simp

中文:
定理 refl
  结论: 整数erval整数egrable f μ a a
  证明: by constructor <;> simp
-/
theorem refl : IntervalIntegrable f μ a a := by constructor <;> simp

variable [PseudoMetrizableSpace ε]

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: {a b c : Real} (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c)
  proof: ⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
    (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩

中文:
定理 trans
  条件: {a b c : 实数} (hab : 整数erval整数egrable f μ a b) (hbc : 整数erval整数egrable f μ b c)
  证明: ⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
    (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩

Depends on / 依赖: Ioc_subset_Ioc_union_Ioc, mono_set
-/
theorem trans {a b c : Real} (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) :
    IntervalIntegrable f μ a c :=
  ⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
    (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩

/--
theorem `trans_iff` / 定理 `trans_iff`

English:
theorem trans_iff
  given: (h : b in [[a, c]])
  proof: by
  simp only [intervalIntegrable_iff, ← integrableOn_union, uIoc_union_uIoc h]

中文:
定理 trans_iff
  条件: (h : b in [[a, c]])
  证明: by
  simp only [intervalIntegrable_iff, ← integrableOn_union, uIoc_union_uIoc h]

Depends on / 依赖: integrableOn_union, intervalIntegrable_iff, uIoc_union_uIoc
-/
theorem trans_iff (h : b in [[a, c]]) :
    IntervalIntegrable f μ a c ↔ IntervalIntegrable f μ a b ∧ IntervalIntegrable f μ b c := by
  simp only [intervalIntegrable_iff, ← integrableOn_union, uIoc_union_uIoc h]

/--
theorem `trans_iterate_Ico` / 定理 `trans_iterate_Ico`

English:
theorem trans_iterate_Ico
  statement: {a : Nat -> Real} {m n : Nat} (hmn : m <= n)
  proof: by
  revert hint
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro p hp IH h
    exact (IH fun k hk => h k (Ico_subset_Ico_right p.le_succ hk)).trans (h p (by simp [hp]))

中文:
定理 trans_iterate_Ico
  结论: {a : 自然数 -> 实数} {m n : 自然数} (hmn : m <= n)
  证明: by
  revert hint
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro p hp IH h
    exact (IH fun k hk => h k (Ico_subset_Ico_right p.le_succ hk)).trans (h p (by simp [hp]))

Depends on / 依赖: Ico_subset_Ico_right, Nat.le_induction, le_induction, le_succ, p.le_succ, revert
-/
theorem trans_iterate_Ico {a : Nat -> Real} {m n : Nat} (hmn : m <= n)
    (hint : forall k in Ico m n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    IntervalIntegrable f μ (a m) (a n) := by
  revert hint
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro p hp IH h
    exact (IH fun k hk => h k (Ico_subset_Ico_right p.le_succ hk)).trans (h p (by simp [hp]))

/--
theorem `trans_iterate` / 定理 `trans_iterate`

English:
theorem trans_iterate
  statement: {a : Nat -> Real} {n : Nat}
  proof: trans_iterate_Ico bot_le fun k hk => hint k hk.2

中文:
定理 trans_iterate
  结论: {a : 自然数 -> 实数} {n : 自然数}
  证明: trans_iterate_Ico bot_le fun k hk => hint k hk.2

Depends on / 依赖: bot_le, trans_iterate_Ico
-/
theorem trans_iterate {a : Nat -> Real} {n : Nat}
    (hint : forall k < n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    IntervalIntegrable f μ (a 0) (a n) :=
  trans_iterate_Ico bot_le fun k hk => hint k hk.2

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: {f : Real -> E} (h : IntervalIntegrable f μ a b)
  statement: IntervalIntegrable (-f) μ a b
  proof: ⟨h.1.neg, h.2.neg⟩

omit [PseudoMetrizableSpace ε] in

中文:
定理 neg
  条件: {f : 实数 -> E} (h : 整数erval整数egrable f μ a b)
  结论: 整数erval整数egrable (-f) μ a b
  证明: ⟨h.1.neg, h.2.neg⟩

omit [PseudoMetrizableSpace ε] in
-/
theorem neg {f : Real -> E} (h : IntervalIntegrable f μ a b) : IntervalIntegrable (-f) μ a b :=
  ⟨h.1.neg, h.2.neg⟩

omit [PseudoMetrizableSpace ε] in
/--
theorem `enorm` / 定理 `enorm`

English:
theorem enorm
  given: (h : IntervalIntegrable f μ a b)
  statement: IntervalIntegrable (‖f ·‖ₑ) μ a b
  proof: ⟨h.1.enorm, h.2.enorm⟩

中文:
定理 enorm
  条件: (h : 整数erval整数egrable f μ a b)
  结论: 整数erval整数egrable (‖f ·‖ₑ) μ a b
  证明: ⟨h.1.enorm, h.2.enorm⟩
-/
theorem enorm (h : IntervalIntegrable f μ a b) : IntervalIntegrable (‖f ·‖ₑ) μ a b :=
  ⟨h.1.enorm, h.2.enorm⟩

/--
theorem `norm` / 定理 `norm`

English:
theorem norm
  given: {f : Real -> E} (h : IntervalIntegrable f μ a b)
  statement: IntervalIntegrable (‖f ·‖) μ a b
  proof: ⟨h.1.norm, h.2.norm⟩

中文:
定理 norm
  条件: {f : 实数 -> E} (h : 整数erval整数egrable f μ a b)
  结论: 整数erval整数egrable (‖f ·‖) μ a b
  证明: ⟨h.1.norm, h.2.norm⟩
-/
theorem norm {f : Real -> E} (h : IntervalIntegrable f μ a b) : IntervalIntegrable (‖f ·‖) μ a b :=
  ⟨h.1.norm, h.2.norm⟩

/--
theorem `intervalIntegrable_enorm_iff` / 定理 `intervalIntegrable_enorm_iff`

English:
theorem intervalIntegrable_enorm_iff
  statement: {μ : Measure Real} {a b : Real}
  proof: by
  simp_rw [intervalIntegrable_iff, IntegrableOn, integrable_enorm_iff hf]

中文:
定理 intervalIntegrable_enorm_iff
  结论: {μ : Measure 实数} {a b : 实数}
  证明: by
  simp_rw [intervalIntegrable_iff, IntegrableOn, integrable_enorm_iff hf]

Depends on / 依赖: IntegrableOn, integrable_enorm_iff, intervalIntegrable_iff, simp_rw
-/
theorem intervalIntegrable_enorm_iff {μ : Measure Real} {a b : Real}
    (hf : AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    IntervalIntegrable (fun t => ‖f t‖ₑ) μ a b ↔ IntervalIntegrable f μ a b := by
  simp_rw [intervalIntegrable_iff, IntegrableOn, integrable_enorm_iff hf]

/--
theorem `intervalIntegrable_norm_iff` / 定理 `intervalIntegrable_norm_iff`

English:
theorem intervalIntegrable_norm_iff
  statement: {f : Real -> E} {μ : Measure Real} {a b : Real}
  proof: by
  simp_rw [intervalIntegrable_iff, IntegrableOn, integrable_norm_iff hf]

中文:
定理 intervalIntegrable_norm_iff
  结论: {f : 实数 -> E} {μ : Measure 实数} {a b : 实数}
  证明: by
  simp_rw [intervalIntegrable_iff, IntegrableOn, integrable_norm_iff hf]

Depends on / 依赖: IntegrableOn, integrable_norm_iff, intervalIntegrable_iff, simp_rw
-/
theorem intervalIntegrable_norm_iff {f : Real -> E} {μ : Measure Real} {a b : Real}
    (hf : AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    IntervalIntegrable (fun t => ‖f t‖) μ a b ↔ IntervalIntegrable f μ a b := by
  simp_rw [intervalIntegrable_iff, IntegrableOn, integrable_norm_iff hf]

/--
theorem `abs` / 定理 `abs`

English:
theorem abs
  given: {f : Real -> Real} (h : IntervalIntegrable f μ a b)
  proof: h.norm

中文:
定理 abs
  条件: {f : 实数 -> 实数} (h : 整数erval整数egrable f μ a b)
  证明: h.norm

Depends on / 依赖: h.norm
-/
theorem abs {f : Real -> Real} (h : IntervalIntegrable f μ a b) :
    IntervalIntegrable (fun x => |f x|) μ a b :=
  h.norm

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hf : IntervalIntegrable f ν a b) (h1 : [[c, d]] subseteq [[a, b]]) (h2 : μ <= ν)
  proof: intervalIntegrable_iff.mpr hf.def'.mono (uIoc_subset_uIoc_of_uIcc_subset_uIcc h1) h2

中文:
定理 mono
  条件: (hf : 整数erval整数egrable f ν a b) (h1 : [[c, d]] subseteq [[a, b]]) (h2 : μ <= ν)
  证明: intervalIntegrable_iff.mpr hf.def'.mono (uIoc_subset_uIoc_of_uIcc_subset_uIcc h1) h2

Depends on / 依赖: hf.def, intervalIntegrable_iff, intervalIntegrable_iff.mpr, uIoc_subset_uIoc_of_uIcc_subset_uIcc
-/
theorem mono (hf : IntervalIntegrable f ν a b) (h1 : [[c, d]] subseteq [[a, b]]) (h2 : μ <= ν) :
    IntervalIntegrable f μ c d :=
intervalIntegrable_iff.mpr hf.def'.mono (uIoc_subset_uIoc_of_uIcc_subset_uIcc h1) h2

/--
theorem `mono_measure` / 定理 `mono_measure`

English:
theorem mono_measure
  given: (hf : IntervalIntegrable f ν a b) (h : μ <= ν)
  statement: IntervalIntegrable f μ a b
  proof: hf.mono Subset.rfl h

中文:
定理 mono_measure
  条件: (hf : 整数erval整数egrable f ν a b) (h : μ <= ν)
  结论: 整数erval整数egrable f μ a b
  证明: hf.mono Subset.rfl h

Depends on / 依赖: Subset, Subset.rfl, hf.mono
-/
theorem mono_measure (hf : IntervalIntegrable f ν a b) (h : μ <= ν) : IntervalIntegrable f μ a b :=
  hf.mono Subset.rfl h

/--
theorem `mono_set` / 定理 `mono_set`

English:
theorem mono_set
  given: (hf : IntervalIntegrable f μ a b) (h : [[c, d]] subseteq [[a, b]])
  proof: hf.mono h le_rfl

中文:
定理 mono_set
  条件: (hf : 整数erval整数egrable f μ a b) (h : [[c, d]] subseteq [[a, b]])
  证明: hf.mono h le_rfl

Depends on / 依赖: hf.mono, le_rfl
-/
theorem mono_set (hf : IntervalIntegrable f μ a b) (h : [[c, d]] subseteq [[a, b]]) :
    IntervalIntegrable f μ c d :=
  hf.mono h le_rfl

/--
theorem `mono_set_ae` / 定理 `mono_set_ae`

English:
theorem mono_set_ae
  given: (hf : IntervalIntegrable f μ a b) (h : Ι c d <=ᵐ[μ] Ι a b)
  proof: intervalIntegrable_iff.mpr hf.def'.mono_set_ae h

中文:
定理 mono_set_ae
  条件: (hf : 整数erval整数egrable f μ a b) (h : Ι c d <=ᵐ[μ] Ι a b)
  证明: intervalIntegrable_iff.mpr hf.def'.mono_set_ae h

Depends on / 依赖: hf.def, intervalIntegrable_iff, intervalIntegrable_iff.mpr, mono_set_ae
-/
theorem mono_set_ae (hf : IntervalIntegrable f μ a b) (h : Ι c d <=ᵐ[μ] Ι a b) :
    IntervalIntegrable f μ c d :=
intervalIntegrable_iff.mpr hf.def'.mono_set_ae h

/--
theorem `mono_set'` / 定理 `mono_set'`

English:
theorem mono_set'
  given: (hf : IntervalIntegrable f μ a b) (hsub : Ι c d subseteq Ι a b)
  proof: hf.mono_set_ae Eventually.of_forall hsub

中文:
定理 mono_set'
  条件: (hf : 整数erval整数egrable f μ a b) (hsub : Ι c d subseteq Ι a b)
  证明: hf.mono_set_ae Eventually.of_forall hsub

Depends on / 依赖: Eventually, Eventually.of_forall, hf.mono_set_ae, mono_set_ae, of_forall
-/
theorem mono_set' (hf : IntervalIntegrable f μ a b) (hsub : Ι c d subseteq Ι a b) :
    IntervalIntegrable f μ c d :=
hf.mono_set_ae Eventually.of_forall hsub

/--
theorem `mono_fun_enorm` / 定理 `mono_fun_enorm`

English:
theorem mono_fun_enorm
  statement: [PseudoMetrizableSpace ε'] {g : Real -> ε'}
  proof: intervalIntegrable_iff.2 hf.def'.integrable.mono_enorm hgm hle

中文:
定理 mono_fun_enorm
  结论: [PseudoMetrizableSpace ε'] {g : 实数 -> ε'}
  证明: intervalIntegrable_iff.2 hf.def'.integrable.mono_enorm hgm hle

Depends on / 依赖: hf.def, integrable, integrable.mono_enorm, intervalIntegrable_iff, mono_enorm
-/
theorem mono_fun_enorm [PseudoMetrizableSpace ε'] {g : Real -> ε'}
    (hf : IntervalIntegrable f μ a b) (hgm : AEStronglyMeasurable g (μ.restrict (Ι a b)))
    (hle : (‖g ·‖ₑ) <=ᵐ[μ.restrict (Ι a b)] (‖f ·‖ₑ)) : IntervalIntegrable g μ a b :=
intervalIntegrable_iff.2 hf.def'.integrable.mono_enorm hgm hle

/--
theorem `mono_fun` / 定理 `mono_fun`

English:
theorem mono_fun
  statement: {f : Real -> E} [NormedAddCommGroup F] {g : Real -> F} (hf : IntervalIntegrable f μ a b)
  proof: intervalIntegrable_iff.2 hf.def'.integrable.mono hgm hle

中文:
定理 mono_fun
  结论: {f : 实数 -> E} [NormedAddCommGroup F] {g : 实数 -> F} (hf : 整数erval整数egrable f μ a b)
  证明: intervalIntegrable_iff.2 hf.def'.integrable.mono hgm hle

Depends on / 依赖: hf.def, integrable, integrable.mono, intervalIntegrable_iff
-/
theorem mono_fun {f : Real -> E} [NormedAddCommGroup F] {g : Real -> F} (hf : IntervalIntegrable f μ a b)
    (hgm : AEStronglyMeasurable g (μ.restrict (Ι a b)))
    (hle : (fun x => ‖g x‖) <=ᵐ[μ.restrict (Ι a b)] fun x => ‖f x‖) : IntervalIntegrable g μ a b :=
intervalIntegrable_iff.2 hf.def'.integrable.mono hgm hle

-- XXX: the best spelling of this lemma may look slightly different (e.gl, with different domain)
/--
theorem `mono_fun_enorm'` / 定理 `mono_fun_enorm'`

English:
theorem mono_fun_enorm'
  statement: {f : Real -> ε} {g : Real -> Real>=0∞} (hg : IntervalIntegrable g μ a b)
  proof: intervalIntegrable_iff.2 hg.def'.integrable.mono_enorm hfm hle

中文:
定理 mono_fun_enorm'
  结论: {f : 实数 -> ε} {g : 实数 -> 实数>=0∞} (hg : 整数erval整数egrable g μ a b)
  证明: intervalIntegrable_iff.2 hg.def'.integrable.mono_enorm hfm hle

Depends on / 依赖: hg.def, integrable, integrable.mono_enorm, intervalIntegrable_iff, mono_enorm
-/
theorem mono_fun_enorm' {f : Real -> ε} {g : Real -> Real>=0∞} (hg : IntervalIntegrable g μ a b)
    (hfm : AEStronglyMeasurable f (μ.restrict (Ι a b)))
    (hle : (fun x => ‖f x‖ₑ) <=ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b :=
intervalIntegrable_iff.2 hg.def'.integrable.mono_enorm hfm hle

/--
theorem `mono_fun'` / 定理 `mono_fun'`

English:
theorem mono_fun'
  statement: {f : Real -> E} {g : Real -> Real} (hg : IntervalIntegrable g μ a b)
  proof: intervalIntegrable_iff.2 hg.def'.integrable.mono' hfm hle

omit [PseudoMetrizableSpace ε] in

中文:
定理 mono_fun'
  结论: {f : 实数 -> E} {g : 实数 -> 实数} (hg : 整数erval整数egrable g μ a b)
  证明: intervalIntegrable_iff.2 hg.def'.integrable.mono' hfm hle

omit [PseudoMetrizableSpace ε] in

Depends on / 依赖: hg.def, integrable, integrable.mono, intervalIntegrable_iff
-/
theorem mono_fun' {f : Real -> E} {g : Real -> Real} (hg : IntervalIntegrable g μ a b)
    (hfm : AEStronglyMeasurable f (μ.restrict (Ι a b)))
    (hle : (fun x => ‖f x‖) <=ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b :=
intervalIntegrable_iff.2 hg.def'.integrable.mono' hfm hle

omit [PseudoMetrizableSpace ε] in
/--
theorem `aestronglyMeasurable` / 定理 `aestronglyMeasurable`

English:
theorem aestronglyMeasurable
  given: (h : IntervalIntegrable f μ a b)
  proof: h.1.aestronglyMeasurable

omit [PseudoMetrizableSpace ε] in

中文:
定理 aestronglyMeasurable
  条件: (h : 整数erval整数egrable f μ a b)
  证明: h.1.aestronglyMeasurable

omit [PseudoMetrizableSpace ε] in
-/
protected theorem aestronglyMeasurable (h : IntervalIntegrable f μ a b) :
    AEStronglyMeasurable f (μ.restrict (Ioc a b)) :=
  h.1.aestronglyMeasurable

omit [PseudoMetrizableSpace ε] in
/--
theorem `aestronglyMeasurable'` / 定理 `aestronglyMeasurable'`

English:
theorem aestronglyMeasurable'
  given: (h : IntervalIntegrable f μ a b)
  proof: h.2.aestronglyMeasurable

omit [PseudoMetrizableSpace ε] in

中文:
定理 aestronglyMeasurable'
  条件: (h : 整数erval整数egrable f μ a b)
  证明: h.2.aestronglyMeasurable

omit [PseudoMetrizableSpace ε] in
-/
protected theorem aestronglyMeasurable' (h : IntervalIntegrable f μ a b) :
    AEStronglyMeasurable f (μ.restrict (Ioc b a)) :=
  h.2.aestronglyMeasurable

omit [PseudoMetrizableSpace ε] in
/--
theorem `aestronglyMeasurable_restrict_uIoc` / 定理 `aestronglyMeasurable_restrict_uIoc`

English:
theorem aestronglyMeasurable_restrict_uIoc
  given: (h : IntervalIntegrable f μ a b)
  proof: by
  by_cases hab : a <= b
  · rw [uIoc_of_le hab]; exact h.aestronglyMeasurable
  · rw [uIoc_of_ge (by linarith)]; exact h.aestronglyMeasurable'

中文:
定理 aestronglyMeasurable_restrict_uIoc
  条件: (h : 整数erval整数egrable f μ a b)
  证明: by
  by_cases hab : a <= b
  · rw [uIoc_of_le hab]; exact h.aestronglyMeasurable
  · rw [uIoc_of_ge (by linarith)]; exact h.aestronglyMeasurable'
-/
protected theorem aestronglyMeasurable_restrict_uIoc (h : IntervalIntegrable f μ a b) :
    AEStronglyMeasurable f (μ.restrict (uIoc a b)) := by
  by_cases hab : a <= b
  · rw [uIoc_of_le hab]; exact h.aestronglyMeasurable
  · rw [uIoc_of_ge (by linarith)]; exact h.aestronglyMeasurable'

end

variable [NormedRing A] {f g : Real -> ε} {a b : Real} {μ : Measure Real}

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {R : Type*} [NormedAddCommGroup R] [SMulZeroClass R E] [IsBoundedSMul R E] {f : Real -> E}
  proof: ⟨h.1.smul r, h.2.smul r⟩

@[simp]

中文:
定理 smul
  结论: {R : 类型} [NormedAddCommGroup R] [SMulZeroClass R E] [IsBoundedSMul R E] {f : 实数 -> E}
  证明: ⟨h.1.smul r, h.2.smul r⟩

@[simp]
-/
theorem smul {R : Type*} [NormedAddCommGroup R] [SMulZeroClass R E] [IsBoundedSMul R E] {f : Real -> E}
    (h : IntervalIntegrable f μ a b) (r : R) :
    IntervalIntegrable (r • f) μ a b :=
  ⟨h.1.smul r, h.2.smul r⟩

@[simp]
/--
theorem `add` / 定理 `add`

English:
theorem add
  given: [ContinuousAdd ε] (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b)
  proof: ⟨hf.1.add hg.1, hf.2.add hg.2⟩

@[simp]

中文:
定理 add
  条件: [ContinuousAdd ε] (hf : 整数erval整数egrable f μ a b) (hg : 整数erval整数egrable g μ a b)
  证明: ⟨hf.1.add hg.1, hf.2.add hg.2⟩

@[simp]
-/
theorem add [ContinuousAdd ε] (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    IntervalIntegrable (fun x => f x + g x) μ a b :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

@[simp]
/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: {f g : Real -> E} (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b)
  proof: ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

中文:
定理 sub
  条件: {f g : 实数 -> E} (hf : 整数erval整数egrable f μ a b) (hg : 整数erval整数egrable g μ a b)
  证明: ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
-/
theorem sub {f g : Real -> E} (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    IntervalIntegrable (fun x => f x - g x) μ a b :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  statement: {ε} [TopologicalSpace ε] [ENormedAddCommMonoid ε] [ContinuousAdd ε]
  proof: ⟨integrable_finsetSum' s fun i hi => (h i hi).1, integrable_finsetSum' s fun i hi => (h i hi).2⟩

中文:
定理 sum
  结论: {ε} [TopologicalSpace ε] [ENormedAddCommMonoid ε] [ContinuousAdd ε]
  证明: ⟨integrable_finsetSum' s fun i hi => (h i hi).1, integrable_finsetSum' s fun i hi => (h i hi).2⟩

Depends on / 依赖: integrable_finsetSum
-/
theorem sum {ε} [TopologicalSpace ε] [ENormedAddCommMonoid ε] [ContinuousAdd ε]
    (s : Finset ι) {f : ι -> Real -> ε} (h : forall i in s, IntervalIntegrable (f i) μ a b) :
    IntervalIntegrable (∑ i in s, f i) μ a b :=
  ⟨integrable_finsetSum' s fun i hi => (h i hi).1, integrable_finsetSum' s fun i hi => (h i hi).2⟩

/-- Finite sums of interval integrable functions are interval integrable. -/
@[simp]
/--
theorem `finsum` / 定理 `finsum`

English:
theorem finsum
  proof: by
  by_cases h₁ : f.support.Finite
  · simp [finsum_eq_sum _ h₁, IntervalIntegrable.sum h₁.toFinset (fun i _ => h i)]
  · rw [finsum_of_infinite_support h₁]
.2 apply intervalIntegrable_const_iff (c := 0) (by simp)
    tauto

中文:
定理 finsum
  证明: by
  by_cases h₁ : f.support.Finite
  · simp [finsum_eq_sum _ h₁, IntervalIntegrable.sum h₁.toFinset (fun i _ => h i)]
  · rw [finsum_of_infinite_support h₁]
.2 apply intervalIntegrable_const_iff (c := 0) (by simp)
    tauto
-/
protected theorem finsum
    {ε} [TopologicalSpace ε] [ENormedAddCommMonoid ε] [ContinuousAdd ε] [PseudoMetrizableSpace ε]
    {f : ι -> Real -> ε} (h : forall i, IntervalIntegrable (f i) μ a b) :
    IntervalIntegrable (∑ᶠ i, f i) μ a b := by
  by_cases h₁ : f.support.Finite
  · simp [finsum_eq_sum _ h₁, IntervalIntegrable.sum h₁.toFinset (fun i _ => h i)]
  · rw [finsum_of_infinite_support h₁]
.2 apply intervalIntegrable_const_iff (c := 0) (by simp)
    tauto

section Mul

/--
theorem `mul_continuousOn` / 定理 `mul_continuousOn`

English:
theorem mul_continuousOn
  statement: {f g : Real -> A} (hf : IntervalIntegrable f μ a b)
  proof: by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.mul_continuousOn_of_subset hg measurableSet_Ioc isCompact_uIcc Ioc_subset_Icc_self

中文:
定理 mul_continuousOn
  结论: {f g : 实数 -> A} (hf : 整数erval整数egrable f μ a b)
  证明: by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.mul_continuousOn_of_subset hg measurableSet_Ioc isCompact_uIcc Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, hf.mul_continuousOn_of_subset, intervalIntegrable_iff, isCompact_uIcc, measurableSet_Ioc, mul_continuousOn_of_subset
-/
theorem mul_continuousOn {f g : Real -> A} (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => f x * g x) μ a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.mul_continuousOn_of_subset hg measurableSet_Ioc isCompact_uIcc Ioc_subset_Icc_self

/--
theorem `continuousOn_mul` / 定理 `continuousOn_mul`

English:
theorem continuousOn_mul
  statement: {f g : Real -> A} (hf : IntervalIntegrable f μ a b)
  proof: by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.continuousOn_mul_of_subset hg isCompact_uIcc measurableSet_Ioc Ioc_subset_Icc_self

@[simp]

中文:
定理 continuousOn_mul
  结论: {f g : 实数 -> A} (hf : 整数erval整数egrable f μ a b)
  证明: by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.continuousOn_mul_of_subset hg isCompact_uIcc measurableSet_Ioc Ioc_subset_Icc_self

@[simp]

Depends on / 依赖: Ioc_subset_Icc_self, continuousOn_mul_of_subset, hf.continuousOn_mul_of_subset, intervalIntegrable_iff, isCompact_uIcc, measurableSet_Ioc
-/
theorem continuousOn_mul {f g : Real -> A} (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => g x * f x) μ a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.continuousOn_mul_of_subset hg isCompact_uIcc measurableSet_Ioc Ioc_subset_Icc_self

@[simp]
/--
theorem `const_mul` / 定理 `const_mul`

English:
theorem const_mul
  given: {f : Real -> A} (hf : IntervalIntegrable f μ a b) (c : A)
  proof: hf.continuousOn_mul continuousOn_const

@[simp]

中文:
定理 const_mul
  条件: {f : 实数 -> A} (hf : 整数erval整数egrable f μ a b) (c : A)
  证明: hf.continuousOn_mul continuousOn_const

@[simp]

Depends on / 依赖: continuousOn_const, continuousOn_mul, hf.continuousOn_mul
-/
theorem const_mul {f : Real -> A} (hf : IntervalIntegrable f μ a b) (c : A) :
    IntervalIntegrable (fun x => c * f x) μ a b :=
  hf.continuousOn_mul continuousOn_const

@[simp]
/--
theorem `mul_const` / 定理 `mul_const`

English:
theorem mul_const
  given: {f : Real -> A} (hf : IntervalIntegrable f μ a b) (c : A)
  proof: hf.mul_continuousOn continuousOn_const

中文:
定理 mul_const
  条件: {f : 实数 -> A} (hf : 整数erval整数egrable f μ a b) (c : A)
  证明: hf.mul_continuousOn continuousOn_const

Depends on / 依赖: continuousOn_const, hf.mul_continuousOn, mul_continuousOn
-/
theorem mul_const {f : Real -> A} (hf : IntervalIntegrable f μ a b) (c : A) :
    IntervalIntegrable (fun x => f x * c) μ a b :=
  hf.mul_continuousOn continuousOn_const

end Mul

section SMul

variable {f : Real -> 𝕜} {g : Real -> E} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
theorem `smul_continuousOn` / 定理 `smul_continuousOn`

English:
theorem smul_continuousOn
  statement: (hf : IntervalIntegrable f μ a b)
  proof: by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.smul_continuousOn_of_subset hg measurableSet_Ioc isCompact_uIcc Ioc_subset_Icc_self

中文:
定理 smul_continuousOn
  结论: (hf : 整数erval整数egrable f μ a b)
  证明: by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.smul_continuousOn_of_subset hg measurableSet_Ioc isCompact_uIcc Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, hf.smul_continuousOn_of_subset, intervalIntegrable_iff, isCompact_uIcc, measurableSet_Ioc, smul_continuousOn_of_subset
-/
theorem smul_continuousOn (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => f x • g x) μ a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.smul_continuousOn_of_subset hg measurableSet_Ioc isCompact_uIcc Ioc_subset_Icc_self

/--
theorem `continuousOn_smul` / 定理 `continuousOn_smul`

English:
theorem continuousOn_smul
  statement: (hg : IntervalIntegrable g μ a b)
  proof: by
  rw [intervalIntegrable_iff] at hg ⊢
  exact hg.continuousOn_smul_of_subset hf isCompact_uIcc measurableSet_Ioc Ioc_subset_Icc_self

中文:
定理 continuousOn_smul
  结论: (hg : 整数erval整数egrable g μ a b)
  证明: by
  rw [intervalIntegrable_iff] at hg ⊢
  exact hg.continuousOn_smul_of_subset hf isCompact_uIcc measurableSet_Ioc Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, continuousOn_smul_of_subset, hg.continuousOn_smul_of_subset, intervalIntegrable_iff, isCompact_uIcc, measurableSet_Ioc
-/
theorem continuousOn_smul (hg : IntervalIntegrable g μ a b)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => f x • g x) μ a b := by
  rw [intervalIntegrable_iff] at hg ⊢
  exact hg.continuousOn_smul_of_subset hf isCompact_uIcc measurableSet_Ioc Ioc_subset_Icc_self

end SMul

@[simp]
/--
theorem `div_const` / 定理 `div_const`

English:
theorem div_const
  statement: {𝕜 : Type*} {f : Real -> 𝕜} [NormedDivisionRing 𝕜] (h : IntervalIntegrable f μ a b)
  proof: by
  simpa only [div_eq_mul_inv] using mul_const h c⁻¹

中文:
定理 div_const
  结论: {𝕜 : 类型} {f : 实数 -> 𝕜} [NormedDivisionRing 𝕜] (h : 整数erval整数egrable f μ a b)
  证明: by
  simpa only [div_eq_mul_inv] using mul_const h c⁻¹

Depends on / 依赖: div_eq_mul_inv, mul_const
-/
theorem div_const {𝕜 : Type*} {f : Real -> 𝕜} [NormedDivisionRing 𝕜] (h : IntervalIntegrable f μ a b)
    (c : 𝕜) : IntervalIntegrable (fun x => f x / c) μ a b := by
  simpa only [div_eq_mul_inv] using mul_const h c⁻¹

variable [PseudoMetrizableSpace ε]

/--
theorem `comp_mul_left` / 定理 `comp_mul_left`

English:
theorem comp_mul_left
  statement: (hf : IntervalIntegrable f volume a b) {c : Real}
  proof: by
  rcases eq_or_ne c 0 with (hc | hc); · rw [hc]; simp
  rw [intervalIntegrable_iff' h] at hf
  rw [intervalIntegrable_iff' h'] at ⊢
  have A : MeasurableEmbedding fun x => x * c⁻¹ :=
    (Homeomorph.mulRight₀ _ (inv_ne_zero hc)).isClosedEmbedding.measurableEmbedding
  rw [← Real.smul_map_volume_m

中文:
定理 comp_mul_left
  结论: (hf : 整数erval整数egrable f volume a b) {c : 实数}
  证明: by
  rcases eq_or_ne c 0 with (hc | hc); · rw [hc]; simp
  rw [intervalIntegrable_iff' h] at hf
  rw [intervalIntegrable_iff' h'] at ⊢
  have A : MeasurableEmbedding fun x => x * c⁻¹ :=
    (Homeomorph.mulRight₀ _ (inv_ne_zero hc)).isClosedEmbedding.measurableEmbedding
  rw [← Real.smul_map_volume_m

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, IntegrableOn, IntervalIntegrable, MeasurableEmbedding, Measure, Measure.restrict_smu, Real.smul_map_volume_mul_right, eq_or_ne, finiteness, intervalIntegrable_iff, inv_ne_zero, isClosedEmbedding, isClosedEmbedding.measurableEmbedding, measurableEmbedding, restrict_smu, smul_map_volume_mul_right, volume
-/
theorem comp_mul_left (hf : IntervalIntegrable f volume a b) {c : Real}
    (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
    (h' : ‖f (c * min (a / c) (b / c))‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (c * x)) volume (a / c) (b / c) := by
  rcases eq_or_ne c 0 with (hc | hc); · rw [hc]; simp
  rw [intervalIntegrable_iff' h] at hf
  rw [intervalIntegrable_iff' h'] at ⊢
  have A : MeasurableEmbedding fun x => x * c⁻¹ :=
    (Homeomorph.mulRight₀ _ (inv_ne_zero hc)).isClosedEmbedding.measurableEmbedding
  rw [← Real.smul_map_volume_mul_right (inv_ne_zero hc)]; rw [IntegrableOn]; rw [Measure.restrict_smul]; rw [integrable_smul_measure (by simpa : ENNReal.ofReal |c⁻¹| != 0) ENNReal.ofReal_ne_top]; rw [← IntegrableOn]; rw [MeasurableEmbedding.integrableOn_map_iff A]
  convert! hf using 1
  · ext; simp only [comp_apply]; congr 1; field
  · rw [preimage_mul_const_uIcc (inv_ne_zero hc)]; field_simp

-- Note that `h'` is **not** implied by `h` if `c` is negative.
-- TODO: generalise this lemma to enorms!
/--
theorem `comp_mul_left_iff` / 定理 `comp_mul_left_iff`

English:
theorem comp_mul_left_iff
  statement: {f : Real -> E} {c : Real} (hc : c != 0) (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
  proof: by
  exact ⟨fun h => by simpa [hc] using h.comp_mul_left (c := c⁻¹) h' (by simp),
    (comp_mul_left · h h')⟩

中文:
定理 comp_mul_left_iff
  结论: {f : 实数 -> E} {c : 实数} (hc : c != 0) (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
  证明: by
  exact ⟨fun h => by simpa [hc] using h.comp_mul_left (c := c⁻¹) h' (by simp),
    (comp_mul_left · h h')⟩

Depends on / 依赖: IntervalIntegrable, comp_mul_left, finiteness, h.comp_mul_left, volume
-/
theorem comp_mul_left_iff {f : Real -> E} {c : Real} (hc : c != 0) (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
    (h' : ‖f (c * min (a / c) (b / c))‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (c * x)) volume (a / c) (b / c) ↔
      IntervalIntegrable f volume a b := by
  exact ⟨fun h => by simpa [hc] using h.comp_mul_left (c := c⁻¹) h' (by simp),
    (comp_mul_left · h h')⟩

/--
theorem `comp_mul_right` / 定理 `comp_mul_right`

English:
theorem comp_mul_right
  statement: (hf : IntervalIntegrable f volume a b) {c : Real}
  proof: by
  simpa only [mul_comm] using comp_mul_left hf h h'

中文:
定理 comp_mul_right
  结论: (hf : 整数erval整数egrable f volume a b) {c : 实数}
  证明: by
  simpa only [mul_comm] using comp_mul_left hf h h'

Depends on / 依赖: IntervalIntegrable, comp_mul_left, finiteness, mul_comm, volume
-/
theorem comp_mul_right (hf : IntervalIntegrable f volume a b) {c : Real}
    (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
    (h' : ‖f (c * min (a / c) (b / c))‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (x * c)) volume (a / c) (b / c) := by
  simpa only [mul_comm] using comp_mul_left hf h h'

/--
theorem `comp_add_right` / 定理 `comp_add_right`

English:
theorem comp_add_right
  statement: (hf : IntervalIntegrable f volume a b) (c : Real)
  proof: by
  have h' : ‖f (min (a - c) (b - c) + c)‖ₑ != ⊤ := by
    rw [min_sub_sub_right]; rw [sub_add]; rw [sub_self]; rw [sub_zero]
    exact h
  wlog hab : a <= b generalizing a b
  · apply IntervalIntegrable.symm (this hf.symm ?_ ?_ (le_of_not_ge hab))
    · rw [min_comm]; exact h
    · rw [min_comm];

中文:
定理 comp_add_right
  结论: (hf : 整数erval整数egrable f volume a b) (c : 实数)
  证明: by
  have h' : ‖f (min (a - c) (b - c) + c)‖ₑ != ⊤ := by
    rw [min_sub_sub_right]; rw [sub_add]; rw [sub_self]; rw [sub_zero]
    exact h
  wlog hab : a <= b generalizing a b
  · apply IntervalIntegrable.symm (this hf.symm ?_ ?_ (le_of_not_ge hab))
    · rw [min_comm]; exact h
    · rw [min_comm];

Depends on / 依赖: Homeomo, IntervalIntegrable, IntervalIntegrable.symm, MeasurableEmbedding, finiteness, generalizing, hf.symm, intervalIntegrable_iff, le_of_not_ge, min_comm, min_sub_sub_right, sub_add, sub_self, sub_zero, volume
-/
theorem comp_add_right (hf : IntervalIntegrable f volume a b) (c : Real)
    (h : ‖f (min a b)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (x + c)) volume (a - c) (b - c) := by
  have h' : ‖f (min (a - c) (b - c) + c)‖ₑ != ⊤ := by
    rw [min_sub_sub_right]; rw [sub_add]; rw [sub_self]; rw [sub_zero]
    exact h
  wlog hab : a <= b generalizing a b
  · apply IntervalIntegrable.symm (this hf.symm ?_ ?_ (le_of_not_ge hab))
    · rw [min_comm]; exact h
    · rw [min_comm]; exact h'
  rw [intervalIntegrable_iff' h] at hf
  rw [intervalIntegrable_iff' h'] at ⊢
  have A : MeasurableEmbedding fun x => x + c :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  rw [← map_add_right_eq_self volume c] at hf
  convert! (MeasurableEmbedding.integrableOn_map_iff A).mp hf using 1
  rw [preimage_add_const_uIcc]

/--
theorem `comp_add_right_iff` / 定理 `comp_add_right_iff`

English:
theorem comp_add_right_iff
  given: {c : Real} (h : ‖f (min a b + c)‖ₑ != ⊤ := by finiteness)
  proof: by simpa using hf.comp_add_right (-c)
  mpr hf := by
    have : ‖f (min (a + c) (b + c))‖ₑ != ⊤ := by rwa [min_add_add_right]
    simpa using hf.comp_add_right c

中文:
定理 comp_add_right_iff
  条件: {c : 实数} (h : ‖f (min a b + c)‖ₑ != ⊤ := by finiteness)
  证明: by simpa using hf.comp_add_right (-c)
  mpr hf := by
    have : ‖f (min (a + c) (b + c))‖ₑ != ⊤ := by rwa [min_add_add_right]
    simpa using hf.comp_add_right c

Depends on / 依赖: IntervalIntegrable, comp_add_right, finiteness, hf.comp_add_right, min_add_add_right, volume
-/
theorem comp_add_right_iff {c : Real} (h : ‖f (min a b + c)‖ₑ != ⊤ := by finiteness) :
    IntervalIntegrable (fun x => f (x + c)) volume a b
      ↔ IntervalIntegrable f volume (a + c) (b + c) where
  mp hf := by simpa using hf.comp_add_right (-c)
  mpr hf := by
    have : ‖f (min (a + c) (b + c))‖ₑ != ⊤ := by rwa [min_add_add_right]
    simpa using hf.comp_add_right c

/--
theorem `comp_add_left` / 定理 `comp_add_left`

English:
theorem comp_add_left
  statement: (hf : IntervalIntegrable f volume a b) (c : Real)
  proof: by
  simpa [add_comm] using IntervalIntegrable.comp_add_right hf c h

中文:
定理 comp_add_left
  结论: (hf : 整数erval整数egrable f volume a b) (c : 实数)
  证明: by
  simpa [add_comm] using IntervalIntegrable.comp_add_right hf c h

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.comp_add_right, add_comm, comp_add_right, finiteness, volume
-/
theorem comp_add_left (hf : IntervalIntegrable f volume a b) (c : Real)
    (h : ‖f (min a b)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (c + x)) volume (a - c) (b - c) := by
  simpa [add_comm] using IntervalIntegrable.comp_add_right hf c h

/--
theorem `comp_add_left_iff` / 定理 `comp_add_left_iff`

English:
theorem comp_add_left_iff
  given: {c : Real} (h : ‖f (min a b)‖ₑ != ⊤ := by finiteness)
  proof: by
  simp_rw [add_comm c]
  rw [IntervalIntegrable.comp_add_right_iff (by grind)]
  simp

中文:
定理 comp_add_left_iff
  条件: {c : 实数} (h : ‖f (min a b)‖ₑ != ⊤ := by finiteness)
  证明: by
  simp_rw [add_comm c]
  rw [IntervalIntegrable.comp_add_right_iff (by grind)]
  simp

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.comp_add_right_iff, add_comm, comp_add_right_iff, finiteness, simp_rw, volume
-/
theorem comp_add_left_iff {c : Real} (h : ‖f (min a b)‖ₑ != ⊤ := by finiteness) :
    IntervalIntegrable (fun x => f (c + x)) volume (a - c) (b - c)
      ↔ IntervalIntegrable f volume a b := by
  simp_rw [add_comm c]
  rw [IntervalIntegrable.comp_add_right_iff (by grind)]
  simp

/--
theorem `comp_sub_right` / 定理 `comp_sub_right`

English:
theorem comp_sub_right
  statement: (hf : IntervalIntegrable f volume a b) (c : Real)
  proof: by
  simpa only [sub_neg_eq_add] using! IntervalIntegrable.comp_add_right hf (-c) h

中文:
定理 comp_sub_right
  结论: (hf : 整数erval整数egrable f volume a b) (c : 实数)
  证明: by
  simpa only [sub_neg_eq_add] using! IntervalIntegrable.comp_add_right hf (-c) h

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.comp_add_right, comp_add_right, finiteness, sub_neg_eq_add, volume
-/
theorem comp_sub_right (hf : IntervalIntegrable f volume a b) (c : Real)
    (h : ‖f (min a b)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (x - c)) volume (a + c) (b + c) := by
  simpa only [sub_neg_eq_add] using! IntervalIntegrable.comp_add_right hf (-c) h

/--
theorem `comp_sub_right_iff` / 定理 `comp_sub_right_iff`

English:
theorem comp_sub_right_iff
  given: {c : Real} (h : ‖f (min a b)‖ₑ != ⊤ := by finiteness)
  proof: by
  simp_rw [sub_eq_add_neg]
  rw [IntervalIntegrable.comp_add_right_iff (by grind)]
  simp

中文:
定理 comp_sub_right_iff
  条件: {c : 实数} (h : ‖f (min a b)‖ₑ != ⊤ := by finiteness)
  证明: by
  simp_rw [sub_eq_add_neg]
  rw [IntervalIntegrable.comp_add_right_iff (by grind)]
  simp

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.comp_add_right_iff, comp_add_right_iff, finiteness, simp_rw, sub_eq_add_neg, volume
-/
theorem comp_sub_right_iff {c : Real} (h : ‖f (min a b)‖ₑ != ⊤ := by finiteness) :
    IntervalIntegrable (fun x => f (x - c)) volume (a + c) (b + c)
      ↔ IntervalIntegrable f volume a b := by
  simp_rw [sub_eq_add_neg]
  rw [IntervalIntegrable.comp_add_right_iff (by grind)]
  simp

-- TODO: generalise this lemma to enorms!
/--
theorem `iff_comp_neg` / 定理 `iff_comp_neg`

English:
theorem iff_comp_neg
  given: {f : Real -> E} (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
  proof: by
  rw [← comp_mul_left_iff (neg_ne_zero.2 one_ne_zero) h (by simp)]; simp [div_neg]

中文:
定理 iff_comp_neg
  条件: {f : 实数 -> E} (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
  证明: by
  rw [← comp_mul_left_iff (neg_ne_zero.2 one_ne_zero) h (by simp)]; simp [div_neg]

Depends on / 依赖: IntervalIntegrable, comp_mul_left_iff, div_neg, finiteness, neg_ne_zero, one_ne_zero, volume
-/
theorem iff_comp_neg {f : Real -> E} (h : ‖f (min a b)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable f volume a b ↔ IntervalIntegrable (fun x => f (-x)) volume (-a) (-b) := by
  rw [← comp_mul_left_iff (neg_ne_zero.2 one_ne_zero) h (by simp)]; simp [div_neg]

-- TODO: generalise this lemma to enorms!
/--
theorem `comp_sub_left` / 定理 `comp_sub_left`

English:
theorem comp_sub_left
  statement: {f : Real -> E} (hf : IntervalIntegrable f volume a b) (c : Real)
  proof: by
  simpa only [neg_sub, ← sub_eq_add_neg] using (iff_comp_neg (by simp)).mp (hf.comp_add_left c h)

中文:
定理 comp_sub_left
  结论: {f : 实数 -> E} (hf : 整数erval整数egrable f volume a b) (c : 实数)
  证明: by
  simpa only [neg_sub, ← sub_eq_add_neg] using (iff_comp_neg (by simp)).mp (hf.comp_add_left c h)

Depends on / 依赖: IntervalIntegrable, comp_add_left, finiteness, hf.comp_add_left, iff_comp_neg, neg_sub, sub_eq_add_neg, volume
-/
theorem comp_sub_left {f : Real -> E} (hf : IntervalIntegrable f volume a b) (c : Real)
    (h : ‖f (min a b)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (c - x)) volume (c - a) (c - b) := by
  simpa only [neg_sub, ← sub_eq_add_neg] using (iff_comp_neg (by simp)).mp (hf.comp_add_left c h)

-- TODO: generalise this lemma to enorms!
/--
theorem `comp_sub_left_iff` / 定理 `comp_sub_left_iff`

English:
theorem comp_sub_left_iff
  given: {f : Real -> E} (c : Real) (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
  proof: ⟨fun h => by simpa using h.comp_sub_left c, (.comp_sub_left · c h)⟩

中文:
定理 comp_sub_left_iff
  条件: {f : 实数 -> E} (c : 实数) (h : ‖f (min a b)‖ₑ != ∞ := by finiteness)
  证明: ⟨fun h => by simpa using h.comp_sub_left c, (.comp_sub_left · c h)⟩

Depends on / 依赖: IntervalIntegrable, comp_sub_left, finiteness, h.comp_sub_left, volume
-/
theorem comp_sub_left_iff {f : Real -> E} (c : Real) (h : ‖f (min a b)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable (fun x => f (c - x)) volume (c - a) (c - b) ↔
      IntervalIntegrable f volume a b :=
  ⟨fun h => by simpa using h.comp_sub_left c, (.comp_sub_left · c h)⟩

end IntervalIntegrable

/-!
## Continuous functions are interval integrable
-/
section

variable {μ : Measure Real} [IsLocallyFiniteMeasure μ]

/--
theorem `ContinuousOn.intervalIntegrable` / 定理 `ContinuousOn.intervalIntegrable`

English:
theorem ContinuousOn.intervalIntegrable
  given: {u : Real -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b))
  proof: (ContinuousOn.integrableOn_Icc hu).intervalIntegrable

中文:
定理 ContinuousOn.intervalIntegrable
  条件: {u : 实数 -> E} {a b : 实数} (hu : ContinuousOn u (uIcc a b))
  证明: (ContinuousOn.integrableOn_Icc hu).intervalIntegrable

Depends on / 依赖: ContinuousOn, ContinuousOn.integrableOn_Icc, integrableOn_Icc, intervalIntegrable
-/
theorem ContinuousOn.intervalIntegrable {u : Real -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) :
    IntervalIntegrable u μ a b :=
  (ContinuousOn.integrableOn_Icc hu).intervalIntegrable

/--
theorem `ContinuousOn.intervalIntegrable_of_Icc` / 定理 `ContinuousOn.intervalIntegrable_of_Icc`

English:
theorem ContinuousOn.intervalIntegrable_of_Icc
  statement: {u : Real -> E} {a b : Real} (h : a <= b)
  proof: ContinuousOn.intervalIntegrable ((uIcc_of_le h).symm ▸ hu)

中文:
定理 ContinuousOn.intervalIntegrable_of_Icc
  结论: {u : 实数 -> E} {a b : 实数} (h : a <= b)
  证明: ContinuousOn.intervalIntegrable ((uIcc_of_le h).symm ▸ hu)

Depends on / 依赖: ContinuousOn, ContinuousOn.intervalIntegrable, intervalIntegrable, uIcc_of_le
-/
theorem ContinuousOn.intervalIntegrable_of_Icc {u : Real -> E} {a b : Real} (h : a <= b)
    (hu : ContinuousOn u (Icc a b)) : IntervalIntegrable u μ a b :=
  ContinuousOn.intervalIntegrable ((uIcc_of_le h).symm ▸ hu)

/--
theorem `Continuous.intervalIntegrable` / 定理 `Continuous.intervalIntegrable`

English:
theorem Continuous.intervalIntegrable
  given: {u : Real -> E} (hu : Continuous u) (a b : Real)
  proof: hu.continuousOn.intervalIntegrable

中文:
定理 Continuous.intervalIntegrable
  条件: {u : 实数 -> E} (hu : Continuous u) (a b : 实数)
  证明: hu.continuousOn.intervalIntegrable

Depends on / 依赖: continuousOn, hu.continuousOn.intervalIntegrable, intervalIntegrable
-/
theorem Continuous.intervalIntegrable {u : Real -> E} (hu : Continuous u) (a b : Real) :
    IntervalIntegrable u μ a b :=
  hu.continuousOn.intervalIntegrable

end

/-!
## Monotone and antitone functions are integral integrable
-/
section

variable {μ : Measure Real} [IsLocallyFiniteMeasure μ] [ConditionallyCompleteLinearOrder E]
  [OrderTopology E] [SecondCountableTopology E]

/--
theorem `MonotoneOn.intervalIntegrable` / 定理 `MonotoneOn.intervalIntegrable`

English:
theorem MonotoneOn.intervalIntegrable
  given: {u : Real -> E} {a b : Real} (hu : MonotoneOn u (uIcc a b))
  proof: by
  rw [intervalIntegrable_iff]
  exact (hu.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self

中文:
定理 MonotoneOn.intervalIntegrable
  条件: {u : 实数 -> E} {a b : 实数} (hu : MonotoneOn u (uIcc a b))
  证明: by
  rw [intervalIntegrable_iff]
  exact (hu.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, hu.integrableOn_isCompact, integrableOn_isCompact, intervalIntegrable_iff, isCompact_uIcc, mono_set
-/
theorem MonotoneOn.intervalIntegrable {u : Real -> E} {a b : Real} (hu : MonotoneOn u (uIcc a b)) :
    IntervalIntegrable u μ a b := by
  rw [intervalIntegrable_iff]
  exact (hu.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `AntitoneOn.intervalIntegrable` / 定理 `AntitoneOn.intervalIntegrable`

English:
theorem AntitoneOn.intervalIntegrable
  given: {u : Real -> E} {a b : Real} (hu : AntitoneOn u (uIcc a b))
  proof: hu.dual_right.intervalIntegrable

中文:
定理 AntitoneOn.intervalIntegrable
  条件: {u : 实数 -> E} {a b : 实数} (hu : AntitoneOn u (uIcc a b))
  证明: hu.dual_right.intervalIntegrable

Depends on / 依赖: dual_right, hu.dual_right.intervalIntegrable, intervalIntegrable
-/
theorem AntitoneOn.intervalIntegrable {u : Real -> E} {a b : Real} (hu : AntitoneOn u (uIcc a b)) :
    IntervalIntegrable u μ a b :=
  hu.dual_right.intervalIntegrable

/--
theorem `Monotone.intervalIntegrable` / 定理 `Monotone.intervalIntegrable`

English:
theorem Monotone.intervalIntegrable
  given: {u : Real -> E} {a b : Real} (hu : Monotone u)
  proof: (hu.monotoneOn _).intervalIntegrable

中文:
定理 Monotone.intervalIntegrable
  条件: {u : 实数 -> E} {a b : 实数} (hu : Monotone u)
  证明: (hu.monotoneOn _).intervalIntegrable

Depends on / 依赖: hu.monotoneOn, intervalIntegrable, monotoneOn
-/
theorem Monotone.intervalIntegrable {u : Real -> E} {a b : Real} (hu : Monotone u) :
    IntervalIntegrable u μ a b :=
  (hu.monotoneOn _).intervalIntegrable

/--
theorem `Antitone.intervalIntegrable` / 定理 `Antitone.intervalIntegrable`

English:
theorem Antitone.intervalIntegrable
  given: {u : Real -> E} {a b : Real} (hu : Antitone u)
  proof: (hu.antitoneOn _).intervalIntegrable

中文:
定理 Antitone.intervalIntegrable
  条件: {u : 实数 -> E} {a b : 实数} (hu : Antitone u)
  证明: (hu.antitoneOn _).intervalIntegrable

Depends on / 依赖: antitoneOn, hu.antitoneOn, intervalIntegrable
-/
theorem Antitone.intervalIntegrable {u : Real -> E} {a b : Real} (hu : Antitone u) :
    IntervalIntegrable u μ a b :=
  (hu.antitoneOn _).intervalIntegrable

end

/-!
## Interval integrability of functions with even or odd parity
-/
section

variable {f : Real -> E}

/--
lemma `intervalIntegrable_of_even₀` / 引理 `intervalIntegrable_of_even₀`

English:
lemma intervalIntegrable_of_even₀
  statement: (h₁f : forall x, f x = f (-x))
  proof: by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [IntervalIntegrable.iff_comp_neg ht]
    conv => arg 1; intro t; rw [← h₁f]
    simp [h₂f (-t) (by simp [h])]
  · rw [h]
  · exact h₂f t h

中文:
引理 intervalIntegrable_of_even₀
  结论: (h₁f : 对任意 x, f x = f (-x))
  证明: by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [IntervalIntegrable.iff_comp_neg ht]
    conv => arg 1; intro t; rw [← h₁f]
    simp [h₂f (-t) (by simp [h])]
  · rw [h]
  · exact h₂f t h

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.iff_comp_neg, finiteness, iff_comp_neg, lt_trichotomy, volume
-/
lemma intervalIntegrable_of_even₀ (h₁f : forall x, f x = f (-x))
    (h₂f : forall x, 0 < x -> IntervalIntegrable f volume 0 x)
    {t : Real} (ht : ‖f (min 0 t)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable f volume 0 t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [IntervalIntegrable.iff_comp_neg ht]
    conv => arg 1; intro t; rw [← h₁f]
    simp [h₂f (-t) (by simp [h])]
  · rw [h]
  · exact h₂f t h

/--
theorem `intervalIntegrable_of_even` / 定理 `intervalIntegrable_of_even`

English:
theorem intervalIntegrable_of_even
  proof: -- Split integral and apply lemma
  (intervalIntegrable_of_even₀ h₁f h₂f ha).symm.trans (b := 0)
    (intervalIntegrable_of_even₀ h₁f h₂f hb)

中文:
定理 intervalIntegrable_of_even
  证明: -- Split integral and apply lemma
  (intervalIntegrable_of_even₀ h₁f h₂f ha).symm.trans (b := 0)
    (intervalIntegrable_of_even₀ h₁f h₂f hb)

Depends on / 依赖: IntervalIntegrable, finiteness, volume
-/
theorem intervalIntegrable_of_even
    (h₁f : forall x, f x = f (-x)) (h₂f : forall x, 0 < x -> IntervalIntegrable f volume 0 x) {a b : Real}
    (ha : ‖f (min 0 a)‖ₑ != ∞ := by finiteness) (hb : ‖f (min 0 b)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable f volume a b :=
  -- Split integral and apply lemma
  (intervalIntegrable_of_even₀ h₁f h₂f ha).symm.trans (b := 0)
    (intervalIntegrable_of_even₀ h₁f h₂f hb)

/--
lemma `intervalIntegrable_of_odd₀` / 引理 `intervalIntegrable_of_odd₀`

English:
lemma intervalIntegrable_of_odd₀
  statement: (h₁f : forall x, -f x = f (-x))
  proof: by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [IntervalIntegrable.iff_comp_neg]
    conv => arg 1; intro t; rw [← h₁f]
    apply IntervalIntegrable.neg
    simp [h₂f (-t) (by simp [h])]
  · rw [h]
  · exact h₂f t h

中文:
引理 intervalIntegrable_of_odd₀
  结论: (h₁f : 对任意 x, -f x = f (-x))
  证明: by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [IntervalIntegrable.iff_comp_neg]
    conv => arg 1; intro t; rw [← h₁f]
    apply IntervalIntegrable.neg
    simp [h₂f (-t) (by simp [h])]
  · rw [h]
  · exact h₂f t h

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.iff_comp_neg, IntervalIntegrable.neg, finiteness, iff_comp_neg, lt_trichotomy, volume
-/
lemma intervalIntegrable_of_odd₀ (h₁f : forall x, -f x = f (-x))
    (h₂f : forall x, 0 < x -> IntervalIntegrable f volume 0 x) {t : Real}
    (ht : ‖f (min 0 t)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable f volume 0 t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [IntervalIntegrable.iff_comp_neg]
    conv => arg 1; intro t; rw [← h₁f]
    apply IntervalIntegrable.neg
    simp [h₂f (-t) (by simp [h])]
  · rw [h]
  · exact h₂f t h

/--
theorem `intervalIntegrable_of_odd` / 定理 `intervalIntegrable_of_odd`

English:
theorem intervalIntegrable_of_odd
  proof: -- Split integral and apply lemma
  (intervalIntegrable_of_odd₀ h₁f h₂f ha).symm.trans (intervalIntegrable_of_odd₀ h₁f h₂f hb)

中文:
定理 intervalIntegrable_of_odd
  证明: -- Split integral and apply lemma
  (intervalIntegrable_of_odd₀ h₁f h₂f ha).symm.trans (intervalIntegrable_of_odd₀ h₁f h₂f hb)

Depends on / 依赖: IntervalIntegrable, finiteness, volume
-/
theorem intervalIntegrable_of_odd
    (h₁f : forall x, -f x = f (-x)) (h₂f : forall x, 0 < x -> IntervalIntegrable f volume 0 x) {a b : Real}
    (ha : ‖f (min 0 a)‖ₑ != ∞ := by finiteness) (hb : ‖f (min 0 b)‖ₑ != ∞ := by finiteness) :
    IntervalIntegrable f volume a b :=
  -- Split integral and apply lemma
  (intervalIntegrable_of_odd₀ h₁f h₂f ha).symm.trans (intervalIntegrable_of_odd₀ h₁f h₂f hb)

end

/-!
## Limits of intervals
-/

/--
theorem `Filter.Tendsto.eventually_intervalIntegrable_ae` / 定理 `Filter.Tendsto.eventually_intervalIntegrable_ae`

English:
theorem Filter.Tendsto.eventually_intervalIntegrable_ae
  statement: {f : Real -> E} {μ : Measure Real}
  proof: have := (hf.integrableAtFilter_ae hfm hμ).eventually
((hu.Ioc hv).eventually this).and (hv.Ioc hu).eventually this

中文:
定理 Filter.Tendsto.eventually_intervalIntegrable_ae
  结论: {f : 实数 -> E} {μ : Measure 实数}
  证明: have := (hf.integrableAtFilter_ae hfm hμ).eventually
((hu.Ioc hv).eventually this).and (hv.Ioc hu).eventually this

Depends on / 依赖: eventually, hf.integrableAtFilter_ae, hu.Ioc, hv.Ioc, integrableAtFilter_ae
-/
theorem Filter.Tendsto.eventually_intervalIntegrable_ae {f : Real -> E} {μ : Measure Real}
    {l l' : Filter Real} (hfm : StronglyMeasurableAtFilter f l' μ) [TendstoIxxClass Ioc l l']
    [IsMeasurablyGenerated l'] (hμ : μ.FiniteAtFilter l') {c : E} (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    {u v : ι -> Real} {lt : Filter ι} (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    forallᶠ t in lt, IntervalIntegrable f μ (u t) (v t) :=
  have := (hf.integrableAtFilter_ae hfm hμ).eventually
((hu.Ioc hv).eventually this).and (hv.Ioc hu).eventually this

/--
theorem `Filter.Tendsto.eventually_intervalIntegrable` / 定理 `Filter.Tendsto.eventually_intervalIntegrable`

English:
theorem Filter.Tendsto.eventually_intervalIntegrable
  statement: {f : Real -> E} {μ : Measure Real} {l l' : Filter Real}
  proof: (hf.mono_left inf_le_left).eventually_intervalIntegrable_ae hfm hμ hu hv

中文:
定理 Filter.Tendsto.eventually_intervalIntegrable
  结论: {f : 实数 -> E} {μ : Measure 实数} {l l' : Filter 实数}
  证明: (hf.mono_left inf_le_left).eventually_intervalIntegrable_ae hfm hμ hu hv

Depends on / 依赖: eventually_intervalIntegrable_ae, hf.mono_left, inf_le_left, mono_left
-/
theorem Filter.Tendsto.eventually_intervalIntegrable {f : Real -> E} {μ : Measure Real} {l l' : Filter Real}
    (hfm : StronglyMeasurableAtFilter f l' μ) [TendstoIxxClass Ioc l l'] [IsMeasurablyGenerated l']
    (hμ : μ.FiniteAtFilter l') {c : E} (hf : Tendsto f l' (𝓝 c)) {u v : ι -> Real} {lt : Filter ι}
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) : forallᶠ t in lt, IntervalIntegrable f μ (u t) (v t) :=
  (hf.mono_left inf_le_left).eventually_intervalIntegrable_ae hfm hμ hu hv

/-!
### Interval integral: definition and basic properties

In this section we define `∫ x in a..b, f x ∂μ` as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`
and prove some basic properties.
-/

variable [NormedSpace Real E]

/--
Definition of `intervalIntegral` / `intervalIntegral` 的定义

English:
definition intervalIntegral
  signature: (f : Real -> E) (a b : Real) (μ : Measure Real)
  body: (∫ x in Ioc a b, f x ∂μ) - ∫ x in Ioc b a, f x ∂μ

@[inherit_doc intervalIntegral]
notation3"∫ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂"μ:70 => intervalIntegral r a b μ

中文:
定义 intervalIntegral
  签名: (f : 实数 -> E) (a b : 实数) (μ : Measure 实数)
  定义体: (∫ x in Ioc a b, f x ∂μ) - ∫ x in Ioc b a, f x ∂μ

@[inherit_doc intervalIntegral]
notation3"∫ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂"μ:70 => intervalIntegral r a b μ
-/
def intervalIntegral (f : Real -> E) (a b : Real) (μ : Measure Real) : E :=
  (∫ x in Ioc a b, f x ∂μ) - ∫ x in Ioc b a, f x ∂μ

@[inherit_doc intervalIntegral]
notation3"∫ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂"μ:70 => intervalIntegral r a b μ

/-- The interval integral `∫ x in a..b, f x` is defined
as `∫ x in Ioc a b, f x - ∫ x in Ioc b a, f x`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x`, otherwise it equals `-∫ x in Ioc b a, f x`. -/
notation3"∫ "(...)" in "a".."b", "r:60:(scoped f => intervalIntegral f a b volume) => r

namespace intervalIntegral

section Basic

variable {a b : Real} {f g : Real -> E} {μ : Measure Real}

@[simp]
/--
theorem `integral_zero` / 定理 `integral_zero`

English:
theorem integral_zero
  statement: (∫ _ in a..b, (0 : E) ∂μ) = 0
  proof: by simp [intervalIntegral]

中文:
定理 integral_zero
  结论: (∫ _ in a..b, (0 : E) ∂μ) = 0
  证明: by simp [intervalIntegral]

Depends on / 依赖: intervalIntegral
-/
theorem integral_zero : (∫ _ in a..b, (0 : E) ∂μ) = 0 := by simp [intervalIntegral]

/--
theorem `integral_of_le` / 定理 `integral_of_le`

English:
theorem integral_of_le
  given: (h : a <= b)
  statement: ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
  proof: by
  simp [intervalIntegral, h]

@[simp]

中文:
定理 integral_of_le
  条件: (h : a <= b)
  结论: ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
  证明: by
  simp [intervalIntegral, h]

@[simp]

Depends on / 依赖: intervalIntegral
-/
theorem integral_of_le (h : a <= b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ := by
  simp [intervalIntegral, h]

@[simp]
/--
theorem `integral_same` / 定理 `integral_same`

English:
theorem integral_same
  statement: ∫ x in a..a, f x ∂μ = 0
  proof: sub_self _

中文:
定理 integral_same
  结论: ∫ x in a..a, f x ∂μ = 0
  证明: sub_self _

Depends on / 依赖: sub_self
-/
theorem integral_same : ∫ x in a..a, f x ∂μ = 0 :=
  sub_self _

/--
theorem `integral_symm` / 定理 `integral_symm`

English:
theorem integral_symm
  given: (a b)
  statement: ∫ x in b..a, f x ∂μ = -∫ x in a..b, f x ∂μ
  proof: by
  simp only [intervalIntegral, neg_sub]

中文:
定理 integral_symm
  条件: (a b)
  结论: ∫ x in b..a, f x ∂μ = -∫ x in a..b, f x ∂μ
  证明: by
  simp only [intervalIntegral, neg_sub]

Depends on / 依赖: intervalIntegral, neg_sub
-/
theorem integral_symm (a b) : ∫ x in b..a, f x ∂μ = -∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, neg_sub]

/--
theorem `integral_of_ge` / 定理 `integral_of_ge`

English:
theorem integral_of_ge
  given: (h : b <= a)
  statement: ∫ x in a..b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ
  proof: by
  simp only [integral_symm b, integral_of_le h]

中文:
定理 integral_of_ge
  条件: (h : b <= a)
  结论: ∫ x in a..b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ
  证明: by
  simp only [integral_symm b, integral_of_le h]

Depends on / 依赖: integral_of_le, integral_symm
-/
theorem integral_of_ge (h : b <= a) : ∫ x in a..b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ := by
  simp only [integral_symm b, integral_of_le h]

/--
theorem `intervalIntegral_eq_integral_uIoc` / 定理 `intervalIntegral_eq_integral_uIoc`

English:
theorem intervalIntegral_eq_integral_uIoc
  given: (f : Real -> E) (a b : Real) (μ : Measure Real)
  proof: by
  split_ifs with h
  · simp only [integral_of_le h, uIoc_of_le h, one_smul]
  · simp only [integral_of_ge (not_le.1 h).le, uIoc_of_ge (not_le.1 h).le, neg_one_smul]

中文:
定理 intervalIntegral_eq_integral_uIoc
  条件: (f : 实数 -> E) (a b : 实数) (μ : Measure 实数)
  证明: by
  split_ifs with h
  · simp only [integral_of_le h, uIoc_of_le h, one_smul]
  · simp only [integral_of_ge (not_le.1 h).le, uIoc_of_ge (not_le.1 h).le, neg_one_smul]

Depends on / 依赖: integral_of_ge, integral_of_le, neg_one_smul, not_le, one_smul, split_ifs, uIoc_of_ge, uIoc_of_le
-/
theorem intervalIntegral_eq_integral_uIoc (f : Real -> E) (a b : Real) (μ : Measure Real) :
    ∫ x in a..b, f x ∂μ = (if a <= b then 1 else -1 : Real) • ∫ x in Ι a b, f x ∂μ := by
  split_ifs with h
  · simp only [integral_of_le h, uIoc_of_le h, one_smul]
  · simp only [integral_of_ge (not_le.1 h).le, uIoc_of_ge (not_le.1 h).le, neg_one_smul]

/--
theorem `norm_intervalIntegral_eq` / 定理 `norm_intervalIntegral_eq`

English:
theorem norm_intervalIntegral_eq
  given: (f : Real -> E) (a b : Real) (μ : Measure Real)
  proof: by
  simp_rw [intervalIntegral_eq_integral_uIoc, norm_smul]
  split_ifs <;> simp only [norm_neg, norm_one, one_mul]

中文:
定理 norm_intervalIntegral_eq
  条件: (f : 实数 -> E) (a b : 实数) (μ : Measure 实数)
  证明: by
  simp_rw [intervalIntegral_eq_integral_uIoc, norm_smul]
  split_ifs <;> simp only [norm_neg, norm_one, one_mul]

Depends on / 依赖: intervalIntegral_eq_integral_uIoc, norm_neg, norm_one, norm_smul, one_mul, simp_rw, split_ifs
-/
theorem norm_intervalIntegral_eq (f : Real -> E) (a b : Real) (μ : Measure Real) :
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := by
  simp_rw [intervalIntegral_eq_integral_uIoc, norm_smul]
  split_ifs <;> simp only [norm_neg, norm_one, one_mul]

/--
theorem `abs_intervalIntegral_eq` / 定理 `abs_intervalIntegral_eq`

English:
theorem abs_intervalIntegral_eq
  given: (f : Real -> Real) (a b : Real) (μ : Measure Real)
  proof: norm_intervalIntegral_eq f a b μ

中文:
定理 abs_intervalIntegral_eq
  条件: (f : 实数 -> 实数) (a b : 实数) (μ : Measure 实数)
  证明: norm_intervalIntegral_eq f a b μ

Depends on / 依赖: norm_intervalIntegral_eq
-/
theorem abs_intervalIntegral_eq (f : Real -> Real) (a b : Real) (μ : Measure Real) :
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
  norm_intervalIntegral_eq f a b μ

/--
theorem `integral_cases` / 定理 `integral_cases`

English:
theorem integral_cases
  given: (f : Real -> E) (a b)
  proof: by
  rw [intervalIntegral_eq_integral_uIoc]; split_ifs <;> simp

nonrec theorem integral_undef (h : ¬IntervalIntegrable f μ a b) : ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegrable_iff] at h
  rw [intervalIntegral_eq_integral_uIoc]; rw [integral_undef h]; rw [smul_zero]

中文:
定理 integral_cases
  条件: (f : 实数 -> E) (a b)
  证明: by
  rw [intervalIntegral_eq_integral_uIoc]; split_ifs <;> simp

nonrec theorem integral_undef (h : ¬IntervalIntegrable f μ a b) : ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegrable_iff] at h
  rw [intervalIntegral_eq_integral_uIoc]; rw [integral_undef h]; rw [smul_zero]

Depends on / 依赖: intervalIntegral_eq_integral_uIoc, split_ifs
-/
theorem integral_cases (f : Real -> E) (a b) :
    (∫ x in a..b, f x ∂μ) in ({∫ x in Ι a b, f x ∂μ, -∫ x in Ι a b, f x ∂μ} : Set E) := by
  rw [intervalIntegral_eq_integral_uIoc]; split_ifs <;> simp

nonrec theorem integral_undef (h : ¬IntervalIntegrable f μ a b) : ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegrable_iff] at h
  rw [intervalIntegral_eq_integral_uIoc]; rw [integral_undef h]; rw [smul_zero]

/--
theorem `intervalIntegrable_of_integral_ne_zero` / 定理 `intervalIntegrable_of_integral_ne_zero`

English:
theorem intervalIntegrable_of_integral_ne_zero
  statement: {a b : Real} {f : Real -> E} {μ : Measure Real}
  proof: not_imp_comm.1 integral_undef h

nonrec theorem integral_non_aestronglyMeasurable
    (hf : ¬AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegral_eq_integral_uIoc]; rw [integral_non_aestronglyMeasurable hf]; rw [smul_zero]

中文:
定理 intervalIntegrable_of_integral_ne_zero
  结论: {a b : 实数} {f : 实数 -> E} {μ : Measure 实数}
  证明: not_imp_comm.1 integral_undef h

nonrec theorem integral_non_aestronglyMeasurable
    (hf : ¬AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegral_eq_integral_uIoc]; rw [integral_non_aestronglyMeasurable hf]; rw [smul_zero]

Depends on / 依赖: integral_undef, not_imp_comm
-/
theorem intervalIntegrable_of_integral_ne_zero {a b : Real} {f : Real -> E} {μ : Measure Real}
    (h : (∫ x in a..b, f x ∂μ) != 0) : IntervalIntegrable f μ a b :=
  not_imp_comm.1 integral_undef h

nonrec theorem integral_non_aestronglyMeasurable
    (hf : ¬AEStronglyMeasurable f (μ.restrict (Ι a b))) :
    ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegral_eq_integral_uIoc]; rw [integral_non_aestronglyMeasurable hf]; rw [smul_zero]

/--
theorem `integral_non_aestronglyMeasurable_of_le` / 定理 `integral_non_aestronglyMeasurable_of_le`

English:
theorem integral_non_aestronglyMeasurable_of_le
  statement: (h : a <= b)
  proof: integral_non_aestronglyMeasurable by rwa [uIoc_of_le h]

中文:
定理 integral_non_aestronglyMeasurable_of_le
  结论: (h : a <= b)
  证明: integral_non_aestronglyMeasurable by rwa [uIoc_of_le h]

Depends on / 依赖: integral_non_aestronglyMeasurable, uIoc_of_le
-/
theorem integral_non_aestronglyMeasurable_of_le (h : a <= b)
    (hf : ¬AEStronglyMeasurable f (μ.restrict (Ioc a b))) : ∫ x in a..b, f x ∂μ = 0 :=
integral_non_aestronglyMeasurable by rwa [uIoc_of_le h]

/--
theorem `norm_integral_min_max` / 定理 `norm_integral_min_max`

English:
theorem norm_integral_min_max
  given: (f : Real -> E)
  proof: by
  cases le_total a b <;> simp [*, integral_symm a b]

中文:
定理 norm_integral_min_max
  条件: (f : 实数 -> E)
  证明: by
  cases le_total a b <;> simp [*, integral_symm a b]

Depends on / 依赖: integral_symm, le_total
-/
theorem norm_integral_min_max (f : Real -> E) :
    ‖∫ x in min a b..max a b, f x ∂μ‖ = ‖∫ x in a..b, f x ∂μ‖ := by
  cases le_total a b <;> simp [*, integral_symm a b]

/--
theorem `norm_integral_eq_norm_integral_uIoc` / 定理 `norm_integral_eq_norm_integral_uIoc`

English:
theorem norm_integral_eq_norm_integral_uIoc
  given: (f : Real -> E)
  proof: by
  rw [← norm_integral_min_max]; rw [integral_of_le min_le_max]; rw [uIoc]

中文:
定理 norm_integral_eq_norm_integral_uIoc
  条件: (f : 实数 -> E)
  证明: by
  rw [← norm_integral_min_max]; rw [integral_of_le min_le_max]; rw [uIoc]

Depends on / 依赖: integral_of_le, min_le_max, norm_integral_min_max
-/
theorem norm_integral_eq_norm_integral_uIoc (f : Real -> E) :
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := by
  rw [← norm_integral_min_max]; rw [integral_of_le min_le_max]; rw [uIoc]

/--
theorem `abs_integral_eq_abs_integral_uIoc` / 定理 `abs_integral_eq_abs_integral_uIoc`

English:
theorem abs_integral_eq_abs_integral_uIoc
  given: (f : Real -> Real)
  proof: norm_integral_eq_norm_integral_uIoc f

中文:
定理 abs_integral_eq_abs_integral_uIoc
  条件: (f : 实数 -> 实数)
  证明: norm_integral_eq_norm_integral_uIoc f

Depends on / 依赖: norm_integral_eq_norm_integral_uIoc
-/
theorem abs_integral_eq_abs_integral_uIoc (f : Real -> Real) :
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
  norm_integral_eq_norm_integral_uIoc f

/--
theorem `norm_integral_le_integral_norm_uIoc` / 定理 `norm_integral_le_integral_norm_uIoc`

English:
theorem norm_integral_le_integral_norm_uIoc
  statement: ‖∫ x in a..b, f x ∂μ‖ <= ∫ x in Ι a b, ‖f x‖ ∂μ
  proof: calc
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := norm_integral_eq_norm_integral_uIoc f
    _ <= ∫ x in Ι a b, ‖f x‖ ∂μ := norm_integral_le_integral_norm f

中文:
定理 norm_integral_le_integral_norm_uIoc
  结论: ‖∫ x in a..b, f x ∂μ‖ <= ∫ x in Ι a b, ‖f x‖ ∂μ
  证明: calc
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := norm_integral_eq_norm_integral_uIoc f
    _ <= ∫ x in Ι a b, ‖f x‖ ∂μ := norm_integral_le_integral_norm f

Depends on / 依赖: norm_integral_eq_norm_integral_uIoc, norm_integral_le_integral_norm
-/
theorem norm_integral_le_integral_norm_uIoc : ‖∫ x in a..b, f x ∂μ‖ <= ∫ x in Ι a b, ‖f x‖ ∂μ :=
  calc
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := norm_integral_eq_norm_integral_uIoc f
    _ <= ∫ x in Ι a b, ‖f x‖ ∂μ := norm_integral_le_integral_norm f

/--
theorem `norm_integral_le_abs_integral_norm` / 定理 `norm_integral_le_abs_integral_norm`

English:
theorem norm_integral_le_abs_integral_norm
  statement: ‖∫ x in a..b, f x ∂μ‖ <= |∫ x in a..b, ‖f x‖ ∂μ|
  proof: by
  simp only [← Real.norm_eq_abs, norm_integral_eq_norm_integral_uIoc]
  exact le_trans (norm_integral_le_integral_norm _) (le_abs_self _)

中文:
定理 norm_integral_le_abs_integral_norm
  结论: ‖∫ x in a..b, f x ∂μ‖ <= |∫ x in a..b, ‖f x‖ ∂μ|
  证明: by
  simp only [← Real.norm_eq_abs, norm_integral_eq_norm_integral_uIoc]
  exact le_trans (norm_integral_le_integral_norm _) (le_abs_self _)

Depends on / 依赖: Real.norm_eq_abs, le_abs_self, le_trans, norm_eq_abs, norm_integral_eq_norm_integral_uIoc, norm_integral_le_integral_norm
-/
theorem norm_integral_le_abs_integral_norm : ‖∫ x in a..b, f x ∂μ‖ <= |∫ x in a..b, ‖f x‖ ∂μ| := by
  simp only [← Real.norm_eq_abs, norm_integral_eq_norm_integral_uIoc]
  exact le_trans (norm_integral_le_integral_norm _) (le_abs_self _)

/--
theorem `norm_integral_le_integral_norm` / 定理 `norm_integral_le_integral_norm`

English:
theorem norm_integral_le_integral_norm
  given: (h : a <= b)
  proof: norm_integral_le_integral_norm_uIoc.trans_eq by rw [uIoc_of_le h, integral_of_le h]

中文:
定理 norm_integral_le_integral_norm
  条件: (h : a <= b)
  证明: norm_integral_le_integral_norm_uIoc.trans_eq by rw [uIoc_of_le h, integral_of_le h]

Depends on / 依赖: integral_of_le, norm_integral_le_integral_norm_uIoc, norm_integral_le_integral_norm_uIoc.trans_eq, trans_eq, uIoc_of_le
-/
theorem norm_integral_le_integral_norm (h : a <= b) :
    ‖∫ x in a..b, f x ∂μ‖ <= ∫ x in a..b, ‖f x‖ ∂μ :=
norm_integral_le_integral_norm_uIoc.trans_eq by rw [uIoc_of_le h, integral_of_le h]

/--
theorem `norm_integral_le_abs_of_norm_le` / 定理 `norm_integral_le_abs_of_norm_le`

English:
theorem norm_integral_le_abs_of_norm_le
  statement: {g : Real -> Real} (h : forallᵐ t ∂μ.restrict <| Ι a b, ‖f t‖ <= g t)
  proof: by
  rw [norm_intervalIntegral_eq]; rw [abs_intervalIntegral_eq]
  exact (norm_integral_le_of_norm_le hbound.def' h).trans (le_abs_self _)

中文:
定理 norm_integral_le_abs_of_norm_le
  结论: {g : 实数 -> 实数} (h : 对任意ᵐ t ∂μ.restrict <| Ι a b, ‖f t‖ <= g t)
  证明: by
  rw [norm_intervalIntegral_eq]; rw [abs_intervalIntegral_eq]
  exact (norm_integral_le_of_norm_le hbound.def' h).trans (le_abs_self _)

Depends on / 依赖: abs_intervalIntegral_eq, hbound, hbound.def, le_abs_self, norm_integral_le_of_norm_le, norm_intervalIntegral_eq
-/
theorem norm_integral_le_abs_of_norm_le {g : Real -> Real} (h : forallᵐ t ∂μ.restrict <| Ι a b, ‖f t‖ <= g t)
    (hbound : IntervalIntegrable g μ a b) : ‖∫ t in a..b, f t ∂μ‖ <= |∫ t in a..b, g t ∂μ| := by
  rw [norm_intervalIntegral_eq]; rw [abs_intervalIntegral_eq]
  exact (norm_integral_le_of_norm_le hbound.def' h).trans (le_abs_self _)

/--
theorem `norm_integral_le_of_norm_le` / 定理 `norm_integral_le_of_norm_le`

English:
theorem norm_integral_le_of_norm_le
  statement: {g : Real -> Real} (hab : a <= b)
  proof: by
  simp only [integral_of_le hab, ← ae_restrict_iff' measurableSet_Ioc] at *
  exact MeasureTheory.norm_integral_le_of_norm_le hbound.1 h

中文:
定理 norm_integral_le_of_norm_le
  结论: {g : 实数 -> 实数} (hab : a <= b)
  证明: by
  simp only [integral_of_le hab, ← ae_restrict_iff' measurableSet_Ioc] at *
  exact MeasureTheory.norm_integral_le_of_norm_le hbound.1 h

Depends on / 依赖: MeasureTheory, MeasureTheory.norm_integral_le_of_norm_le, ae_restrict_iff, hbound, integral_of_le, measurableSet_Ioc, norm_integral_le_of_norm_le
-/
theorem norm_integral_le_of_norm_le {g : Real -> Real} (hab : a <= b)
    (h : forallᵐ t ∂μ, t in Set.Ioc a b -> ‖f t‖ <= g t) (hbound : IntervalIntegrable g μ a b) :
    ‖∫ t in a..b, f t ∂μ‖ <= ∫ t in a..b, g t ∂μ := by
  simp only [integral_of_le hab, ← ae_restrict_iff' measurableSet_Ioc] at *
  exact MeasureTheory.norm_integral_le_of_norm_le hbound.1 h

/--
theorem `norm_integral_le_of_norm_le_const_ae` / 定理 `norm_integral_le_of_norm_le_const_ae`

English:
theorem norm_integral_le_of_norm_le_const_ae
  statement: {a b C : Real} {f : Real -> E}
  proof: by
  rw [norm_integral_eq_norm_integral_uIoc]
  convert! norm_setIntegral_le_of_norm_le_const_ae' _ h using 1
  · rw [uIoc, Real.volume_real_Ioc_of_le inf_le_sup, max_sub_min_eq_abs]
  · simp [uIoc, Real.volume_Ioc]

中文:
定理 norm_integral_le_of_norm_le_const_ae
  结论: {a b C : 实数} {f : 实数 -> E}
  证明: by
  rw [norm_integral_eq_norm_integral_uIoc]
  convert! norm_setIntegral_le_of_norm_le_const_ae' _ h using 1
  · rw [uIoc, Real.volume_real_Ioc_of_le inf_le_sup, max_sub_min_eq_abs]
  · simp [uIoc, Real.volume_Ioc]

Depends on / 依赖: Real.volume_Ioc, Real.volume_real_Ioc_of_le, convert, inf_le_sup, max_sub_min_eq_abs, norm_integral_eq_norm_integral_uIoc, norm_setIntegral_le_of_norm_le_const_ae, volume_Ioc, volume_real_Ioc_of_le
-/
theorem norm_integral_le_of_norm_le_const_ae {a b C : Real} {f : Real -> E}
    (h : forallᵐ x, x in Ι a b -> ‖f x‖ <= C) : ‖∫ x in a..b, f x‖ <= C * |b - a| := by
  rw [norm_integral_eq_norm_integral_uIoc]
  convert! norm_setIntegral_le_of_norm_le_const_ae' _ h using 1
  · rw [uIoc, Real.volume_real_Ioc_of_le inf_le_sup, max_sub_min_eq_abs]
  · simp [uIoc, Real.volume_Ioc]

/--
theorem `norm_integral_le_of_norm_le_const` / 定理 `norm_integral_le_of_norm_le_const`

English:
theorem norm_integral_le_of_norm_le_const
  given: {a b C : Real} {f : Real -> E} (h : forall x in Ι a b, ‖f x‖ <= C)
  proof: norm_integral_le_of_norm_le_const_ae Eventually.of_forall h

@[simp]
nonrec theorem integral_add (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    ∫ x in a..b, f x + g x ∂μ = (∫ x in a..b, f x ∂μ) + ∫ x in a..b, g x ∂μ := by
  simp only [intervalIntegral_eq_integral_uIoc, int

中文:
定理 norm_integral_le_of_norm_le_const
  条件: {a b C : 实数} {f : 实数 -> E} (h : 对任意 x in Ι a b, ‖f x‖ <= C)
  证明: norm_integral_le_of_norm_le_const_ae Eventually.of_forall h

@[simp]
nonrec theorem integral_add (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    ∫ x in a..b, f x + g x ∂μ = (∫ x in a..b, f x ∂μ) + ∫ x in a..b, g x ∂μ := by
  simp only [intervalIntegral_eq_integral_uIoc, int

Depends on / 依赖: Eventually, Eventually.of_forall, norm_integral_le_of_norm_le_const_ae, of_forall
-/
theorem norm_integral_le_of_norm_le_const {a b C : Real} {f : Real -> E} (h : forall x in Ι a b, ‖f x‖ <= C) :
    ‖∫ x in a..b, f x‖ <= C * |b - a| :=
norm_integral_le_of_norm_le_const_ae Eventually.of_forall h

@[simp]
nonrec theorem integral_add (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    ∫ x in a..b, f x + g x ∂μ = (∫ x in a..b, f x ∂μ) + ∫ x in a..b, g x ∂μ := by
  simp only [intervalIntegral_eq_integral_uIoc, integral_add hf.def' hg.def', smul_add]

nonrec theorem integral_finsetSum {ι} {s : Finset ι} {f : ι -> Real -> E}
    (h : forall i in s, IntervalIntegrable (f i) μ a b) :
    ∫ x in a..b, ∑ i in s, f i x ∂μ = ∑ i in s, ∫ x in a..b, f i x ∂μ := by
  simp only [intervalIntegral_eq_integral_uIoc, integral_finsetSum s fun i hi => (h i hi).def',
    Finset.smul_sum]

@[deprecated (since := "2026-04-08")] alias integral_finset_sum := integral_finsetSum

@[simp]
nonrec theorem integral_neg : ∫ x in a..b, -f x ∂μ = -∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, integral_neg]; abel

@[simp]
/--
theorem `integral_sub` / 定理 `integral_sub`

English:
theorem integral_sub
  given: (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b)
  proof: by
  simpa only [sub_eq_add_neg] using! (integral_add hf hg.neg).trans (congr_arg _ integral_neg)

中文:
定理 integral_sub
  条件: (hf : 整数erval整数egrable f μ a b) (hg : 整数erval整数egrable g μ a b)
  证明: by
  simpa only [sub_eq_add_neg] using! (integral_add hf hg.neg).trans (congr_arg _ integral_neg)

Depends on / 依赖: congr_arg, hg.neg, integral_add, integral_neg, sub_eq_add_neg
-/
theorem integral_sub (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    ∫ x in a..b, f x - g x ∂μ = (∫ x in a..b, f x ∂μ) - ∫ x in a..b, g x ∂μ := by
  simpa only [sub_eq_add_neg] using! (integral_add hf hg.neg).trans (congr_arg _ integral_neg)

/-- Compatibility with scalar multiplication. Note this assumes `𝕜` is a division ring in order to
ensure that for `c ≠ 0`, `c • f` is integrable iff `f` is. For scalar multiplication by more
general rings assuming integrability, see `IntervalIntegrable.integral_smul`. -/
@[simp]
nonrec theorem integral_smul [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [SMulCommClass Real 𝕜 E] (r : 𝕜) (f : Real -> E) :
    ∫ x in a..b, r • f x ∂μ = r • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, integral_smul, smul_sub]

/--
theorem `_root_.IntervalIntegrable.integral_smul` / 定理 `_root_.IntervalIntegrable.integral_smul`

English:
theorem _root_.IntervalIntegrable.integral_smul
  proof: by
  simp only [intervalIntegral, smul_sub, hf.1.integral_smul, hf.2.integral_smul]

@[simp]
nonrec theorem integral_smul_const [CompleteSpace E]
    {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (f : Real -> 𝕜) (c : E) :
    ∫ x in a..b, f x • c ∂μ = (∫ x in a..b, f x ∂μ) • c := by
  simp only [interval

中文:
定理 _root_.IntervalIntegrable.integral_smul
  证明: by
  simp only [intervalIntegral, smul_sub, hf.1.integral_smul, hf.2.integral_smul]

@[simp]
nonrec theorem integral_smul_const [CompleteSpace E]
    {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (f : Real -> 𝕜) (c : E) :
    ∫ x in a..b, f x • c ∂μ = (∫ x in a..b, f x ∂μ) • c := by
  simp only [interval

Depends on / 依赖: integral_smul, intervalIntegral, smul_sub
-/
theorem _root_.IntervalIntegrable.integral_smul
    {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E] [SMulCommClass Real R E]
    {f : Real -> E} (r : R) (hf : IntervalIntegrable f μ a b) :
    ∫ x in a..b, r • f x ∂μ = r • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, smul_sub, hf.1.integral_smul, hf.2.integral_smul]

@[simp]
nonrec theorem integral_smul_const [CompleteSpace E]
    {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (f : Real -> 𝕜) (c : E) :
    ∫ x in a..b, f x • c ∂μ = (∫ x in a..b, f x ∂μ) • c := by
  simp only [intervalIntegral_eq_integral_uIoc, integral_smul_const, smul_assoc]

@[simp]
/--
theorem `integral_const_mul` / 定理 `integral_const_mul`

English:
theorem integral_const_mul
  given: [NormedDivisionRing 𝕜] [NormedAlgebra Real 𝕜] (r : 𝕜) (f : Real -> 𝕜)
  proof: integral_smul r f

@[simp]

中文:
定理 integral_const_mul
  条件: [NormedDivisionRing 𝕜] [NormedAlgebra 实数 𝕜] (r : 𝕜) (f : 实数 -> 𝕜)
  证明: integral_smul r f

@[simp]

Depends on / 依赖: integral_smul
-/
theorem integral_const_mul [NormedDivisionRing 𝕜] [NormedAlgebra Real 𝕜] (r : 𝕜) (f : Real -> 𝕜) :
    ∫ x in a..b, r * f x ∂μ = r * ∫ x in a..b, f x ∂μ :=
  integral_smul r f

@[simp]
/--
theorem `integral_mul_const` / 定理 `integral_mul_const`

English:
theorem integral_mul_const
  given: {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : Real -> 𝕜)
  proof: by
  simpa only [mul_comm r] using integral_const_mul r f

@[simp]

中文:
定理 integral_mul_const
  条件: {𝕜 : 类型} [RCLike 𝕜] (r : 𝕜) (f : 实数 -> 𝕜)
  证明: by
  simpa only [mul_comm r] using integral_const_mul r f

@[simp]

Depends on / 依赖: integral_const_mul, mul_comm
-/
theorem integral_mul_const {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : Real -> 𝕜) :
    ∫ x in a..b, f x * r ∂μ = (∫ x in a..b, f x ∂μ) * r := by
  simpa only [mul_comm r] using integral_const_mul r f

@[simp]
/--
theorem `integral_div` / 定理 `integral_div`

English:
theorem integral_div
  given: {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : Real -> 𝕜)
  proof: by
  simpa only [div_eq_mul_inv] using integral_mul_const r⁻¹ f

中文:
定理 integral_div
  条件: {𝕜 : 类型} [RCLike 𝕜] (r : 𝕜) (f : 实数 -> 𝕜)
  证明: by
  simpa only [div_eq_mul_inv] using integral_mul_const r⁻¹ f

Depends on / 依赖: div_eq_mul_inv, integral_mul_const
-/
theorem integral_div {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : Real -> 𝕜) :
    ∫ x in a..b, f x / r ∂μ = (∫ x in a..b, f x ∂μ) / r := by
  simpa only [div_eq_mul_inv] using integral_mul_const r⁻¹ f

/--
theorem `integral_const'` / 定理 `integral_const'`

English:
theorem integral_const'
  given: [CompleteSpace E] (c : E)
  proof: by
  simp only [measureReal_def, intervalIntegral, setIntegral_const, sub_smul]

@[simp]

中文:
定理 integral_const'
  条件: [CompleteSpace E] (c : E)
  证明: by
  simp only [measureReal_def, intervalIntegral, setIntegral_const, sub_smul]

@[simp]

Depends on / 依赖: intervalIntegral, measureReal_def, setIntegral_const, sub_smul
-/
theorem integral_const' [CompleteSpace E] (c : E) :
    ∫ _ in a..b, c ∂μ = (μ.real (Ioc a b) - μ.real (Ioc b a)) • c := by
  simp only [measureReal_def, intervalIntegral, setIntegral_const, sub_smul]

@[simp]
/--
theorem `integral_const` / 定理 `integral_const`

English:
theorem integral_const
  given: [CompleteSpace E] (c : E)
  statement: ∫ _ in a..b, c = (b - a) • c
  proof: by
  simp only [integral_const', Real.volume_Ioc, ENNReal.toReal_ofReal', ← neg_sub b,
    max_zero_sub_eq_self, measureReal_def]

nonrec theorem integral_smul_measure (c : Real>=0∞) :
    ∫ x in a..b, f x ∂c • μ = c.toReal • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, Measure.restrict_

中文:
定理 integral_const
  条件: [CompleteSpace E] (c : E)
  结论: ∫ _ in a..b, c = (b - a) • c
  证明: by
  simp only [integral_const', Real.volume_Ioc, ENNReal.toReal_ofReal', ← neg_sub b,
    max_zero_sub_eq_self, measureReal_def]

nonrec theorem integral_smul_measure (c : Real>=0∞) :
    ∫ x in a..b, f x ∂c • μ = c.toReal • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, Measure.restrict_

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, Real.volume_Ioc, integral_const, max_zero_sub_eq_self, measureReal_def, neg_sub, toReal_ofReal, volume_Ioc
-/
theorem integral_const [CompleteSpace E] (c : E) : ∫ _ in a..b, c = (b - a) • c := by
  simp only [integral_const', Real.volume_Ioc, ENNReal.toReal_ofReal', ← neg_sub b,
    max_zero_sub_eq_self, measureReal_def]

nonrec theorem integral_smul_measure (c : Real>=0∞) :
    ∫ x in a..b, f x ∂c • μ = c.toReal • ∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, Measure.restrict_smul, integral_smul_measure, smul_sub]

end Basic

-- TODO: add `Complex.ofReal` version of `_root_.integral_ofReal`

nonrec theorem _root_.RCLike.intervalIntegral_ofReal {𝕜 : Type*} [RCLike 𝕜] {a b : Real}
    {μ : Measure Real} {f : Real -> Real} : (∫ x in a..b, (f x : 𝕜) ∂μ) = ↑(∫ x in a..b, f x ∂μ) := by
  simp only [intervalIntegral, integral_ofReal, RCLike.ofReal_sub]

nonrec theorem integral_ofReal {a b : Real} {μ : Measure Real} {f : Real -> Real} :
    (∫ x in a..b, (f x : Complex) ∂μ) = ↑(∫ x in a..b, f x ∂μ) :=
  RCLike.intervalIntegral_ofReal

section ContinuousLinearMap

variable {a b : Real} {μ : Measure Real} {f : Real -> E}
variable [RCLike 𝕜] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open ContinuousLinearMap

/--
theorem `_root_.ContinuousLinearMap.intervalIntegral_apply` / 定理 `_root_.ContinuousLinearMap.intervalIntegral_apply`

English:
theorem _root_.ContinuousLinearMap.intervalIntegral_apply
  statement: {a b : Real} {φ : Real -> F ->L[𝕜] E}
  proof: by
  simp_rw [intervalIntegral_eq_integral_uIoc, ← integral_apply hφ.def' v, smul_apply]

中文:
定理 _root_.ContinuousLinearMap.intervalIntegral_apply
  结论: {a b : 实数} {φ : 实数 -> F ->L[𝕜] E}
  证明: by
  simp_rw [intervalIntegral_eq_integral_uIoc, ← integral_apply hφ.def' v, smul_apply]

Depends on / 依赖: integral_apply, intervalIntegral_eq_integral_uIoc, simp_rw, smul_apply
-/
theorem _root_.ContinuousLinearMap.intervalIntegral_apply {a b : Real} {φ : Real -> F ->L[𝕜] E}
    (hφ : IntervalIntegrable φ μ a b) (v : F) :
    (∫ x in a..b, φ x ∂μ) v = ∫ x in a..b, φ x v ∂μ := by
  simp_rw [intervalIntegral_eq_integral_uIoc, ← integral_apply hφ.def' v, smul_apply]

variable [NormedSpace Real F] [CompleteSpace F]

/--
theorem `_root_.ContinuousLinearMap.intervalIntegral_comp_comm` / 定理 `_root_.ContinuousLinearMap.intervalIntegral_comp_comm`

English:
theorem _root_.ContinuousLinearMap.intervalIntegral_comp_comm
  statement: [CompleteSpace E] (L : E ->L[𝕜] F)
  proof: by
  simp_rw [intervalIntegral, L.integral_comp_comm hf.1, L.integral_comp_comm hf.2, L.map_sub]

中文:
定理 _root_.ContinuousLinearMap.intervalIntegral_comp_comm
  结论: [CompleteSpace E] (L : E ->L[𝕜] F)
  证明: by
  simp_rw [intervalIntegral, L.integral_comp_comm hf.1, L.integral_comp_comm hf.2, L.map_sub]

Depends on / 依赖: L.integral_comp_comm, L.map_sub, integral_comp_comm, intervalIntegral, map_sub, simp_rw
-/
theorem _root_.ContinuousLinearMap.intervalIntegral_comp_comm [CompleteSpace E] (L : E ->L[𝕜] F)
    (hf : IntervalIntegrable f μ a b) : (∫ x in a..b, L (f x) ∂μ) = L (∫ x in a..b, f x ∂μ) := by
  simp_rw [intervalIntegral, L.integral_comp_comm hf.1, L.integral_comp_comm hf.2, L.map_sub]

end ContinuousLinearMap

section LinearIsometry

variable {a b : Real} {μ : Measure Real} {f : Real -> E} [RCLike 𝕜]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

variable [NormedSpace Real F] [CompleteSpace E] [CompleteSpace F]

/--
theorem `_root_.LinearIsometry.intervalIntegral_comp_comm` / 定理 `_root_.LinearIsometry.intervalIntegral_comp_comm`

English:
theorem _root_.LinearIsometry.intervalIntegral_comp_comm
  given: (L : E ->ₗᵢ[𝕜] F) (f : Real -> E)
  proof: by
  simp_rw [intervalIntegral, L.integral_comp_comm, L.map_sub]

中文:
定理 _root_.LinearIsometry.intervalIntegral_comp_comm
  条件: (L : E ->ₗᵢ[𝕜] F) (f : 实数 -> E)
  证明: by
  simp_rw [intervalIntegral, L.integral_comp_comm, L.map_sub]

Depends on / 依赖: L.integral_comp_comm, L.map_sub, integral_comp_comm, intervalIntegral, map_sub, simp_rw
-/
theorem _root_.LinearIsometry.intervalIntegral_comp_comm (L : E ->ₗᵢ[𝕜] F) (f : Real -> E) :
    ∫ x in a..b, L (f x) ∂μ = L (∫ x in a..b, f x ∂μ) := by
  simp_rw [intervalIntegral, L.integral_comp_comm, L.map_sub]

end LinearIsometry

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : Real -> 𝕜} {a b : Real} {μ : Measure Real}

/--
theorem `intervalIntegral_re` / 定理 `intervalIntegral_re`

English:
theorem intervalIntegral_re
  given: (hf : IntervalIntegrable f μ a b)
  proof: RCLike.reCLM.intervalIntegral_comp_comm hf

中文:
定理 intervalIntegral_re
  条件: (hf : 整数erval整数egrable f μ a b)
  证明: RCLike.reCLM.intervalIntegral_comp_comm hf

Depends on / 依赖: RCLike, RCLike.reCLM.intervalIntegral_comp_comm, intervalIntegral_comp_comm
-/
theorem intervalIntegral_re (hf : IntervalIntegrable f μ a b) :
    ∫ x in a..b, RCLike.re (f x) ∂μ = RCLike.re (∫ x in a..b, f x ∂μ) :=
  RCLike.reCLM.intervalIntegral_comp_comm hf

/--
theorem `intervalIntegral_im` / 定理 `intervalIntegral_im`

English:
theorem intervalIntegral_im
  given: (hf : IntervalIntegrable f μ a b)
  proof: RCLike.imCLM.intervalIntegral_comp_comm hf

中文:
定理 intervalIntegral_im
  条件: (hf : 整数erval整数egrable f μ a b)
  证明: RCLike.imCLM.intervalIntegral_comp_comm hf

Depends on / 依赖: RCLike, RCLike.imCLM.intervalIntegral_comp_comm, intervalIntegral_comp_comm
-/
theorem intervalIntegral_im (hf : IntervalIntegrable f μ a b) :
    ∫ x in a..b, RCLike.im (f x) ∂μ = RCLike.im (∫ x in a..b, f x ∂μ) :=
  RCLike.imCLM.intervalIntegral_comp_comm hf

open scoped ComplexConjugate in
/--
theorem `intervalIntegral_conj` / 定理 `intervalIntegral_conj`

English:
theorem intervalIntegral_conj
  statement: ∫ x in a..b, conj (f x) ∂μ = conj (∫ x in a..b, f x ∂μ)
  proof: RCLike.conjLIE.toLinearIsometry.intervalIntegral_comp_comm f

中文:
定理 intervalIntegral_conj
  结论: ∫ x in a..b, conj (f x) ∂μ = conj (∫ x in a..b, f x ∂μ)
  证明: RCLike.conjLIE.toLinearIsometry.intervalIntegral_comp_comm f

Depends on / 依赖: RCLike, RCLike.conjLIE.toLinearIsometry.intervalIntegral_comp_comm, conjLIE, intervalIntegral_comp_comm, toLinearIsometry
-/
theorem intervalIntegral_conj : ∫ x in a..b, conj (f x) ∂μ = conj (∫ x in a..b, f x ∂μ) :=
  RCLike.conjLIE.toLinearIsometry.intervalIntegral_comp_comm f

end RCLike

/-!
## Basic arithmetic
Includes addition, scalar multiplication and affine transformations.
-/
section Comp

variable {a b c d : Real} (f : Real -> E)

@[simp]
/--
theorem `integral_comp_mul_right` / 定理 `integral_comp_mul_right`

English:
theorem integral_comp_mul_right
  given: (hc : c != 0)
  proof: by
  have A : MeasurableEmbedding fun x => x * c :=
    (Homeomorph.mulRight₀ c hc).isClosedEmbedding.measurableEmbedding
  conv_rhs => rw [← Real.smul_map_volume_mul_right hc]
  simp_rw [integral_smul_measure, intervalIntegral, A.setIntegral_map,
    ENNReal.toReal_ofReal (abs_nonneg c)]
  rcases h

中文:
定理 integral_comp_mul_right
  条件: (hc : c != 0)
  证明: by
  have A : MeasurableEmbedding fun x => x * c :=
    (Homeomorph.mulRight₀ c hc).isClosedEmbedding.measurableEmbedding
  conv_rhs => rw [← Real.smul_map_volume_mul_right hc]
  simp_rw [integral_smul_measure, intervalIntegral, A.setIntegral_map,
    ENNReal.toReal_ofReal (abs_nonneg c)]
  rcases h

Depends on / 依赖: A.setIntegral_map, ENNReal, ENNReal.toReal_ofReal, Homeomorph, Homeomorph.mulRight, Ico_ae_eq_Ioc, MeasurableEmbedding, Measure, Measure.restrict_congr_set, Real.smul_map_volume_mul_right, abs_nonneg, abs_of_neg, abs_of_pos, conv_rhs, hc.lt_or_gt, integral_smul_measure, intervalIntegral, isClosedEmbedding, isClosedEmbedding.measurableEmbedding, lt_or_gt
-/
theorem integral_comp_mul_right (hc : c != 0) :
    (∫ x in a..b, f (x * c)) = c⁻¹ • ∫ x in a * c..b * c, f x := by
  have A : MeasurableEmbedding fun x => x * c :=
    (Homeomorph.mulRight₀ c hc).isClosedEmbedding.measurableEmbedding
  conv_rhs => rw [← Real.smul_map_volume_mul_right hc]
  simp_rw [integral_smul_measure, intervalIntegral, A.setIntegral_map,
    ENNReal.toReal_ofReal (abs_nonneg c)]
  rcases hc.lt_or_gt with h | h
  · simp [h, mul_div_cancel_right₀, hc, abs_of_neg,
      Measure.restrict_congr_set (α := Real) (μ := volume) Ico_ae_eq_Ioc]
  · simp [h, mul_div_cancel_right₀, hc, abs_of_pos]

@[simp]
/--
theorem `smul_integral_comp_mul_right` / 定理 `smul_integral_comp_mul_right`

English:
theorem smul_integral_comp_mul_right
  given: (c)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_right]

@[simp]

中文:
定理 smul_integral_comp_mul_right
  条件: (c)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_right]

@[simp]

Depends on / 依赖: integral_comp_mul_right
-/
theorem smul_integral_comp_mul_right (c) :
    (c • ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_right]

@[simp]
/--
theorem `integral_comp_mul_left` / 定理 `integral_comp_mul_left`

English:
theorem integral_comp_mul_left
  given: (hc : c != 0)
  proof: by
  simpa only [mul_comm c] using integral_comp_mul_right f hc

@[simp]

中文:
定理 integral_comp_mul_left
  条件: (hc : c != 0)
  证明: by
  simpa only [mul_comm c] using integral_comp_mul_right f hc

@[simp]

Depends on / 依赖: integral_comp_mul_right, mul_comm
-/
theorem integral_comp_mul_left (hc : c != 0) :
    (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ x in c * a..c * b, f x := by
  simpa only [mul_comm c] using integral_comp_mul_right f hc

@[simp]
/--
theorem `smul_integral_comp_mul_left` / 定理 `smul_integral_comp_mul_left`

English:
theorem smul_integral_comp_mul_left
  given: (c)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_left]

@[simp]

中文:
定理 smul_integral_comp_mul_left
  条件: (c)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_left]

@[simp]

Depends on / 依赖: integral_comp_mul_left
-/
theorem smul_integral_comp_mul_left (c) :
    (c • ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_left]

@[simp]
/--
theorem `integral_comp_div` / 定理 `integral_comp_div`

English:
theorem integral_comp_div
  given: (hc : c != 0)
  proof: by
  simpa only [inv_inv] using! integral_comp_mul_right f (inv_ne_zero hc)

@[simp]

中文:
定理 integral_comp_div
  条件: (hc : c != 0)
  证明: by
  simpa only [inv_inv] using! integral_comp_mul_right f (inv_ne_zero hc)

@[simp]

Depends on / 依赖: integral_comp_mul_right, inv_inv, inv_ne_zero
-/
theorem integral_comp_div (hc : c != 0) :
    (∫ x in a..b, f (x / c)) = c • ∫ x in a / c..b / c, f x := by
  simpa only [inv_inv] using! integral_comp_mul_right f (inv_ne_zero hc)

@[simp]
/--
theorem `inv_smul_integral_comp_div` / 定理 `inv_smul_integral_comp_div`

English:
theorem inv_smul_integral_comp_div
  given: (c)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div]

@[simp]

中文:
定理 inv_smul_integral_comp_div
  条件: (c)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div]

@[simp]

Depends on / 依赖: integral_comp_div
-/
theorem inv_smul_integral_comp_div (c) :
    (c⁻¹ • ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div]

@[simp]
/--
theorem `integral_comp_add_right` / 定理 `integral_comp_add_right`

English:
theorem integral_comp_add_right
  given: (d)
  statement: (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x
  proof: have A : MeasurableEmbedding fun x => x + d :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  calc
    (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x ∂Measure.map (fun x => x + d) volume := by
      simp [intervalIntegral, A.setIntegral_map]
    _ = ∫ x in a + d..b + d, f x

中文:
定理 integral_comp_add_right
  条件: (d)
  结论: (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x
  证明: have A : MeasurableEmbedding fun x => x + d :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  calc
    (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x ∂Measure.map (fun x => x + d) volume := by
      simp [intervalIntegral, A.setIntegral_map]
    _ = ∫ x in a + d..b + d, f x

Depends on / 依赖: A.setIntegral_map, Homeomorph, Homeomorph.addRight, MeasurableEmbedding, Measure, Measure.map, addRight, intervalIntegral, isClosedEmbedding, isClosedEmbedding.measurableEmbedding, map_add_right_eq_self, measurableEmbedding, setIntegral_map, volume
-/
theorem integral_comp_add_right (d) : (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x :=
  have A : MeasurableEmbedding fun x => x + d :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  calc
    (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x ∂Measure.map (fun x => x + d) volume := by
      simp [intervalIntegral, A.setIntegral_map]
    _ = ∫ x in a + d..b + d, f x := by rw [map_add_right_eq_self]

@[simp]
nonrec theorem integral_comp_add_left (d) :
    (∫ x in a..b, f (d + x)) = ∫ x in d + a..d + b, f x := by
  simpa only [add_comm d] using integral_comp_add_right f d

@[simp]
/--
theorem `integral_comp_mul_add` / 定理 `integral_comp_mul_add`

English:
theorem integral_comp_mul_add
  given: (hc : c != 0) (d)
  proof: by
  rw [← integral_comp_add_right]; rw [← integral_comp_mul_left _ hc]

@[simp]

中文:
定理 integral_comp_mul_add
  条件: (hc : c != 0) (d)
  证明: by
  rw [← integral_comp_add_right]; rw [← integral_comp_mul_left _ hc]

@[simp]

Depends on / 依赖: integral_comp_add_right, integral_comp_mul_left
-/
theorem integral_comp_mul_add (hc : c != 0) (d) :
    (∫ x in a..b, f (c * x + d)) = c⁻¹ • ∫ x in c * a + d..c * b + d, f x := by
  rw [← integral_comp_add_right]; rw [← integral_comp_mul_left _ hc]

@[simp]
/--
theorem `smul_integral_comp_mul_add` / 定理 `smul_integral_comp_mul_add`

English:
theorem smul_integral_comp_mul_add
  given: (c d)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_add]

@[simp]

中文:
定理 smul_integral_comp_mul_add
  条件: (c d)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_add]

@[simp]

Depends on / 依赖: integral_comp_mul_add
-/
theorem smul_integral_comp_mul_add (c d) :
    (c • ∫ x in a..b, f (c * x + d)) = ∫ x in c * a + d..c * b + d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_add]

@[simp]
/--
theorem `integral_comp_add_mul` / 定理 `integral_comp_add_mul`

English:
theorem integral_comp_add_mul
  given: (hc : c != 0) (d)
  proof: by
  rw [← integral_comp_add_left]; rw [← integral_comp_mul_left _ hc]

@[simp]

中文:
定理 integral_comp_add_mul
  条件: (hc : c != 0) (d)
  证明: by
  rw [← integral_comp_add_left]; rw [← integral_comp_mul_left _ hc]

@[simp]

Depends on / 依赖: integral_comp_add_left, integral_comp_mul_left
-/
theorem integral_comp_add_mul (hc : c != 0) (d) :
    (∫ x in a..b, f (d + c * x)) = c⁻¹ • ∫ x in d + c * a..d + c * b, f x := by
  rw [← integral_comp_add_left]; rw [← integral_comp_mul_left _ hc]

@[simp]
/--
theorem `smul_integral_comp_add_mul` / 定理 `smul_integral_comp_add_mul`

English:
theorem smul_integral_comp_add_mul
  given: (c d)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_mul]

@[simp]

中文:
定理 smul_integral_comp_add_mul
  条件: (c d)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_mul]

@[simp]

Depends on / 依赖: CompletelyDistribLattice, CompletelyDistribLattice.toCompleteDistribLattice, integral_comp_add_mul, toCompleteDistribLattice
-/
theorem smul_integral_comp_add_mul (c d) :
    (c • ∫ x in a..b, f (d + c * x)) = ∫ x in d + c * a..d + c * b, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_mul]

@[simp]
/--
theorem `integral_comp_div_add` / 定理 `integral_comp_div_add`

English:
theorem integral_comp_div_add
  given: (hc : c != 0) (d)
  proof: by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_add f (inv_ne_zero hc) d

@[simp]

中文:
定理 integral_comp_div_add
  条件: (hc : c != 0) (d)
  证明: by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_add f (inv_ne_zero hc) d

@[simp]

Depends on / 依赖: CompleteLinearOrder, CompleteLinearOrder.toCompletelyDistribLattice, div_eq_inv_mul, integral_comp_mul_add, inv_inv, inv_ne_zero, toCompletelyDistribLattice
-/
theorem integral_comp_div_add (hc : c != 0) (d) :
    (∫ x in a..b, f (x / c + d)) = c • ∫ x in a / c + d..b / c + d, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_add f (inv_ne_zero hc) d

@[simp]
/--
theorem `inv_smul_integral_comp_div_add` / 定理 `inv_smul_integral_comp_div_add`

English:
theorem inv_smul_integral_comp_div_add
  given: (c d)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_add]

@[simp]

中文:
定理 inv_smul_integral_comp_div_add
  条件: (c d)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_add]

@[simp]

Depends on / 依赖: integral_comp_div_add
-/
theorem inv_smul_integral_comp_div_add (c d) :
    (c⁻¹ • ∫ x in a..b, f (x / c + d)) = ∫ x in a / c + d..b / c + d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_add]

@[simp]
/--
theorem `integral_comp_add_div` / 定理 `integral_comp_add_div`

English:
theorem integral_comp_add_div
  given: (hc : c != 0) (d)
  proof: by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_add_mul f (inv_ne_zero hc) d

@[simp]

中文:
定理 integral_comp_add_div
  条件: (hc : c != 0) (d)
  证明: by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_add_mul f (inv_ne_zero hc) d

@[simp]

Depends on / 依赖: div_eq_inv_mul, integral_comp_add_mul, inv_inv, inv_ne_zero
-/
theorem integral_comp_add_div (hc : c != 0) (d) :
    (∫ x in a..b, f (d + x / c)) = c • ∫ x in d + a / c..d + b / c, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_add_mul f (inv_ne_zero hc) d

@[simp]
/--
theorem `inv_smul_integral_comp_add_div` / 定理 `inv_smul_integral_comp_add_div`

English:
theorem inv_smul_integral_comp_add_div
  given: (c d)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_div]

@[simp]

中文:
定理 inv_smul_integral_comp_add_div
  条件: (c d)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_div]

@[simp]

Depends on / 依赖: integral_comp_add_div
-/
theorem inv_smul_integral_comp_add_div (c d) :
    (c⁻¹ • ∫ x in a..b, f (d + x / c)) = ∫ x in d + a / c..d + b / c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_div]

@[simp]
/--
theorem `integral_comp_mul_sub` / 定理 `integral_comp_mul_sub`

English:
theorem integral_comp_mul_sub
  given: (hc : c != 0) (d)
  proof: by
  simpa only [sub_eq_add_neg] using integral_comp_mul_add f hc (-d)

@[simp]

中文:
定理 integral_comp_mul_sub
  条件: (hc : c != 0) (d)
  证明: by
  simpa only [sub_eq_add_neg] using integral_comp_mul_add f hc (-d)

@[simp]

Depends on / 依赖: integral_comp_mul_add, sub_eq_add_neg
-/
theorem integral_comp_mul_sub (hc : c != 0) (d) :
    (∫ x in a..b, f (c * x - d)) = c⁻¹ • ∫ x in c * a - d..c * b - d, f x := by
  simpa only [sub_eq_add_neg] using integral_comp_mul_add f hc (-d)

@[simp]
/--
theorem `smul_integral_comp_mul_sub` / 定理 `smul_integral_comp_mul_sub`

English:
theorem smul_integral_comp_mul_sub
  given: (c d)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_sub]

@[simp]

中文:
定理 smul_integral_comp_mul_sub
  条件: (c d)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_sub]

@[simp]

Depends on / 依赖: integral_comp_mul_sub
-/
theorem smul_integral_comp_mul_sub (c d) :
    (c • ∫ x in a..b, f (c * x - d)) = ∫ x in c * a - d..c * b - d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_sub]

@[simp]
/--
theorem `integral_comp_sub_mul` / 定理 `integral_comp_sub_mul`

English:
theorem integral_comp_sub_mul
  given: (hc : c != 0) (d)
  proof: by
  simp only [sub_eq_add_neg, neg_mul_eq_neg_mul]
  rw [integral_comp_add_mul f (neg_ne_zero.mpr hc) d]; rw [integral_symm]
  simp only [inv_neg, smul_neg, neg_neg, neg_smul]

@[simp]

中文:
定理 integral_comp_sub_mul
  条件: (hc : c != 0) (d)
  证明: by
  simp only [sub_eq_add_neg, neg_mul_eq_neg_mul]
  rw [integral_comp_add_mul f (neg_ne_zero.mpr hc) d]; rw [integral_symm]
  simp only [inv_neg, smul_neg, neg_neg, neg_smul]

@[simp]

Depends on / 依赖: integral_comp_add_mul, integral_symm, inv_neg, neg_mul_eq_neg_mul, neg_ne_zero, neg_ne_zero.mpr, neg_neg, neg_smul, smul_neg, sub_eq_add_neg
-/
theorem integral_comp_sub_mul (hc : c != 0) (d) :
    (∫ x in a..b, f (d - c * x)) = c⁻¹ • ∫ x in d - c * b..d - c * a, f x := by
  simp only [sub_eq_add_neg, neg_mul_eq_neg_mul]
  rw [integral_comp_add_mul f (neg_ne_zero.mpr hc) d]; rw [integral_symm]
  simp only [inv_neg, smul_neg, neg_neg, neg_smul]

@[simp]
/--
theorem `smul_integral_comp_sub_mul` / 定理 `smul_integral_comp_sub_mul`

English:
theorem smul_integral_comp_sub_mul
  given: (c d)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_mul]

@[simp]

中文:
定理 smul_integral_comp_sub_mul
  条件: (c d)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_mul]

@[simp]

Depends on / 依赖: integral_comp_sub_mul
-/
theorem smul_integral_comp_sub_mul (c d) :
    (c • ∫ x in a..b, f (d - c * x)) = ∫ x in d - c * b..d - c * a, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_mul]

@[simp]
/--
theorem `integral_comp_div_sub` / 定理 `integral_comp_div_sub`

English:
theorem integral_comp_div_sub
  given: (hc : c != 0) (d)
  proof: by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_sub f (inv_ne_zero hc) d

@[simp]

中文:
定理 integral_comp_div_sub
  条件: (hc : c != 0) (d)
  证明: by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_sub f (inv_ne_zero hc) d

@[simp]

Depends on / 依赖: div_eq_inv_mul, integral_comp_mul_sub, inv_inv, inv_ne_zero
-/
theorem integral_comp_div_sub (hc : c != 0) (d) :
    (∫ x in a..b, f (x / c - d)) = c • ∫ x in a / c - d..b / c - d, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_sub f (inv_ne_zero hc) d

@[simp]
/--
theorem `inv_smul_integral_comp_div_sub` / 定理 `inv_smul_integral_comp_div_sub`

English:
theorem inv_smul_integral_comp_div_sub
  given: (c d)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_sub]

@[simp]

中文:
定理 inv_smul_integral_comp_div_sub
  条件: (c d)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_sub]

@[simp]

Depends on / 依赖: integral_comp_div_sub
-/
theorem inv_smul_integral_comp_div_sub (c d) :
    (c⁻¹ • ∫ x in a..b, f (x / c - d)) = ∫ x in a / c - d..b / c - d, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_sub]

@[simp]
/--
theorem `integral_comp_sub_div` / 定理 `integral_comp_sub_div`

English:
theorem integral_comp_sub_div
  given: (hc : c != 0) (d)
  proof: by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_sub_mul f (inv_ne_zero hc) d

@[simp]

中文:
定理 integral_comp_sub_div
  条件: (hc : c != 0) (d)
  证明: by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_sub_mul f (inv_ne_zero hc) d

@[simp]

Depends on / 依赖: div_eq_inv_mul, integral_comp_sub_mul, inv_inv, inv_ne_zero
-/
theorem integral_comp_sub_div (hc : c != 0) (d) :
    (∫ x in a..b, f (d - x / c)) = c • ∫ x in d - b / c..d - a / c, f x := by
  simpa only [div_eq_inv_mul, inv_inv] using integral_comp_sub_mul f (inv_ne_zero hc) d

@[simp]
/--
theorem `inv_smul_integral_comp_sub_div` / 定理 `inv_smul_integral_comp_sub_div`

English:
theorem inv_smul_integral_comp_sub_div
  given: (c d)
  proof: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_div]

@[simp]

中文:
定理 inv_smul_integral_comp_sub_div
  条件: (c d)
  证明: by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_div]

@[simp]

Depends on / 依赖: integral_comp_sub_div
-/
theorem inv_smul_integral_comp_sub_div (c d) :
    (c⁻¹ • ∫ x in a..b, f (d - x / c)) = ∫ x in d - b / c..d - a / c, f x := by
  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_div]

@[simp]
/--
theorem `integral_comp_sub_right` / 定理 `integral_comp_sub_right`

English:
theorem integral_comp_sub_right
  given: (d)
  statement: (∫ x in a..b, f (x - d)) = ∫ x in a - d..b - d, f x
  proof: by
  simpa only [sub_eq_add_neg] using integral_comp_add_right f (-d)

@[simp]

中文:
定理 integral_comp_sub_right
  条件: (d)
  结论: (∫ x in a..b, f (x - d)) = ∫ x in a - d..b - d, f x
  证明: by
  simpa only [sub_eq_add_neg] using integral_comp_add_right f (-d)

@[simp]

Depends on / 依赖: integral_comp_add_right, sub_eq_add_neg
-/
theorem integral_comp_sub_right (d) : (∫ x in a..b, f (x - d)) = ∫ x in a - d..b - d, f x := by
  simpa only [sub_eq_add_neg] using integral_comp_add_right f (-d)

@[simp]
/--
theorem `integral_comp_sub_left` / 定理 `integral_comp_sub_left`

English:
theorem integral_comp_sub_left
  given: (d)
  statement: (∫ x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x
  proof: by
  simpa only [one_mul, one_smul, inv_one] using integral_comp_sub_mul f one_ne_zero d

@[simp]

中文:
定理 integral_comp_sub_left
  条件: (d)
  结论: (∫ x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x
  证明: by
  simpa only [one_mul, one_smul, inv_one] using integral_comp_sub_mul f one_ne_zero d

@[simp]

Depends on / 依赖: integral_comp_sub_mul, inv_one, one_mul, one_ne_zero, one_smul
-/
theorem integral_comp_sub_left (d) : (∫ x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x := by
  simpa only [one_mul, one_smul, inv_one] using integral_comp_sub_mul f one_ne_zero d

@[simp]
/--
theorem `integral_comp_neg` / 定理 `integral_comp_neg`

English:
theorem integral_comp_neg
  statement: (∫ x in a..b, f (-x)) = ∫ x in -b..-a, f x
  proof: by
  simpa only [zero_sub] using integral_comp_sub_left f 0

中文:
定理 integral_comp_neg
  结论: (∫ x in a..b, f (-x)) = ∫ x in -b..-a, f x
  证明: by
  simpa only [zero_sub] using integral_comp_sub_left f 0

Depends on / 依赖: integral_comp_sub_left, zero_sub
-/
theorem integral_comp_neg : (∫ x in a..b, f (-x)) = ∫ x in -b..-a, f x := by
  simpa only [zero_sub] using integral_comp_sub_left f 0

end Comp

/-!
### Integral is an additive function of the interval

In this section we prove that `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ`
as well as a few other identities trivially equivalent to this one. We also prove that
`∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ` provided that `support f ⊆ Ioc a b`.

-/

section OrderClosedTopology

variable {a b c d : Real} {f g : Real -> E} {μ : Measure Real}

/--
theorem `integral_congr` / 定理 `integral_congr`

English:
theorem integral_congr
  given: {a b : Real} (h : EqOn f g [[a, b]])
  proof: by
  rcases le_total a b with hab | hab <;>
    simpa [hab, integral_of_le, integral_of_ge] using
      setIntegral_congr_fun measurableSet_Ioc (h.mono Ioc_subset_Icc_self)

中文:
定理 integral_congr
  条件: {a b : 实数} (h : EqOn f g [[a, b]])
  证明: by
  rcases le_total a b with hab | hab <;>
    simpa [hab, integral_of_le, integral_of_ge] using
      setIntegral_congr_fun measurableSet_Ioc (h.mono Ioc_subset_Icc_self)

Depends on / 依赖: Ioc_subset_Icc_self, h.mono, integral_of_ge, integral_of_le, le_total, measurableSet_Ioc, setIntegral_congr_fun
-/
theorem integral_congr {a b : Real} (h : EqOn f g [[a, b]]) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ := by
  rcases le_total a b with hab | hab <;>
    simpa [hab, integral_of_le, integral_of_ge] using
      setIntegral_congr_fun measurableSet_Ioc (h.mono Ioc_subset_Icc_self)

/--
theorem `integral_add_adjacent_intervals_cancel` / 定理 `integral_add_adjacent_intervals_cancel`

English:
theorem integral_add_adjacent_intervals_cancel
  statement: (hab : IntervalIntegrable f μ a b)
  proof: by
  have hac := hab.trans hbc
  simp only [intervalIntegral, sub_add_sub_comm, sub_eq_zero]
  iterate 4 rw [← setIntegral_union]
  · suffices Ioc a b union Ioc b c union Ioc c a = Ioc b a union Ioc c b union Ioc a c by rw [this]
    rw [Ioc_union_Ioc_union_Ioc_cycle]; rw [union_right_comm]; rw [Ioc

中文:
定理 integral_add_adjacent_intervals_cancel
  结论: (hab : 整数erval整数egrable f μ a b)
  证明: by
  have hac := hab.trans hbc
  simp only [intervalIntegral, sub_add_sub_comm, sub_eq_zero]
  iterate 4 rw [← setIntegral_union]
  · suffices Ioc a b union Ioc b c union Ioc c a = Ioc b a union Ioc c b union Ioc a c by rw [this]
    rw [Ioc_union_Ioc_union_Ioc_cycle]; rw [union_right_comm]; rw [Ioc

Depends on / 依赖: Ioc_union_Ioc_union_Ioc_cycle, all_goals, hab.trans, intervalIntegral, iterate, max_left_comm, min_left_comm, setIntegral_union, sub_add_sub_comm, sub_eq_zero, union_right_comm
-/
theorem integral_add_adjacent_intervals_cancel (hab : IntervalIntegrable f μ a b)
    (hbc : IntervalIntegrable f μ b c) :
    (((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ) + ∫ x in c..a, f x ∂μ) = 0 := by
  have hac := hab.trans hbc
  simp only [intervalIntegral, sub_add_sub_comm, sub_eq_zero]
  iterate 4 rw [← setIntegral_union]
  · suffices Ioc a b union Ioc b c union Ioc c a = Ioc b a union Ioc c b union Ioc a c by rw [this]
    rw [Ioc_union_Ioc_union_Ioc_cycle]; rw [union_right_comm]; rw [Ioc_union_Ioc_union_Ioc_cycle]; rw [min_left_comm]; rw [max_left_comm]
  all_goals
    simp [*, hab.1, hab.2, hbc.1, hbc.2, hac.1, hac.2]

/--
theorem `integral_add_adjacent_intervals` / 定理 `integral_add_adjacent_intervals`

English:
theorem integral_add_adjacent_intervals
  statement: (hab : IntervalIntegrable f μ a b)
  proof: by
  rw [← add_neg_eq_zero]; rw [← integral_symm]; rw [integral_add_adjacent_intervals_cancel hab hbc]

中文:
定理 integral_add_adjacent_intervals
  结论: (hab : 整数erval整数egrable f μ a b)
  证明: by
  rw [← add_neg_eq_zero]; rw [← integral_symm]; rw [integral_add_adjacent_intervals_cancel hab hbc]

Depends on / 依赖: add_neg_eq_zero, integral_add_adjacent_intervals_cancel, integral_symm
-/
theorem integral_add_adjacent_intervals (hab : IntervalIntegrable f μ a b)
    (hbc : IntervalIntegrable f μ b c) :
    ((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ) = ∫ x in a..c, f x ∂μ := by
  rw [← add_neg_eq_zero]; rw [← integral_symm]; rw [integral_add_adjacent_intervals_cancel hab hbc]

/--
theorem `sum_integral_adjacent_intervals_Ico` / 定理 `sum_integral_adjacent_intervals_Ico`

English:
theorem sum_integral_adjacent_intervals_Ico
  statement: {a : Nat -> Real} {m n : Nat} (hmn : m <= n)
  proof: by
  revert hint
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro p hmp IH h
    rw [Finset.sum_Ico_succ_top hmp]; rw [IH]; rw [integral_add_adjacent_intervals]
    · refine IntervalIntegrable.trans_iterate_Ico hmp fun k hk => h k ?_
      exact (Ico_subset_Ico le_rfl (Nat.le_succ _)) hk
   

中文:
定理 sum_integral_adjacent_intervals_Ico
  结论: {a : 自然数 -> 实数} {m n : 自然数} (hmn : m <= n)
  证明: by
  revert hint
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro p hmp IH h
    rw [Finset.sum_Ico_succ_top hmp]; rw [IH]; rw [integral_add_adjacent_intervals]
    · refine IntervalIntegrable.trans_iterate_Ico hmp fun k hk => h k ?_
      exact (Ico_subset_Ico le_rfl (Nat.le_succ _)) hk
   

Depends on / 依赖: Finset, Finset.sum_Ico_succ_top, Ico_subset_Ico, Ico_subset_Ico_right, IntervalIntegrable, IntervalIntegrable.trans_iterate_Ico, Nat.le_induction, Nat.le_succ, integral_add_adjacent_intervals, le_induction, le_rfl, le_succ, p.le_succ, revert, sum_Ico_succ_top, trans_iterate_Ico
-/
theorem sum_integral_adjacent_intervals_Ico {a : Nat -> Real} {m n : Nat} (hmn : m <= n)
    (hint : forall k in Ico m n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
∑ k in Finset.Ico m n, ∫ x in a k..a k + 1, f x ∂μ = ∫ x in a m..a n, f x ∂μ := by
  revert hint
  refine Nat.le_induction ?_ ?_ n hmn
  · simp
  · intro p hmp IH h
    rw [Finset.sum_Ico_succ_top hmp]; rw [IH]; rw [integral_add_adjacent_intervals]
    · refine IntervalIntegrable.trans_iterate_Ico hmp fun k hk => h k ?_
      exact (Ico_subset_Ico le_rfl (Nat.le_succ _)) hk
    · apply h
      simp [hmp]
    · intro k hk
      exact h _ (Ico_subset_Ico_right p.le_succ hk)

/--
theorem `sum_integral_adjacent_intervals` / 定理 `sum_integral_adjacent_intervals`

English:
theorem sum_integral_adjacent_intervals
  statement: {a : Nat -> Real} {n : Nat}
  proof: by
  rw [← Nat.Ico_zero_eq_range]
  exact sum_integral_adjacent_intervals_Ico zero_le fun k hk => hint k hk.2

中文:
定理 sum_integral_adjacent_intervals
  结论: {a : 自然数 -> 实数} {n : 自然数}
  证明: by
  rw [← Nat.Ico_zero_eq_range]
  exact sum_integral_adjacent_intervals_Ico zero_le fun k hk => hint k hk.2

Depends on / 依赖: Ico_zero_eq_range, Nat.Ico_zero_eq_range, sum_integral_adjacent_intervals_Ico, zero_le
-/
theorem sum_integral_adjacent_intervals {a : Nat -> Real} {n : Nat}
    (hint : forall k < n, IntervalIntegrable f μ (a k) (a <| k + 1)) :
∑ k in Finset.range n, ∫ x in a k..a k + 1, f x ∂μ = ∫ x in (a 0)..(a n), f x ∂μ := by
  rw [← Nat.Ico_zero_eq_range]
  exact sum_integral_adjacent_intervals_Ico zero_le fun k hk => hint k hk.2

/--
theorem `integral_interval_sub_left` / 定理 `integral_interval_sub_left`

English:
theorem integral_interval_sub_left
  statement: (hab : IntervalIntegrable f μ a b)
  proof: sub_eq_of_eq_add' Eq.symm integral_add_adjacent_intervals hac (hac.symm.trans hab)

中文:
定理 integral_interval_sub_left
  结论: (hab : 整数erval整数egrable f μ a b)
  证明: sub_eq_of_eq_add' Eq.symm integral_add_adjacent_intervals hac (hac.symm.trans hab)

Depends on / 依赖: Eq.symm, hac.symm.trans, integral_add_adjacent_intervals, sub_eq_of_eq_add
-/
theorem integral_interval_sub_left (hab : IntervalIntegrable f μ a b)
    (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in a..c, f x ∂μ) = ∫ x in c..b, f x ∂μ :=
sub_eq_of_eq_add' Eq.symm integral_add_adjacent_intervals hac (hac.symm.trans hab)

/--
theorem `integral_interval_add_interval_comm` / 定理 `integral_interval_add_interval_comm`

English:
theorem integral_interval_add_interval_comm
  statement: (hab : IntervalIntegrable f μ a b)
  proof: by
  rw [← integral_add_adjacent_intervals hac hcd]; rw [add_assoc]; rw [add_left_comm]; rw [integral_add_adjacent_intervals hac (hac.symm.trans hab)]; rw [add_comm]

中文:
定理 integral_interval_add_interval_comm
  结论: (hab : 整数erval整数egrable f μ a b)
  证明: by
  rw [← integral_add_adjacent_intervals hac hcd]; rw [add_assoc]; rw [add_left_comm]; rw [integral_add_adjacent_intervals hac (hac.symm.trans hab)]; rw [add_comm]

Depends on / 依赖: add_assoc, add_comm, add_left_comm, hac.symm.trans, integral_add_adjacent_intervals
-/
theorem integral_interval_add_interval_comm (hab : IntervalIntegrable f μ a b)
    (hcd : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) + ∫ x in c..d, f x ∂μ) =
      (∫ x in a..d, f x ∂μ) + ∫ x in c..b, f x ∂μ := by
  rw [← integral_add_adjacent_intervals hac hcd]; rw [add_assoc]; rw [add_left_comm]; rw [integral_add_adjacent_intervals hac (hac.symm.trans hab)]; rw [add_comm]

/--
theorem `integral_interval_sub_interval_comm` / 定理 `integral_interval_sub_interval_comm`

English:
theorem integral_interval_sub_interval_comm
  statement: (hab : IntervalIntegrable f μ a b)
  proof: by
  simp only [sub_eq_add_neg, ← integral_symm,
    integral_interval_add_interval_comm hab hcd.symm (hac.trans hcd)]

中文:
定理 integral_interval_sub_interval_comm
  结论: (hab : 整数erval整数egrable f μ a b)
  证明: by
  simp only [sub_eq_add_neg, ← integral_symm,
    integral_interval_add_interval_comm hab hcd.symm (hac.trans hcd)]

Depends on / 依赖: hac.trans, hcd.symm, integral_interval_add_interval_comm, integral_symm, sub_eq_add_neg
-/
theorem integral_interval_sub_interval_comm (hab : IntervalIntegrable f μ a b)
    (hcd : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in c..d, f x ∂μ) =
      (∫ x in a..c, f x ∂μ) - ∫ x in b..d, f x ∂μ := by
  simp only [sub_eq_add_neg, ← integral_symm,
    integral_interval_add_interval_comm hab hcd.symm (hac.trans hcd)]

/--
theorem `integral_interval_sub_interval_comm'` / 定理 `integral_interval_sub_interval_comm'`

English:
theorem integral_interval_sub_interval_comm'
  statement: (hab : IntervalIntegrable f μ a b)
  proof: by
  rw [integral_interval_sub_interval_comm hab hcd hac]; rw [integral_symm b d]; rw [integral_symm a c]; rw [sub_neg_eq_add]; rw [sub_eq_neg_add]

中文:
定理 integral_interval_sub_interval_comm'
  结论: (hab : 整数erval整数egrable f μ a b)
  证明: by
  rw [integral_interval_sub_interval_comm hab hcd hac]; rw [integral_symm b d]; rw [integral_symm a c]; rw [sub_neg_eq_add]; rw [sub_eq_neg_add]

Depends on / 依赖: integral_interval_sub_interval_comm, integral_symm, sub_eq_neg_add, sub_neg_eq_add
-/
theorem integral_interval_sub_interval_comm' (hab : IntervalIntegrable f μ a b)
    (hcd : IntervalIntegrable f μ c d) (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in c..d, f x ∂μ) =
      (∫ x in d..b, f x ∂μ) - ∫ x in c..a, f x ∂μ := by
  rw [integral_interval_sub_interval_comm hab hcd hac]; rw [integral_symm b d]; rw [integral_symm a c]; rw [sub_neg_eq_add]; rw [sub_eq_neg_add]

/--
theorem `integral_Iic_sub_Iic` / 定理 `integral_Iic_sub_Iic`

English:
theorem integral_Iic_sub_Iic
  given: (ha : IntegrableOn f (Iic a) μ) (hb : IntegrableOn f (Iic b) μ)
  proof: by
  wlog hab : a <= b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab), neg_sub]
  rw [sub_eq_iff_eq_add']; rw [integral_of_le hab]; rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl)]; rw [Iic_union_Ioc_eq_Iic hab]
  exacts [measurableSet_Ioc, ha, hb.mono_set fun _ => And.rig

中文:
定理 integral_Iic_sub_Iic
  条件: (ha : 整数egrableOn f (Iic a) μ) (hb : 整数egrableOn f (Iic b) μ)
  证明: by
  wlog hab : a <= b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab), neg_sub]
  rw [sub_eq_iff_eq_add']; rw [integral_of_le hab]; rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl)]; rw [Iic_union_Ioc_eq_Iic hab]
  exacts [measurableSet_Ioc, ha, hb.mono_set fun _ => And.rig

Depends on / 依赖: And.right, DistribLattice, Iic_disjoint_Ioc, Iic_union_Ioc_eq_Iic, Order.Frame.toDistribLattice, exacts, generalizing, hb.mono_set, integral_of_le, integral_symm, le_of_not_ge, le_rfl, measurableSet_Ioc, mono_set, neg_sub, setIntegral_union, sub_eq_iff_eq_add, toDistribLattice
-/
theorem integral_Iic_sub_Iic (ha : IntegrableOn f (Iic a) μ) (hb : IntegrableOn f (Iic b) μ) :
    ((∫ x in Iic b, f x ∂μ) - ∫ x in Iic a, f x ∂μ) = ∫ x in a..b, f x ∂μ := by
  wlog hab : a <= b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab), neg_sub]
  rw [sub_eq_iff_eq_add']; rw [integral_of_le hab]; rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl)]; rw [Iic_union_Ioc_eq_Iic hab]
  exacts [measurableSet_Ioc, ha, hb.mono_set fun _ => And.right]

/--
theorem `integral_interval_add_Ioi` / 定理 `integral_interval_add_Ioi`

English:
theorem integral_interval_add_Ioi
  statement: (ha : IntegrableOn f (Ioi a) μ)
  proof: by
  wlog hab : a <= b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab)]; grind
  rw [integral_of_le hab]; rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (ha.mono_set Ioc_subset_Ioi_self) hb]; rw [Ioc_union_Ioi_eq_Ioi hab]

中文:
定理 integral_interval_add_Ioi
  结论: (ha : 整数egrableOn f (Ioi a) μ)
  证明: by
  wlog hab : a <= b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab)]; grind
  rw [integral_of_le hab]; rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (ha.mono_set Ioc_subset_Ioi_self) hb]; rw [Ioc_union_Ioi_eq_Ioi hab]

Depends on / 依赖: Ioc_disjoint_Ioi_same, Ioc_subset_Ioi_self, Ioc_union_Ioi_eq_Ioi, generalizing, ha.mono_set, integral_of_le, integral_symm, le_of_not_ge, measurableSet_Ioi, mono_set, setIntegral_union
-/
theorem integral_interval_add_Ioi (ha : IntegrableOn f (Ioi a) μ)
    (hb : IntegrableOn f (Ioi b) μ) :
    ∫ (x : Real) in a..b, f x ∂μ + ∫ (x : Real) in Ioi b, f x ∂μ
    = ∫ (x : Real) in Ioi a, f x ∂μ := by
  wlog hab : a <= b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab)]; grind
  rw [integral_of_le hab]; rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (ha.mono_set Ioc_subset_Ioi_self) hb]; rw [Ioc_union_Ioi_eq_Ioi hab]

/--
theorem `integral_interval_add_Ioi'` / 定理 `integral_interval_add_Ioi'`

English:
theorem integral_interval_add_Ioi'
  statement: (ha : IntervalIntegrable f μ a b)
  proof: by
  rw [integral_interval_add_Ioi _ hb]
  by_cases! h : a <= b
  · exact (Ioc_union_Ioi_eq_Ioi h) ▸ IntegrableOn.union
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h).1 ha) hb
· exact hb.mono_set Ioi_subset_Ioi h.le

中文:
定理 integral_interval_add_Ioi'
  结论: (ha : 整数erval整数egrable f μ a b)
  证明: by
  rw [integral_interval_add_Ioi _ hb]
  by_cases! h : a <= b
  · exact (Ioc_union_Ioi_eq_Ioi h) ▸ IntegrableOn.union
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h).1 ha) hb
· exact hb.mono_set Ioi_subset_Ioi h.le

Depends on / 依赖: IntegrableOn, IntegrableOn.union, Ioc_union_Ioi_eq_Ioi, Ioi_subset_Ioi, h.le, hb.mono_set, integral_interval_add_Ioi, intervalIntegrable_iff_integrableOn_Ioc_of_le, mono_set
-/
theorem integral_interval_add_Ioi' (ha : IntervalIntegrable f μ a b)
    (hb : IntegrableOn f (Ioi b) μ) :
    ∫ (x : Real) in a..b, f x ∂μ + ∫ (x : Real) in Ioi b, f x ∂μ
    = ∫ (x : Real) in Ioi a, f x ∂μ := by
  rw [integral_interval_add_Ioi _ hb]
  by_cases! h : a <= b
  · exact (Ioc_union_Ioi_eq_Ioi h) ▸ IntegrableOn.union
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h).1 ha) hb
· exact hb.mono_set Ioi_subset_Ioi h.le

/--
theorem `integral_Ioi_sub_Ioi` / 定理 `integral_Ioi_sub_Ioi`

English:
theorem integral_Ioi_sub_Ioi
  given: (hf : IntegrableOn f (Ioi a) μ) (hab : a <= b)
  proof: sub_eq_of_eq_add (integral_interval_add_Ioi hf (hf.mono_set (Ioi_subset_Ioi hab))).symm

中文:
定理 integral_Ioi_sub_Ioi
  条件: (hf : 整数egrableOn f (Ioi a) μ) (hab : a <= b)
  证明: sub_eq_of_eq_add (integral_interval_add_Ioi hf (hf.mono_set (Ioi_subset_Ioi hab))).symm

Depends on / 依赖: Ioi_subset_Ioi, hf.mono_set, integral_interval_add_Ioi, mono_set, sub_eq_of_eq_add
-/
theorem integral_Ioi_sub_Ioi (hf : IntegrableOn f (Ioi a) μ) (hab : a <= b) :
    ∫ x in Ioi a, f x ∂μ - ∫ x in Ioi b, f x ∂μ = ∫ x in a..b, f x ∂μ :=
  sub_eq_of_eq_add (integral_interval_add_Ioi hf (hf.mono_set (Ioi_subset_Ioi hab))).symm

/--
theorem `integral_Ioi_sub_Ioi'` / 定理 `integral_Ioi_sub_Ioi'`

English:
theorem integral_Ioi_sub_Ioi'
  given: (hf : IntegrableOn f (Ioi a) μ) (hg : IntegrableOn f (Ioi b) μ)
  proof: by
  wlog! hab : a <= b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  exact integral_Ioi_sub_Ioi hf hab

中文:
定理 integral_Ioi_sub_Ioi'
  条件: (hf : 整数egrableOn f (Ioi a) μ) (hg : 整数egrableOn f (Ioi b) μ)
  证明: by
  wlog! hab : a <= b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  exact integral_Ioi_sub_Ioi hf hab

Depends on / 依赖: generalizing, hab.le, integral_Ioi_sub_Ioi, integral_symm, neg_sub
-/
theorem integral_Ioi_sub_Ioi' (hf : IntegrableOn f (Ioi a) μ) (hg : IntegrableOn f (Ioi b) μ) :
    ∫ x in Ioi a, f x ∂μ - ∫ x in Ioi b, f x ∂μ = ∫ x in a..b, f x ∂μ := by
  wlog! hab : a <= b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  exact integral_Ioi_sub_Ioi hf hab

/--
theorem `integral_Iio_sub_Iio` / 定理 `integral_Iio_sub_Iio`

English:
theorem integral_Iio_sub_Iio
  given: (hf : IntegrableOn f (Iio b) μ) (hab : a <= b)
  proof: by
  have ha : IntegrableOn f (Iio a) μ := hf.mono_set (Iio_subset_Iio hab)
  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Iio_self
  rw [sub_eq_iff_eq_add']; rw [← setIntegral_union (by grind) measurableSet_Ico ha h]; rw [Iio_union_Ico_eq_Iio hab]

中文:
定理 integral_Iio_sub_Iio
  条件: (hf : 整数egrableOn f (Iio b) μ) (hab : a <= b)
  证明: by
  have ha : IntegrableOn f (Iio a) μ := hf.mono_set (Iio_subset_Iio hab)
  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Iio_self
  rw [sub_eq_iff_eq_add']; rw [← setIntegral_union (by grind) measurableSet_Ico ha h]; rw [Iio_union_Ico_eq_Iio hab]

Depends on / 依赖: Ico_subset_Iio_self, Iio_subset_Iio, Iio_union_Ico_eq_Iio, IntegrableOn, hf.mono_set, measurableSet_Ico, mono_set, setIntegral_union, sub_eq_iff_eq_add
-/
theorem integral_Iio_sub_Iio (hf : IntegrableOn f (Iio b) μ) (hab : a <= b) :
    ∫ x in Iio b, f x ∂μ - ∫ x in Iio a, f x ∂μ = ∫ x in Ico a b, f x ∂μ := by
  have ha : IntegrableOn f (Iio a) μ := hf.mono_set (Iio_subset_Iio hab)
  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Iio_self
  rw [sub_eq_iff_eq_add']; rw [← setIntegral_union (by grind) measurableSet_Ico ha h]; rw [Iio_union_Ico_eq_Iio hab]

/--
theorem `integral_Iio_sub_Iio'` / 定理 `integral_Iio_sub_Iio'`

English:
theorem integral_Iio_sub_Iio'
  statement: [NullSingletonClass μ] (hf : IntegrableOn f (Iio b) μ)
  proof: by
  wlog! hab : a <= b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  rw [integral_Iio_sub_Iio hf hab]; rw [integral_of_le hab]; rw [integral_Ico_eq_integral_Ioc]

中文:
定理 integral_Iio_sub_Iio'
  结论: [NullSingletonClass μ] (hf : 整数egrableOn f (Iio b) μ)
  证明: by
  wlog! hab : a <= b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  rw [integral_Iio_sub_Iio hf hab]; rw [integral_of_le hab]; rw [integral_Ico_eq_integral_Ioc]

Depends on / 依赖: generalizing, hab.le, integral_Ico_eq_integral_Ioc, integral_Iio_sub_Iio, integral_of_le, integral_symm, neg_sub
-/
theorem integral_Iio_sub_Iio' [NullSingletonClass μ] (hf : IntegrableOn f (Iio b) μ)
    (hg : IntegrableOn f (Iio a) μ) :
    ∫ x in Iio b, f x ∂μ - ∫ x in Iio a, f x ∂μ = ∫ x in a..b, f x ∂μ := by
  wlog! hab : a <= b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  rw [integral_Iio_sub_Iio hf hab]; rw [integral_of_le hab]; rw [integral_Ico_eq_integral_Ioc]

/--
theorem `integral_Ici_sub_Ici` / 定理 `integral_Ici_sub_Ici`

English:
theorem integral_Ici_sub_Ici
  given: (hf : IntegrableOn f (Ici a) μ) (hab : a <= b)
  proof: by
  have ha : IntegrableOn f (Ici b) μ := hf.mono_set (Ici_subset_Ici.2 hab)
  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Ici_self
  rw [sub_eq_iff_eq_add']; rw [← setIntegral_union (by grind) measurableSet_Ico ha h]; rw [union_comm]; rw [Ico_union_Ici_eq_Ici hab]

中文:
定理 integral_Ici_sub_Ici
  条件: (hf : 整数egrableOn f (Ici a) μ) (hab : a <= b)
  证明: by
  have ha : IntegrableOn f (Ici b) μ := hf.mono_set (Ici_subset_Ici.2 hab)
  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Ici_self
  rw [sub_eq_iff_eq_add']; rw [← setIntegral_union (by grind) measurableSet_Ico ha h]; rw [union_comm]; rw [Ico_union_Ici_eq_Ici hab]

Depends on / 依赖: Ici_subset_Ici, Ico_subset_Ici_self, Ico_union_Ici_eq_Ici, IntegrableOn, hf.mono_set, measurableSet_Ico, mono_set, setIntegral_union, sub_eq_iff_eq_add, union_comm
-/
theorem integral_Ici_sub_Ici (hf : IntegrableOn f (Ici a) μ) (hab : a <= b) :
    ∫ x in Ici a, f x ∂μ - ∫ x in Ici b, f x ∂μ = ∫ x in Ico a b, f x ∂μ := by
  have ha : IntegrableOn f (Ici b) μ := hf.mono_set (Ici_subset_Ici.2 hab)
  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Ici_self
  rw [sub_eq_iff_eq_add']; rw [← setIntegral_union (by grind) measurableSet_Ico ha h]; rw [union_comm]; rw [Ico_union_Ici_eq_Ici hab]

/--
theorem `integral_Ici_sub_Ici'` / 定理 `integral_Ici_sub_Ici'`

English:
theorem integral_Ici_sub_Ici'
  statement: [NullSingletonClass μ] (hf : IntegrableOn f (Ici a) μ)
  proof: by
  wlog! hab : a <= b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  rw [integral_Ici_sub_Ici hf hab]; rw [integral_of_le hab]; rw [integral_Ico_eq_integral_Ioc]

中文:
定理 integral_Ici_sub_Ici'
  结论: [NullSingletonClass μ] (hf : 整数egrableOn f (Ici a) μ)
  证明: by
  wlog! hab : a <= b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  rw [integral_Ici_sub_Ici hf hab]; rw [integral_of_le hab]; rw [integral_Ico_eq_integral_Ioc]

Depends on / 依赖: generalizing, hab.le, integral_Ici_sub_Ici, integral_Ico_eq_integral_Ioc, integral_of_le, integral_symm, neg_sub
-/
theorem integral_Ici_sub_Ici' [NullSingletonClass μ] (hf : IntegrableOn f (Ici a) μ)
    (hg : IntegrableOn f (Ici b) μ) :
    ∫ x in Ici a, f x ∂μ - ∫ x in Ici b, f x ∂μ = ∫ x in a..b, f x ∂μ := by
  wlog! hab : a <= b generalizing a b
  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
  rw [integral_Ici_sub_Ici hf hab]; rw [integral_of_le hab]; rw [integral_Ico_eq_integral_Ioc]

/--
theorem `integral_Iic_add_Ioi` / 定理 `integral_Iic_add_Ioi`

English:
theorem integral_Iic_add_Ioi
  statement: (h_left : IntegrableOn f (Iic b) μ)
  proof: by
  convert! (setIntegral_union (Iic_disjoint_Ioi <| Eq.le rfl) measurableSet_Ioi h_left h_right).symm
  rw [Iic_union_Ioi]; rw [Measure.restrict_univ]

中文:
定理 integral_Iic_add_Ioi
  结论: (h_left : 整数egrableOn f (Iic b) μ)
  证明: by
  convert! (setIntegral_union (Iic_disjoint_Ioi <| Eq.le rfl) measurableSet_Ioi h_left h_right).symm
  rw [Iic_union_Ioi]; rw [Measure.restrict_univ]

Depends on / 依赖: Eq.le, Iic_disjoint_Ioi, Iic_union_Ioi, Measure, Measure.restrict_univ, convert, h_left, h_right, measurableSet_Ioi, restrict_univ, setIntegral_union
-/
theorem integral_Iic_add_Ioi (h_left : IntegrableOn f (Iic b) μ)
    (h_right : IntegrableOn f (Ioi b) μ) :
    (∫ x in Iic b, f x ∂μ) + (∫ x in Ioi b, f x ∂μ) = ∫ (x : Real), f x ∂μ := by
  convert! (setIntegral_union (Iic_disjoint_Ioi <| Eq.le rfl) measurableSet_Ioi h_left h_right).symm
  rw [Iic_union_Ioi]; rw [Measure.restrict_univ]

/--
theorem `integral_Iio_add_Ici` / 定理 `integral_Iio_add_Ici`

English:
theorem integral_Iio_add_Ici
  statement: (h_left : IntegrableOn f (Iio b) μ)
  proof: by
  convert! (setIntegral_union (Iio_disjoint_Ici <| Eq.le rfl) measurableSet_Ici h_left h_right).symm
  rw [Iio_union_Ici]; rw [Measure.restrict_univ]

中文:
定理 integral_Iio_add_Ici
  结论: (h_left : 整数egrableOn f (Iio b) μ)
  证明: by
  convert! (setIntegral_union (Iio_disjoint_Ici <| Eq.le rfl) measurableSet_Ici h_left h_right).symm
  rw [Iio_union_Ici]; rw [Measure.restrict_univ]

Depends on / 依赖: Eq.le, Iio_disjoint_Ici, Iio_union_Ici, Measure, Measure.restrict_univ, convert, h_left, h_right, measurableSet_Ici, restrict_univ, setIntegral_union
-/
theorem integral_Iio_add_Ici (h_left : IntegrableOn f (Iio b) μ)
    (h_right : IntegrableOn f (Ici b) μ) :
    (∫ x in Iio b, f x ∂μ) + (∫ x in Ici b, f x ∂μ) = ∫ (x : Real), f x ∂μ := by
  convert! (setIntegral_union (Iio_disjoint_Ici <| Eq.le rfl) measurableSet_Ici h_left h_right).symm
  rw [Iio_union_Ici]; rw [Measure.restrict_univ]

/--
theorem `integral_const_of_cdf` / 定理 `integral_const_of_cdf`

English:
theorem integral_const_of_cdf
  given: [CompleteSpace E] [IsFiniteMeasure μ] (c : E)
  proof: by
  simp only [sub_smul, ← setIntegral_const]
  refine (integral_Iic_sub_Iic ?_ ?_).symm <;> simp

中文:
定理 integral_const_of_cdf
  条件: [CompleteSpace E] [IsFiniteMeasure μ] (c : E)
  证明: by
  simp only [sub_smul, ← setIntegral_const]
  refine (integral_Iic_sub_Iic ?_ ?_).symm <;> simp

Depends on / 依赖: integral_Iic_sub_Iic, setIntegral_const, sub_smul
-/
theorem integral_const_of_cdf [CompleteSpace E] [IsFiniteMeasure μ] (c : E) :
    ∫ _ in a..b, c ∂μ = (μ.real (Iic b) - μ.real (Iic a)) • c := by
  simp only [sub_smul, ← setIntegral_const]
  refine (integral_Iic_sub_Iic ?_ ?_).symm <;> simp

/--
theorem `integral_eq_integral_of_support_subset` / 定理 `integral_eq_integral_of_support_subset`

English:
theorem integral_eq_integral_of_support_subset
  given: {a b} (h : support f subseteq Ioc a b)
  proof: by
  rcases le_total a b with hab | hab
  · rw [integral_of_le hab, ← integral_indicator measurableSet_Ioc, indicator_eq_self.2 h]
  · rw [Ioc_eq_empty hab.not_gt, subset_empty_iff, support_eq_empty_iff] at h
    simp [h]

中文:
定理 integral_eq_integral_of_support_subset
  条件: {a b} (h : support f subseteq Ioc a b)
  证明: by
  rcases le_total a b with hab | hab
  · rw [integral_of_le hab, ← integral_indicator measurableSet_Ioc, indicator_eq_self.2 h]
  · rw [Ioc_eq_empty hab.not_gt, subset_empty_iff, support_eq_empty_iff] at h
    simp [h]

Depends on / 依赖: Ioc_eq_empty, hab.not_gt, indicator_eq_self, integral_indicator, integral_of_le, le_total, measurableSet_Ioc, not_gt, subset_empty_iff, support_eq_empty_iff
-/
theorem integral_eq_integral_of_support_subset {a b} (h : support f subseteq Ioc a b) :
    ∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ := by
  rcases le_total a b with hab | hab
  · rw [integral_of_le hab, ← integral_indicator measurableSet_Ioc, indicator_eq_self.2 h]
  · rw [Ioc_eq_empty hab.not_gt, subset_empty_iff, support_eq_empty_iff] at h
    simp [h]

/--
theorem `integral_congr_ae'` / 定理 `integral_congr_ae'`

English:
theorem integral_congr_ae'
  statement: (h : forallᵐ x ∂μ, x in Ioc a b -> f x = g x)
  proof: by
  simp only [intervalIntegral, setIntegral_congr_ae measurableSet_Ioc h,
    setIntegral_congr_ae measurableSet_Ioc h']

中文:
定理 integral_congr_ae'
  结论: (h : 对任意ᵐ x ∂μ, x in Ioc a b -> f x = g x)
  证明: by
  simp only [intervalIntegral, setIntegral_congr_ae measurableSet_Ioc h,
    setIntegral_congr_ae measurableSet_Ioc h']

Depends on / 依赖: intervalIntegral, measurableSet_Ioc, setIntegral_congr_ae
-/
theorem integral_congr_ae' (h : forallᵐ x ∂μ, x in Ioc a b -> f x = g x)
    (h' : forallᵐ x ∂μ, x in Ioc b a -> f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ := by
  simp only [intervalIntegral, setIntegral_congr_ae measurableSet_Ioc h,
    setIntegral_congr_ae measurableSet_Ioc h']

/--
theorem `integral_congr_ae` / 定理 `integral_congr_ae`

English:
theorem integral_congr_ae
  given: (h : forallᵐ x ∂μ, x in Ι a b -> f x = g x)
  proof: integral_congr_ae' (ae_uIoc_iff.mp h).1 (ae_uIoc_iff.mp h).2

中文:
定理 integral_congr_ae
  条件: (h : 对任意ᵐ x ∂μ, x in Ι a b -> f x = g x)
  证明: integral_congr_ae' (ae_uIoc_iff.mp h).1 (ae_uIoc_iff.mp h).2

Depends on / 依赖: ae_uIoc_iff, ae_uIoc_iff.mp, integral_congr_ae
-/
theorem integral_congr_ae (h : forallᵐ x ∂μ, x in Ι a b -> f x = g x) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
  integral_congr_ae' (ae_uIoc_iff.mp h).1 (ae_uIoc_iff.mp h).2

/--
theorem `integral_congr_uIoo` / 定理 `integral_congr_uIoo`

English:
theorem integral_congr_uIoo
  given: [NullSingletonClass μ] (h : (uIoo a b).EqOn f g)
  proof: by
  apply integral_congr_ae
  filter_upwards [μ.ae_ne <| a ⊔ b] with x _ hx
  exact h ⟨hx.left, lt_of_le_of_ne hx.right ‹_›⟩

中文:
定理 integral_congr_uIoo
  条件: [NullSingletonClass μ] (h : (uIoo a b).EqOn f g)
  证明: by
  apply integral_congr_ae
  filter_upwards [μ.ae_ne <| a ⊔ b] with x _ hx
  exact h ⟨hx.left, lt_of_le_of_ne hx.right ‹_›⟩

Depends on / 依赖: CompleteBooleanAlgebra, CompleteBooleanAlgebra.toCompleteDistribLattice, ae_ne, filter_upwards, hx.left, hx.right, integral_congr_ae, lt_of_le_of_ne, toCompleteDistribLattice
-/
theorem integral_congr_uIoo [NullSingletonClass μ] (h : (uIoo a b).EqOn f g) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ := by
  apply integral_congr_ae
  filter_upwards [μ.ae_ne <| a ⊔ b] with x _ hx
  exact h ⟨hx.left, lt_of_le_of_ne hx.right ‹_›⟩

/--
theorem `integral_congr_Ioo_of_le` / 定理 `integral_congr_Ioo_of_le`

English:
theorem integral_congr_Ioo_of_le
  given: [NullSingletonClass μ] (hab : a <= b) (h : (Ioo a b).EqOn f g)
  proof: integral_congr_uIoo uIoo_of_le hab ▸ h

中文:
定理 integral_congr_Ioo_of_le
  条件: [NullSingletonClass μ] (hab : a <= b) (h : (Ioo a b).EqOn f g)
  证明: integral_congr_uIoo uIoo_of_le hab ▸ h

Depends on / 依赖: integral_congr_uIoo, uIoo_of_le
-/
theorem integral_congr_Ioo_of_le [NullSingletonClass μ] (hab : a <= b) (h : (Ioo a b).EqOn f g) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
integral_congr_uIoo uIoo_of_le hab ▸ h

/--
theorem `integral_congr_ae_restrict` / 定理 `integral_congr_ae_restrict`

English:
theorem integral_congr_ae_restrict
  statement: {a b : Real} {f g : Real -> E} {μ : Measure Real}
  proof: integral_congr_ae (ae_imp_of_ae_restrict h)

中文:
定理 integral_congr_ae_restrict
  结论: {a b : 实数} {f g : 实数 -> E} {μ : Measure 实数}
  证明: integral_congr_ae (ae_imp_of_ae_restrict h)

Depends on / 依赖: ae_imp_of_ae_restrict, integral_congr_ae
-/
theorem integral_congr_ae_restrict {a b : Real} {f g : Real -> E} {μ : Measure Real}
    (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
  integral_congr_ae (ae_imp_of_ae_restrict h)

/--
theorem `integral_congr_codiscreteWithin` / 定理 `integral_congr_codiscreteWithin`

English:
theorem integral_congr_codiscreteWithin
  statement: {a b : Real} {f₁ f₂ : Real -> Real}
  proof: integral_congr_ae_restrict (ae_restrict_le_codiscreteWithin measurableSet_uIoc hf)

中文:
定理 integral_congr_codiscreteWithin
  结论: {a b : 实数} {f₁ f₂ : 实数 -> 实数}
  证明: integral_congr_ae_restrict (ae_restrict_le_codiscreteWithin measurableSet_uIoc hf)

Depends on / 依赖: ae_restrict_le_codiscreteWithin, integral_congr_ae_restrict, measurableSet_uIoc
-/
theorem integral_congr_codiscreteWithin {a b : Real} {f₁ f₂ : Real -> Real}
    (hf : f₁ =ᶠ[codiscreteWithin (Ι a b)] f₂) :
    ∫ (x : Real) in a..b, f₁ x = ∫ (x : Real) in a..b, f₂ x :=
  integral_congr_ae_restrict (ae_restrict_le_codiscreteWithin measurableSet_uIoc hf)

/--
theorem `integral_zero_ae` / 定理 `integral_zero_ae`

English:
theorem integral_zero_ae
  given: (h : forallᵐ x ∂μ, x in Ι a b -> f x = 0)
  statement: ∫ x in a..b, f x ∂μ = 0
  proof: calc
    ∫ x in a..b, f x ∂μ = ∫ _ in a..b, 0 ∂μ := integral_congr_ae h
    _ = 0 := integral_zero

nonrec theorem integral_indicator {a₁ a₂ a₃ : Real} (h : a₂ in Icc a₁ a₃) :
    ∫ x in a₁..a₃, indicator {x | x <= a₂} f x ∂μ = ∫ x in a₁..a₂, f x ∂μ := by
  have : {x | x <= a₂} inter Ioc a₁ a₃ = Ioc

中文:
定理 integral_zero_ae
  条件: (h : 对任意ᵐ x ∂μ, x in Ι a b -> f x = 0)
  结论: ∫ x in a..b, f x ∂μ = 0
  证明: calc
    ∫ x in a..b, f x ∂μ = ∫ _ in a..b, 0 ∂μ := integral_congr_ae h
    _ = 0 := integral_zero

nonrec theorem integral_indicator {a₁ a₂ a₃ : Real} (h : a₂ in Icc a₁ a₃) :
    ∫ x in a₁..a₃, indicator {x | x <= a₂} f x ∂μ = ∫ x in a₁..a₂, f x ∂μ := by
  have : {x | x <= a₂} inter Ioc a₁ a₃ = Ioc

Depends on / 依赖: integral_congr_ae, integral_zero
-/
theorem integral_zero_ae (h : forallᵐ x ∂μ, x in Ι a b -> f x = 0) : ∫ x in a..b, f x ∂μ = 0 :=
  calc
    ∫ x in a..b, f x ∂μ = ∫ _ in a..b, 0 ∂μ := integral_congr_ae h
    _ = 0 := integral_zero

nonrec theorem integral_indicator {a₁ a₂ a₃ : Real} (h : a₂ in Icc a₁ a₃) :
    ∫ x in a₁..a₃, indicator {x | x <= a₂} f x ∂μ = ∫ x in a₁..a₂, f x ∂μ := by
  have : {x | x <= a₂} inter Ioc a₁ a₃ = Ioc a₁ a₂ := Iic_inter_Ioc_of_le h.2
  rw [integral_of_le h.1]; rw [integral_of_le (h.1.trans h.2)]; rw [integral_indicator]; rw [Measure.restrict_restrict]; rw [this]
  · exact measurableSet_Iic
  all_goals apply measurableSet_Iic

end OrderClosedTopology

section

variable {f g : Real -> Real} {a b : Real} {μ : Measure Real}

/--
theorem `integral_eq_zero_iff_of_le_of_nonneg_ae` / 定理 `integral_eq_zero_iff_of_le_of_nonneg_ae`

English:
theorem integral_eq_zero_iff_of_le_of_nonneg_ae
  statement: (hab : a <= b) (hf : 0 <=ᵐ[μ.restrict (Ioc a b)] f)
  proof: by
  rw [integral_of_le hab]; rw [integral_eq_zero_iff_of_nonneg_ae hf hfi.1]

中文:
定理 integral_eq_zero_iff_of_le_of_nonneg_ae
  结论: (hab : a <= b) (hf : 0 <=ᵐ[μ.restrict (Ioc a b)] f)
  证明: by
  rw [integral_of_le hab]; rw [integral_eq_zero_iff_of_nonneg_ae hf hfi.1]

Depends on / 依赖: integral_eq_zero_iff_of_nonneg_ae, integral_of_le
-/
theorem integral_eq_zero_iff_of_le_of_nonneg_ae (hab : a <= b) (hf : 0 <=ᵐ[μ.restrict (Ioc a b)] f)
    (hfi : IntervalIntegrable f μ a b) :
    ∫ x in a..b, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b)] 0 := by
  rw [integral_of_le hab]; rw [integral_eq_zero_iff_of_nonneg_ae hf hfi.1]

/--
theorem `integral_eq_zero_iff_of_nonneg_ae` / 定理 `integral_eq_zero_iff_of_nonneg_ae`

English:
theorem integral_eq_zero_iff_of_nonneg_ae
  statement: (hf : 0 <=ᵐ[μ.restrict (Ioc a b union Ioc b a)] f)
  proof: by
  rcases le_total a b with hab | hab <;>
    simp only [Ioc_eq_empty hab.not_gt, empty_union, union_empty] at hf ⊢
  · exact integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi
  · rw [integral_symm, neg_eq_zero, integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi.symm]

中文:
定理 integral_eq_zero_iff_of_nonneg_ae
  结论: (hf : 0 <=ᵐ[μ.restrict (Ioc a b union Ioc b a)] f)
  证明: by
  rcases le_total a b with hab | hab <;>
    simp only [Ioc_eq_empty hab.not_gt, empty_union, union_empty] at hf ⊢
  · exact integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi
  · rw [integral_symm, neg_eq_zero, integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi.symm]

Depends on / 依赖: Ioc_eq_empty, empty_union, hab.not_gt, hfi.symm, integral_eq_zero_iff_of_le_of_nonneg_ae, integral_symm, le_total, neg_eq_zero, not_gt, union_empty
-/
theorem integral_eq_zero_iff_of_nonneg_ae (hf : 0 <=ᵐ[μ.restrict (Ioc a b union Ioc b a)] f)
    (hfi : IntervalIntegrable f μ a b) :
    ∫ x in a..b, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b union Ioc b a)] 0 := by
  rcases le_total a b with hab | hab <;>
    simp only [Ioc_eq_empty hab.not_gt, empty_union, union_empty] at hf ⊢
  · exact integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi
  · rw [integral_symm, neg_eq_zero, integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi.symm]

/--
theorem `integral_pos_iff_support_of_nonneg_ae'` / 定理 `integral_pos_iff_support_of_nonneg_ae'`

English:
theorem integral_pos_iff_support_of_nonneg_ae'
  statement: (hf : 0 <=ᵐ[μ.restrict (Ι a b)] f)
  proof: by
  rcases lt_or_ge a b with hab | hba
  · rw [uIoc_of_le hab.le] at hf
    simp only [hab, true_and, integral_of_le hab.le,
      setIntegral_pos_iff_support_of_nonneg_ae hf hfi.1]
  · suffices (∫ x in a..b, f x ∂μ) <= 0 by simp only [this.not_gt, hba.not_gt, false_and]
    rw [integral_of_ge hba]

中文:
定理 integral_pos_iff_support_of_nonneg_ae'
  结论: (hf : 0 <=ᵐ[μ.restrict (Ι a b)] f)
  证明: by
  rcases lt_or_ge a b with hab | hba
  · rw [uIoc_of_le hab.le] at hf
    simp only [hab, true_and, integral_of_le hab.le,
      setIntegral_pos_iff_support_of_nonneg_ae hf hfi.1]
  · suffices (∫ x in a..b, f x ∂μ) <= 0 by simp only [this.not_gt, hba.not_gt, false_and]
    rw [integral_of_ge hba]

Depends on / 依赖: false_and, hab.le, hba.not_gt, integral_nonneg_of_ae, integral_of_ge, integral_of_le, lt_or_ge, neg_nonpos, not_gt, setIntegral_pos_iff_support_of_nonneg_ae, this.not_gt, true_and, uIoc_comm, uIoc_of_le
-/
theorem integral_pos_iff_support_of_nonneg_ae' (hf : 0 <=ᵐ[μ.restrict (Ι a b)] f)
    (hfi : IntervalIntegrable f μ a b) :
    (0 < ∫ x in a..b, f x ∂μ) ↔ a < b ∧ 0 < μ (support f inter Ioc a b) := by
  rcases lt_or_ge a b with hab | hba
  · rw [uIoc_of_le hab.le] at hf
    simp only [hab, true_and, integral_of_le hab.le,
      setIntegral_pos_iff_support_of_nonneg_ae hf hfi.1]
  · suffices (∫ x in a..b, f x ∂μ) <= 0 by simp only [this.not_gt, hba.not_gt, false_and]
    rw [integral_of_ge hba]; rw [neg_nonpos]
    rw [uIoc_comm]; rw [uIoc_of_le hba] at hf
    exact integral_nonneg_of_ae hf

/--
theorem `integral_pos_iff_support_of_nonneg_ae` / 定理 `integral_pos_iff_support_of_nonneg_ae`

English:
theorem integral_pos_iff_support_of_nonneg_ae
  given: (hf : 0 <=ᵐ[μ] f) (hfi : IntervalIntegrable f μ a b)
  proof: integral_pos_iff_support_of_nonneg_ae' (ae_mono Measure.restrict_le_self hf) hfi

中文:
定理 integral_pos_iff_support_of_nonneg_ae
  条件: (hf : 0 <=ᵐ[μ] f) (hfi : 整数erval整数egrable f μ a b)
  证明: integral_pos_iff_support_of_nonneg_ae' (ae_mono Measure.restrict_le_self hf) hfi

Depends on / 依赖: Measure, Measure.restrict_le_self, ae_mono, integral_pos_iff_support_of_nonneg_ae, restrict_le_self
-/
theorem integral_pos_iff_support_of_nonneg_ae (hf : 0 <=ᵐ[μ] f) (hfi : IntervalIntegrable f μ a b) :
    (0 < ∫ x in a..b, f x ∂μ) ↔ a < b ∧ 0 < μ (support f inter Ioc a b) :=
  integral_pos_iff_support_of_nonneg_ae' (ae_mono Measure.restrict_le_self hf) hfi

/--
theorem `intervalIntegral_pos_of_pos_on` / 定理 `intervalIntegral_pos_of_pos_on`

English:
theorem intervalIntegral_pos_of_pos_on
  statement: {f : Real -> Real} {a b : Real} (hfi : IntervalIntegrable f volume a b)
  proof: by
  have hsupp : Ioo a b subseteq support f inter Ioc a b := fun x hx =>
    ⟨mem_support.mpr (hpos x hx).ne', Ioo_subset_Ioc_self hx⟩
  have h₀ : 0 <=ᵐ[volume.restrict (uIoc a b)] f := by
    rw [EventuallyLE]; rw [uIoc_of_le hab.le]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_


中文:
定理 intervalIntegral_pos_of_pos_on
  结论: {f : 实数 -> 实数} {a b : 实数} (hfi : 整数erval整数egrable f volume a b)
  证明: by
  have hsupp : Ioo a b subseteq support f inter Ioc a b := fun x hx =>
    ⟨mem_support.mpr (hpos x hx).ne', Ioo_subset_Ioc_self hx⟩
  have h₀ : 0 <=ᵐ[volume.restrict (uIoc a b)] f := by
    rw [EventuallyLE]; rw [uIoc_of_le hab.le]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_


Depends on / 依赖: EventuallyLE, Ioo_ae_eq_Ioc, Ioo_subset_Ioc_self, Measure, Measure.measure_Ioo_pos, ae_restrict_iff, ae_restrict_of_ae_eq_of_ae_restrict, filter_upwards, hab.le, integral_pos_iff_support_of_nonneg_ae, measurableSet_Ioo, measure_Ioo_pos, measure_mono, mem_support, mem_support.mpr, restrict, subseteq, support, trans_le, uIoc_of_le
-/
theorem intervalIntegral_pos_of_pos_on {f : Real -> Real} {a b : Real} (hfi : IntervalIntegrable f volume a b)
    (hpos : forall x : Real, x in Ioo a b -> 0 < f x) (hab : a < b) : 0 < ∫ x : Real in a..b, f x := by
  have hsupp : Ioo a b subseteq support f inter Ioc a b := fun x hx =>
    ⟨mem_support.mpr (hpos x hx).ne', Ioo_subset_Ioc_self hx⟩
  have h₀ : 0 <=ᵐ[volume.restrict (uIoc a b)] f := by
    rw [EventuallyLE]; rw [uIoc_of_le hab.le]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with x hx using (hpos x hx).le
  rw [integral_pos_iff_support_of_nonneg_ae' h₀ hfi]
  exact ⟨hab, ((Measure.measure_Ioo_pos _).mpr hab).trans_le (measure_mono hsupp)⟩

/--
theorem `intervalIntegral_pos_of_pos` / 定理 `intervalIntegral_pos_of_pos`

English:
theorem intervalIntegral_pos_of_pos
  statement: {f : Real -> Real} {a b : Real}
  proof: intervalIntegral_pos_of_pos_on hfi (fun x _ => hpos x) hab

中文:
定理 intervalIntegral_pos_of_pos
  结论: {f : 实数 -> 实数} {a b : 实数}
  证明: intervalIntegral_pos_of_pos_on hfi (fun x _ => hpos x) hab

Depends on / 依赖: intervalIntegral_pos_of_pos_on
-/
theorem intervalIntegral_pos_of_pos {f : Real -> Real} {a b : Real}
    (hfi : IntervalIntegrable f MeasureSpace.volume a b) (hpos : forall x, 0 < f x) (hab : a < b) :
    0 < ∫ x in a..b, f x :=
  intervalIntegral_pos_of_pos_on hfi (fun x _ => hpos x) hab

/--
theorem `integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero` / 定理 `integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero`

English:
theorem integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero
  statement: (hab : a <= b)
  proof: by
  rw [← sub_pos]; rw [← integral_sub hgi hfi]; rw [integral_of_le hab]; rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · refine pos_iff_ne_zero.2 (mt (measure_mono_null ?_) hlt)
    exact fun x hx => (sub_pos.2 hx.out).ne'
  exacts [hle.mono fun x => sub_nonneg.2, hgi.1.sub hfi.1]

@[

中文:
定理 integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero
  结论: (hab : a <= b)
  证明: by
  rw [← sub_pos]; rw [← integral_sub hgi hfi]; rw [integral_of_le hab]; rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · refine pos_iff_ne_zero.2 (mt (measure_mono_null ?_) hlt)
    exact fun x hx => (sub_pos.2 hx.out).ne'
  exacts [hle.mono fun x => sub_nonneg.2, hgi.1.sub hfi.1]

@[

Depends on / 依赖: MeasureTheory, MeasureTheory.integral_pos_iff_support_of_nonneg_ae, exacts, hle.mono, hx.out, integral_of_le, integral_pos_iff_support_of_nonneg_ae, integral_sub, measure_mono_null, pos_iff_ne_zero, sub_nonneg, sub_pos
-/
theorem integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero (hab : a <= b)
    (hfi : IntervalIntegrable f μ a b) (hgi : IntervalIntegrable g μ a b)
    (hle : f <=ᵐ[μ.restrict (Ioc a b)] g) (hlt : μ.restrict (Ioc a b) {x | f x < g x} != 0) :
    (∫ x in a..b, f x ∂μ) < ∫ x in a..b, g x ∂μ := by
  rw [← sub_pos]; rw [← integral_sub hgi hfi]; rw [integral_of_le hab]; rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · refine pos_iff_ne_zero.2 (mt (measure_mono_null ?_) hlt)
    exact fun x hx => (sub_pos.2 hx.out).ne'
  exacts [hle.mono fun x => sub_nonneg.2, hgi.1.sub hfi.1]

@[deprecated (since := "2026-07-09")]
alias integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero :=
  integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero

/--
theorem `integral_lt_integral_of_continuousOn_of_le_of_exists_lt` / 定理 `integral_lt_integral_of_continuousOn_of_le_of_exists_lt`

English:
theorem integral_lt_integral_of_continuousOn_of_le_of_exists_lt
  statement: {f g : Real -> Real} {a b : Real}
  proof: by
  apply integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero hab.le
    (hfc.intervalIntegrable_of_Icc hab.le) (hgc.intervalIntegrable_of_Icc hab.le)
  · simpa only [measurableSet_Ioc, ae_restrict_eq]
      using! (ae_restrict_mem measurableSet_Ioc).mono hle
  contrapose! hlt
  have h_eq

中文:
定理 integral_lt_integral_of_continuousOn_of_le_of_exists_lt
  结论: {f g : 实数 -> 实数} {a b : 实数}
  证明: by
  apply integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero hab.le
    (hfc.intervalIntegrable_of_Icc hab.le) (hgc.intervalIntegrable_of_Icc hab.le)
  · simpa only [measurableSet_Ioc, ae_restrict_eq]
      using! (ae_restrict_mem measurableSet_Ioc).mono hle
  contrapose! hlt
  have h_eq

Depends on / 依赖: Eventually, Eventually.of_forall, EventuallyLE, EventuallyLE.antisymm, Ioc_a, Measure, Measure.restrict_congr_set, ae_iff, ae_restrict_eq, ae_restrict_iff, ae_restrict_mem, antisymm, contrapose, h_eq, hab.le, hfc.intervalIntegrable_of_Icc, hgc.intervalIntegrable_of_Icc, integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero, intervalIntegrable_of_Icc, measurableSet_Ioc
-/
theorem integral_lt_integral_of_continuousOn_of_le_of_exists_lt {f g : Real -> Real} {a b : Real}
    (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hle : forall x in Ioc a b, f x <= g x) (hlt : exists c in Icc a b, f c < g c) :
    (∫ x in a..b, f x) < ∫ x in a..b, g x := by
  apply integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero hab.le
    (hfc.intervalIntegrable_of_Icc hab.le) (hgc.intervalIntegrable_of_Icc hab.le)
  · simpa only [measurableSet_Ioc, ae_restrict_eq]
      using! (ae_restrict_mem measurableSet_Ioc).mono hle
  contrapose! hlt
  have h_eq : f =ᵐ[volume.restrict (Ioc a b)] g := by
    simp only [← not_le, ← ae_iff] at hlt
    exact EventuallyLE.antisymm ((ae_restrict_iff' measurableSet_Ioc).2 <|
      Eventually.of_forall hle) hlt
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at h_eq
  exact fun c hc => (Measure.eqOn_Icc_of_ae_eq volume hab.ne h_eq hfc hgc hc).ge

/--
theorem `integral_nonneg_of_ae_restrict` / 定理 `integral_nonneg_of_ae_restrict`

English:
theorem integral_nonneg_of_ae_restrict
  given: (hab : a <= b) (hf : 0 <=ᵐ[μ.restrict (Icc a b)] f)
  proof: by
  let H := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hf
  simpa only [integral_of_le hab] using setIntegral_nonneg_of_ae_restrict H

中文:
定理 integral_nonneg_of_ae_restrict
  条件: (hab : a <= b) (hf : 0 <=ᵐ[μ.restrict (Icc a b)] f)
  证明: by
  let H := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hf
  simpa only [integral_of_le hab] using setIntegral_nonneg_of_ae_restrict H

Depends on / 依赖: Ioc_subset_Icc_self, ae_restrict_of_ae_restrict_of_subset, integral_of_le, setIntegral_nonneg_of_ae_restrict
-/
theorem integral_nonneg_of_ae_restrict (hab : a <= b) (hf : 0 <=ᵐ[μ.restrict (Icc a b)] f) :
    0 <= ∫ u in a..b, f u ∂μ := by
  let H := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hf
  simpa only [integral_of_le hab] using setIntegral_nonneg_of_ae_restrict H

/--
theorem `integral_nonneg_of_ae` / 定理 `integral_nonneg_of_ae`

English:
theorem integral_nonneg_of_ae
  given: (hab : a <= b) (hf : 0 <=ᵐ[μ] f)
  statement: 0 <= ∫ u in a..b, f u ∂μ
  proof: integral_nonneg_of_ae_restrict hab ae_restrict_of_ae hf

中文:
定理 integral_nonneg_of_ae
  条件: (hab : a <= b) (hf : 0 <=ᵐ[μ] f)
  结论: 0 <= ∫ u in a..b, f u ∂μ
  证明: integral_nonneg_of_ae_restrict hab ae_restrict_of_ae hf

Depends on / 依赖: ae_restrict_of_ae, integral_nonneg_of_ae_restrict
-/
theorem integral_nonneg_of_ae (hab : a <= b) (hf : 0 <=ᵐ[μ] f) : 0 <= ∫ u in a..b, f u ∂μ :=
integral_nonneg_of_ae_restrict hab ae_restrict_of_ae hf

/--
theorem `integral_nonneg_of_forall` / 定理 `integral_nonneg_of_forall`

English:
theorem integral_nonneg_of_forall
  given: (hab : a <= b) (hf : forall u, 0 <= f u)
  statement: 0 <= ∫ u in a..b, f u ∂μ
  proof: integral_nonneg_of_ae hab Eventually.of_forall hf

中文:
定理 integral_nonneg_of_forall
  条件: (hab : a <= b) (hf : 对任意 u, 0 <= f u)
  结论: 0 <= ∫ u in a..b, f u ∂μ
  证明: integral_nonneg_of_ae hab Eventually.of_forall hf

Depends on / 依赖: Eventually, Eventually.of_forall, integral_nonneg_of_ae, of_forall
-/
theorem integral_nonneg_of_forall (hab : a <= b) (hf : forall u, 0 <= f u) : 0 <= ∫ u in a..b, f u ∂μ :=
integral_nonneg_of_ae hab Eventually.of_forall hf

/--
theorem `integral_nonneg` / 定理 `integral_nonneg`

English:
theorem integral_nonneg
  given: (hab : a <= b) (hf : forall u, u in Icc a b -> 0 <= f u)
  statement: 0 <= ∫ u in a..b, f u ∂μ
  proof: integral_nonneg_of_ae_restrict hab (ae_restrict_iff' measurableSet_Icc).mpr ae_of_all μ hf

中文:
定理 integral_nonneg
  条件: (hab : a <= b) (hf : 对任意 u, u in Icc a b -> 0 <= f u)
  结论: 0 <= ∫ u in a..b, f u ∂μ
  证明: integral_nonneg_of_ae_restrict hab (ae_restrict_iff' measurableSet_Icc).mpr ae_of_all μ hf

Depends on / 依赖: ae_of_all, ae_restrict_iff, integral_nonneg_of_ae_restrict, measurableSet_Icc
-/
theorem integral_nonneg (hab : a <= b) (hf : forall u, u in Icc a b -> 0 <= f u) : 0 <= ∫ u in a..b, f u ∂μ :=
integral_nonneg_of_ae_restrict hab (ae_restrict_iff' measurableSet_Icc).mpr ae_of_all μ hf

/--
theorem `abs_integral_le_integral_abs` / 定理 `abs_integral_le_integral_abs`

English:
theorem abs_integral_le_integral_abs
  given: (hab : a <= b)
  proof: by
  simpa only [← Real.norm_eq_abs] using norm_integral_le_integral_norm hab

中文:
定理 abs_integral_le_integral_abs
  条件: (hab : a <= b)
  证明: by
  simpa only [← Real.norm_eq_abs] using norm_integral_le_integral_norm hab

Depends on / 依赖: CompleteAtomicBooleanAlgebra, CompleteAtomicBooleanAlgebra.toCompletelyDistribLattice, Real.norm_eq_abs, norm_eq_abs, norm_integral_le_integral_norm, toCompletelyDistribLattice
-/
theorem abs_integral_le_integral_abs (hab : a <= b) :
    |∫ x in a..b, f x ∂μ| <= ∫ x in a..b, |f x| ∂μ := by
  simpa only [← Real.norm_eq_abs] using norm_integral_le_integral_norm hab

/--
lemma `integral_pos` / 引理 `integral_pos`

English:
lemma integral_pos
  statement: (hab : a < b)
  proof: (integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    continuousOn_const hfc hle hlt).trans_eq' (by simp)

中文:
引理 integral_pos
  结论: (hab : a < b)
  证明: (integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    continuousOn_const hfc hle hlt).trans_eq' (by simp)

Depends on / 依赖: continuousOn_const, integral_lt_integral_of_continuousOn_of_le_of_exists_lt, trans_eq
-/
lemma integral_pos (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hle : forall x in Ioc a b, 0 <= f x) (hlt : exists c in Icc a b, 0 < f c) :
    0 < ∫ x in a..b, f x :=
  (integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    continuousOn_const hfc hle hlt).trans_eq' (by simp)

section Mono

/--
theorem `integral_mono_interval` / 定理 `integral_mono_interval`

English:
theorem integral_mono_interval
  statement: {c d} (hca : c <= a) (hab : a <= b) (hbd : b <= d)
  proof: by
  rw [integral_of_le hab]; rw [integral_of_le (hca.trans (hab.trans hbd))]
  exact setIntegral_mono_set hfi.1 hf (Ioc_subset_Ioc hca hbd).eventuallyLE

中文:
定理 integral_mono_interval
  结论: {c d} (hca : c <= a) (hab : a <= b) (hbd : b <= d)
  证明: by
  rw [integral_of_le hab]; rw [integral_of_le (hca.trans (hab.trans hbd))]
  exact setIntegral_mono_set hfi.1 hf (Ioc_subset_Ioc hca hbd).eventuallyLE

Depends on / 依赖: Ioc_subset_Ioc, eventuallyLE, hab.trans, hca.trans, integral_of_le, setIntegral_mono_set
-/
theorem integral_mono_interval {c d} (hca : c <= a) (hab : a <= b) (hbd : b <= d)
    (hf : 0 <=ᵐ[μ.restrict (Ioc c d)] f) (hfi : IntervalIntegrable f μ c d) :
    (∫ x in a..b, f x ∂μ) <= ∫ x in c..d, f x ∂μ := by
  rw [integral_of_le hab]; rw [integral_of_le (hca.trans (hab.trans hbd))]
  exact setIntegral_mono_set hfi.1 hf (Ioc_subset_Ioc hca hbd).eventuallyLE

/--
theorem `abs_integral_mono_interval` / 定理 `abs_integral_mono_interval`

English:
theorem abs_integral_mono_interval
  statement: {c d} (h : Ι a b subseteq Ι c d) (hf : 0 <=ᵐ[μ.restrict (Ι c d)] f)
  proof: have hf' : 0 <=ᵐ[μ.restrict (Ι a b)] f := ae_mono (Measure.restrict_mono h le_rfl) hf
  calc
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| := abs_integral_eq_abs_integral_uIoc f
    _ = ∫ x in Ι a b, f x ∂μ := abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae hf')
    _ <= ∫ x in Ι c d, f x ∂μ

中文:
定理 abs_integral_mono_interval
  结论: {c d} (h : Ι a b subseteq Ι c d) (hf : 0 <=ᵐ[μ.restrict (Ι c d)] f)
  证明: have hf' : 0 <=ᵐ[μ.restrict (Ι a b)] f := ae_mono (Measure.restrict_mono h le_rfl) hf
  calc
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| := abs_integral_eq_abs_integral_uIoc f
    _ = ∫ x in Ι a b, f x ∂μ := abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae hf')
    _ <= ∫ x in Ι c d, f x ∂μ

Depends on / 依赖: Measure, Measure.restrict_mono, MeasureTheory, MeasureTheory.integral_nonneg_of_ae, abs_integral_eq_abs_integral_uIoc, abs_of_nonneg, ae_mono, eventuallyLE, h.eventuallyLE, hfi.def, integral_nonneg_of_ae, le_abs_self, le_rfl, restrict, restrict_mono, setIntegral_mono_set
-/
theorem abs_integral_mono_interval {c d} (h : Ι a b subseteq Ι c d) (hf : 0 <=ᵐ[μ.restrict (Ι c d)] f)
    (hfi : IntervalIntegrable f μ c d) : |∫ x in a..b, f x ∂μ| <= |∫ x in c..d, f x ∂μ| :=
  have hf' : 0 <=ᵐ[μ.restrict (Ι a b)] f := ae_mono (Measure.restrict_mono h le_rfl) hf
  calc
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| := abs_integral_eq_abs_integral_uIoc f
    _ = ∫ x in Ι a b, f x ∂μ := abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae hf')
    _ <= ∫ x in Ι c d, f x ∂μ := setIntegral_mono_set hfi.def' hf h.eventuallyLE
    _ <= |∫ x in Ι c d, f x ∂μ| := le_abs_self _
    _ = |∫ x in c..d, f x ∂μ| := (abs_integral_eq_abs_integral_uIoc f).symm

variable (hab : a <= b) (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b)
include hab hf hg

/--
theorem `integral_mono_ae_restrict` / 定理 `integral_mono_ae_restrict`

English:
theorem integral_mono_ae_restrict
  given: (h : f <=ᵐ[μ.restrict (Icc a b)] g)
  proof: by
let H := h.filter_mono ae_mono Measure.restrict_mono Ioc_subset_Icc_self le_refl μ
  simpa only [integral_of_le hab] using setIntegral_mono_ae_restrict hf.1 hg.1 H

中文:
定理 integral_mono_ae_restrict
  条件: (h : f <=ᵐ[μ.restrict (Icc a b)] g)
  证明: by
let H := h.filter_mono ae_mono Measure.restrict_mono Ioc_subset_Icc_self le_refl μ
  simpa only [integral_of_le hab] using setIntegral_mono_ae_restrict hf.1 hg.1 H

Depends on / 依赖: Ioc_subset_Icc_self, Measure, Measure.restrict_mono, ae_mono, filter_mono, h.filter_mono, integral_of_le, le_refl, restrict_mono, setIntegral_mono_ae_restrict
-/
theorem integral_mono_ae_restrict (h : f <=ᵐ[μ.restrict (Icc a b)] g) :
    (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ := by
let H := h.filter_mono ae_mono Measure.restrict_mono Ioc_subset_Icc_self le_refl μ
  simpa only [integral_of_le hab] using setIntegral_mono_ae_restrict hf.1 hg.1 H

/--
theorem `integral_mono_ae` / 定理 `integral_mono_ae`

English:
theorem integral_mono_ae
  given: (h : f <=ᵐ[μ] g)
  statement: (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ
  proof: by
  simpa only [integral_of_le hab] using setIntegral_mono_ae hf.1 hg.1 h

中文:
定理 integral_mono_ae
  条件: (h : f <=ᵐ[μ] g)
  结论: (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ
  证明: by
  simpa only [integral_of_le hab] using setIntegral_mono_ae hf.1 hg.1 h

Depends on / 依赖: integral_of_le, setIntegral_mono_ae
-/
theorem integral_mono_ae (h : f <=ᵐ[μ] g) : (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ := by
  simpa only [integral_of_le hab] using setIntegral_mono_ae hf.1 hg.1 h

/--
theorem `integral_mono_on` / 定理 `integral_mono_on`

English:
theorem integral_mono_on
  given: (h : forall x in Icc a b, f x <= g x)
  proof: by
let H x hx := h x Ioc_subset_Icc_self hx
  simpa only [integral_of_le hab] using setIntegral_mono_on hf.1 hg.1 measurableSet_Ioc H

中文:
定理 integral_mono_on
  条件: (h : 对任意 x in Icc a b, f x <= g x)
  证明: by
let H x hx := h x Ioc_subset_Icc_self hx
  simpa only [integral_of_le hab] using setIntegral_mono_on hf.1 hg.1 measurableSet_Ioc H

Depends on / 依赖: Ioc_subset_Icc_self, integral_of_le, measurableSet_Ioc, setIntegral_mono_on
-/
theorem integral_mono_on (h : forall x in Icc a b, f x <= g x) :
    (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ := by
let H x hx := h x Ioc_subset_Icc_self hx
  simpa only [integral_of_le hab] using setIntegral_mono_on hf.1 hg.1 measurableSet_Ioc H

/--
theorem `integral_mono_on_of_le_Ioo` / 定理 `integral_mono_on_of_le_Ioo`

English:
theorem integral_mono_on_of_le_Ioo
  given: [NullSingletonClass μ] (h : forall x in Ioo a b, f x <= g x)
  proof: by
  simp only [integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_mono_on
  · apply hf.1.mono Ioo_subset_Ioc_self le_rfl
  · apply hg.1.mono Ioo_subset_Ioc_self le_rfl
  · exact measurableSet_Ioo
  · exact h

中文:
定理 integral_mono_on_of_le_Ioo
  条件: [NullSingletonClass μ] (h : 对任意 x in Ioo a b, f x <= g x)
  证明: by
  simp only [integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_mono_on
  · apply hf.1.mono Ioo_subset_Ioc_self le_rfl
  · apply hg.1.mono Ioo_subset_Ioc_self le_rfl
  · exact measurableSet_Ioo
  · exact h

Depends on / 依赖: Ioo_subset_Ioc_self, integral_Ioc_eq_integral_Ioo, integral_of_le, le_rfl, measurableSet_Ioo, setIntegral_mono_on
-/
theorem integral_mono_on_of_le_Ioo [NullSingletonClass μ] (h : forall x in Ioo a b, f x <= g x) :
    (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ := by
  simp only [integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_mono_on
  · apply hf.1.mono Ioo_subset_Ioc_self le_rfl
  · apply hg.1.mono Ioo_subset_Ioc_self le_rfl
  · exact measurableSet_Ioo
  · exact h

/--
theorem `integral_mono` / 定理 `integral_mono`

English:
theorem integral_mono
  given: (h : f <= g)
  statement: (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ
  proof: integral_mono_ae hab hf hg ae_of_all _ h

中文:
定理 integral_mono
  条件: (h : f <= g)
  结论: (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ
  证明: integral_mono_ae hab hf hg ae_of_all _ h

Depends on / 依赖: ae_of_all, integral_mono_ae
-/
theorem integral_mono (h : f <= g) : (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ :=
integral_mono_ae hab hf hg ae_of_all _ h

end Mono

end

section HasSum

variable {μ : Measure Real} {f : Real -> E}

/--
theorem `_root_.MeasureTheory.Integrable.hasSum_intervalIntegral` / 定理 `_root_.MeasureTheory.Integrable.hasSum_intervalIntegral`

English:
theorem _root_.MeasureTheory.Integrable.hasSum_intervalIntegral
  given: (hfi : Integrable f μ) (y : Real)
  proof: by
  simp_rw [integral_of_le (le_add_of_nonneg_right zero_le_one)]
  rw [← setIntegral_univ]; rw [← iUnion_Ioc_add_intCast y]
  exact
    hasSum_integral_iUnion (fun i => measurableSet_Ioc) (pairwise_disjoint_Ioc_add_intCast y)
      hfi.integrableOn

中文:
定理 _root_.MeasureTheory.Integrable.hasSum_intervalIntegral
  条件: (hfi : 整数egrable f μ) (y : 实数)
  证明: by
  simp_rw [integral_of_le (le_add_of_nonneg_right zero_le_one)]
  rw [← setIntegral_univ]; rw [← iUnion_Ioc_add_intCast y]
  exact
    hasSum_integral_iUnion (fun i => measurableSet_Ioc) (pairwise_disjoint_Ioc_add_intCast y)
      hfi.integrableOn

Depends on / 依赖: hasSum_integral_iUnion, hfi.integrableOn, iUnion_Ioc_add_intCast, integrableOn, integral_of_le, le_add_of_nonneg_right, measurableSet_Ioc, pairwise_disjoint_Ioc_add_intCast, setIntegral_univ, simp_rw, zero_le_one
-/
theorem _root_.MeasureTheory.Integrable.hasSum_intervalIntegral (hfi : Integrable f μ) (y : Real) :
    HasSum (fun n : Int => ∫ x in y + n..y + n + 1, f x ∂μ) (∫ x, f x ∂μ) := by
  simp_rw [integral_of_le (le_add_of_nonneg_right zero_le_one)]
  rw [← setIntegral_univ]; rw [← iUnion_Ioc_add_intCast y]
  exact
    hasSum_integral_iUnion (fun i => measurableSet_Ioc) (pairwise_disjoint_Ioc_add_intCast y)
      hfi.integrableOn

/--
theorem `_root_.MeasureTheory.Integrable.hasSum_intervalIntegral_comp_add_int` / 定理 `_root_.MeasureTheory.Integrable.hasSum_intervalIntegral_comp_add_int`

English:
theorem _root_.MeasureTheory.Integrable.hasSum_intervalIntegral_comp_add_int
  given: (hfi : Integrable f)
  proof: by
  simpa only [integral_comp_add_right, zero_add, add_comm (1 : Real)] using
    hfi.hasSum_intervalIntegral 0

中文:
定理 _root_.MeasureTheory.Integrable.hasSum_intervalIntegral_comp_add_int
  条件: (hfi : 整数egrable f)
  证明: by
  simpa only [integral_comp_add_right, zero_add, add_comm (1 : Real)] using
    hfi.hasSum_intervalIntegral 0

Depends on / 依赖: add_comm, hasSum_intervalIntegral, hfi.hasSum_intervalIntegral, integral_comp_add_right, zero_add
-/
theorem _root_.MeasureTheory.Integrable.hasSum_intervalIntegral_comp_add_int (hfi : Integrable f) :
    HasSum (fun n : Int => ∫ x in (0 : Real)..(1 : Real), f (x + n)) (∫ x, f x) := by
  simpa only [integral_comp_add_right, zero_add, add_comm (1 : Real)] using
    hfi.hasSum_intervalIntegral 0

end HasSum

end intervalIntegral
