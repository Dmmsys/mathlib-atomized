/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

import Mathlib.MeasureTheory.VectorMeasure.AddContent

/-!
# Vector valued Stieltjes measure associated to a bounded variation function

Let `α` be a dense linear order with compact segments (e.g. `ℝ` or `ℝ≥0`), and `f : α → E` a
bounded variation function taking values in a complete additive normed group.
We associate to `f` a vector measure, called `BoundedVariationOn.vectorMeasure`. It gives
mass `f.rightLim b - f.leftLim a` to the interval `[a, b]` (with similar formulas for
other types of intervals).

For the construction, we define first an additive content on the set semiring of open-closed
intervals `(a, b]`, mapping this interval to `f.rightLim b - f.rightLim a`. To extend this content
to the whole sigma-algebra, by general extension theorems, it is enough to show that it is
dominated by a finite measure. For this, we can use the Stieltjes measure associated to the
variation of `f.rightLim`. The extension we get is not exactly the desired vector measure, as we
need to tweak things if there is a bot element `a`: the previous vector measure gives to `{a}` the
mass `0` instead of the desired `f.rightLim a - f a`, so we add a Dirac mass to correct this defect.
-/

@[expose] public section

open Filter Set MeasureTheory MeasurableSpace MeasureTheory
open scoped symmDiff Topology NNReal ENNReal

variable {α : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
  [SecondCountableTopology α] [CompactIccSpace α] [hα : MeasurableSpace α] [BorelSpace α]
  {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  {f : α -> E} {a b : α}

namespace BoundedVariationOn

/--
Definition of `stieltjesFunctionRightLim` / `stieltjesFunctionRightLim` 的定义

English:
definition stieltjesFunctionRightLim
  body: variationOnFromTo f.rightLim univ x₀ x
  mono' := by
    rw [← monotoneOn_univ]
    exact variationOnFromTo.monotoneOn hf.rightLim.locallyBoundedVariationOn (mem_univ _)
  right_continuous' x := hf.continuousWithinAt_variationOnFromTo_rightLim_Ici

中文:
定义 stieltjesFunctionRightLim
  定义体: variationOnFromTo f.rightLim univ x₀ x
  mono' := by
    rw [← monotoneOn_univ]
    exact variationOnFromTo.monotoneOn hf.rightLim.locallyBoundedVariationOn (mem_univ _)
  right_continuous' x := hf.continuousWithinAt_variationOnFromTo_rightLim_Ici
-/
@[simps] noncomputable def stieltjesFunctionRightLim
    (hf : BoundedVariationOn f univ) (x₀ : α) : StieltjesFunction α where
  toFun x := variationOnFromTo f.rightLim univ x₀ x
  mono' := by
    rw [← monotoneOn_univ]
    exact variationOnFromTo.monotoneOn hf.rightLim.locallyBoundedVariationOn (mem_univ _)
  right_continuous' x := hf.continuousWithinAt_variationOnFromTo_rightLim_Ici

open scoped Classical in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def measureAux (hf : BoundedVariationOn f univ)
  body: if h : Nonempty α then (hf.stieltjesFunctionRightLim h.some).measure else 0

中文:
定义 noncomputable
  签名: def measureAux (hf : BoundedVariationOn f univ)
  定义体: if h : Nonempty α then (hf.stieltjesFunctionRightLim h.some).measure else 0
-/
private noncomputable def measureAux (hf : BoundedVariationOn f univ) : Measure α :=
  if h : Nonempty α then (hf.stieltjesFunctionRightLim h.some).measure else 0

private instance (hf : BoundedVariationOn f univ) : IsFiniteMeasure hf.measureAux := by
  by_cases h : Nonempty α; swap
  · simp only [BoundedVariationOn.measureAux, h, ↓reduceDIte]
    infer_instance
  simp only [BoundedVariationOn.measureAux, h, ↓reduceDIte]
  apply StieltjesFunction.isFiniteMeasure_of_forall_abs_le
    (C := (eVariationOn f.rightLim univ).toReal) _ (fun x => ?_)
  exact variationOnFromTo.abs_le_eVariationOn hf.rightLim

/--
lemma `exists_vectorMeasure_le_measureAux` / 引理 `exists_vectorMeasure_le_measureAux`

English:
lemma exists_vectorMeasure_le_measureAux
  given: (hf : BoundedVariationOn f univ)
  proof: by
  /- We will apply the general extension theorem
  `VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom`. For this, we
  need to check that the additive content is bounded by the measure `measureAux`. -/
  rcases isEmpty_or_nonempty α with h'α | h'α
  · exact ⟨0, by simp

中文:
引理 存在_vectorMeasure_le_measureAux
  条件: (hf : BoundedVariationOn f univ)
  证明: by
  /- We will apply the general extension theorem
  `VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom`. For this, we
  need to check that the additive content is bounded by the measure `measureAux`. -/
  rcases isEmpty_or_nonempty α with h'α | h'α
  · exact ⟨0, by simp
-/
private lemma exists_vectorMeasure_le_measureAux (hf : BoundedVariationOn f univ) :
    exists m : VectorMeasure α E, (forall u v, u <= v -> m (Set.Ioc u v) = f.rightLim v - f.rightLim u) ∧
      m botSet = 0 ∧ forall s, ‖m s‖ₑ <= hf.measureAux s := by
  /- We will apply the general extension theorem
  `VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom`. For this, we
  need to check that the additive content is bounded by the measure `measureAux`. -/
  rcases isEmpty_or_nonempty α with h'α | h'α
  · exact ⟨0, by simp⟩
  let m := AddContent.onIoc f.rightLim
  have A : forall s in {s | exists u v, u <= v ∧ s = Ioc u v}, ‖m s‖ₑ <= hf.measureAux s := by
    rintro s ⟨u, v, huv, rfl⟩
    rw [AddContent.onIoc_apply huv]
    simp only [BoundedVariationOn.measureAux, h'α, ↓reduceDIte, StieltjesFunction.measure_Ioc,
      BoundedVariationOn.stieltjesFunctionRightLim_apply]
    rw [← variationOnFromTo.add hf.rightLim.locallyBoundedVariationOn
      (mem_univ h'α.some) (mem_univ u) (mem_univ v)]
    simp only [add_sub_cancel_left, variationOnFromTo, huv, ↓reduceIte, univ_inter]
    rw [ENNReal.ofReal_toReal]; swap
    · exact ((eVariationOn.mono _ (subset_univ _)).trans_lt hf.rightLim.lt_top).ne
    rw [← edist_eq_enorm_sub]
    exact eVariationOn.edist_le _ (by grind) (by grind)
  have B : hα = generateFrom {s | exists u v, u <= v ∧ s = Ioc u v} := by
    borelize α
    convert! borel_eq_generateFrom_Ioc_le α using 2
    grind only
  rcases VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom
    IsSetSemiring.Ioc A B with ⟨m', hm', h'm'⟩
  refine ⟨m', fun u v huv => ?_, ?_, h'm'⟩
  · rw [hm']
    · exact AddContent.onIoc_apply huv
    · exact ⟨u, v, huv, rfl⟩
  · apply enorm_eq_zero.1
    apply le_bot_iff.1
    exact (h'm' _).trans (by simp [measureAux, h'α])

open scoped Classical in
/--
Definition of `vectorMeasure` / `vectorMeasure` 的定义

English:
definition vectorMeasure
  signature: (hf : BoundedVariationOn f univ)
  body: hf.exists_vectorMeasure_le_measureAux.choose +
  (if h : exists x, IsBot x then VectorMeasure.dirac h.choose (f.rightLim h.choose - f h.choose) else 0)

中文:
定义 vectorMeasure
  签名: (hf : BoundedVariationOn f univ)
  定义体: hf.exists_vectorMeasure_le_measureAux.choose +
  (if h : exists x, IsBot x then VectorMeasure.dirac h.choose (f.rightLim h.choose - f h.choose) else 0)
-/
@[no_expose] noncomputable def vectorMeasure (hf : BoundedVariationOn f univ) : VectorMeasure α E :=
  hf.exists_vectorMeasure_le_measureAux.choose +
  (if h : exists x, IsBot x then VectorMeasure.dirac h.choose (f.rightLim h.choose - f h.choose) else 0)

/--
lemma `vectorMeasure_Ioc` / 引理 `vectorMeasure_Ioc`

English:
lemma vectorMeasure_Ioc
  given: (hf : BoundedVariationOn f univ) (h : a <= b)
  proof: by
  classical
  have A : hf.exists_vectorMeasure_le_measureAux.choose (Ioc a b) =
      f.rightLim b - f.rightLim a :=
    hf.exists_vectorMeasure_le_measureAux.choose_spec.1 a b h
  have B : (if hx : exists (x : α), IsBot x then VectorMeasure.dirac hx.choose
      (f.rightLim hx.choose - f hx.choo

中文:
引理 vectorMeasure_Ioc
  条件: (hf : BoundedVariationOn f univ) (h : a <= b)
  证明: by
  classical
  have A : hf.exists_vectorMeasure_le_measureAux.choose (Ioc a b) =
      f.rightLim b - f.rightLim a :=
    hf.exists_vectorMeasure_le_measureAux.choose_spec.1 a b h
  have B : (if hx : exists (x : α), IsBot x then VectorMeasure.dirac hx.choose
      (f.rightLim hx.choose - f hx.choo

Depends on / 依赖: Or.inl, VectorMeasure, VectorMeasure.dirac, VectorMeasure.dirac_apply_of_notMem, choose_spec, classical, dirac_apply_of_notMem, exists_vectorMeasure_le_measureAux, f.rightLim, hf.exists_vectorMeasure_le_measureAux.choose, hf.exists_vectorMeasure_le_measureAux.choose_spec, hx.choose, hx.choose_spec, mem_Ioc, not_and_or, not_le, not_lt, reduceDIte, rightLim
-/
lemma vectorMeasure_Ioc (hf : BoundedVariationOn f univ) (h : a <= b) :
    hf.vectorMeasure (Ioc a b) = f.rightLim b - f.rightLim a := by
  classical
  have A : hf.exists_vectorMeasure_le_measureAux.choose (Ioc a b) =
      f.rightLim b - f.rightLim a :=
    hf.exists_vectorMeasure_le_measureAux.choose_spec.1 a b h
  have B : (if hx : exists (x : α), IsBot x then VectorMeasure.dirac hx.choose
      (f.rightLim hx.choose - f hx.choose) else 0) (Ioc a b) = 0 := by
    by_cases hx : exists (x : α), IsBot x
    · simp only [hx, ↓reduceDIte]
      rw [VectorMeasure.dirac_apply_of_notMem]
      simp only [mem_Ioc, not_and_or, not_lt, not_le]
      exact Or.inl (hx.choose_spec _)
    · simp [hx]
  simp [vectorMeasure, A, B]

/--
lemma `vectorMeasure_singleton` / 引理 `vectorMeasure_singleton`

English:
lemma vectorMeasure_singleton
  given: (hf : BoundedVariationOn f univ)
  proof: by
  by_cases ha : IsBot a
  · have h : exists x, IsBot x := ⟨a, ha⟩
    have heqa : h.choose = a := subsingleton_isBot _ h.choose_spec ha
    have A : hf.exists_vectorMeasure_le_measureAux.choose {a} = 0 := by
      rw [← botSet_eq_singleton_of_isBot ha]
      exact hf.exists_vectorMeasure_le_measu

中文:
引理 vectorMeasure_singleton
  条件: (hf : BoundedVariationOn f univ)
  证明: by
  by_cases ha : IsBot a
  · have h : exists x, IsBot x := ⟨a, ha⟩
    have heqa : h.choose = a := subsingleton_isBot _ h.choose_spec ha
    have A : hf.exists_vectorMeasure_le_measureAux.choose {a} = 0 := by
      rw [← botSet_eq_singleton_of_isBot ha]
      exact hf.exists_vectorMeasure_le_measu

Depends on / 依赖: MeasurableSet, MeasurableSet.singleton, VectorMeasure, VectorMeasure.dirac_apply_of_mem, add_apply, botSet_eq_singleton_of_isBot, choose_spec, dirac_apply_of_mem, exists_vectorMeasure_le_measureAux, h.choose, h.choose_spec, hf.exists_vectorMeasure_le_measureAux.choose, hf.exists_vectorMeasure_le_measureAux.choose_spec, leftLim_eq_of_isBot, reduceDIte, singleton, sub_right_inj, subsingleton_isBot, vectorMeasure, zero_add
-/
lemma vectorMeasure_singleton (hf : BoundedVariationOn f univ) :
    hf.vectorMeasure {a} = f.rightLim a - f.leftLim a := by
  by_cases ha : IsBot a
  · have h : exists x, IsBot x := ⟨a, ha⟩
    have heqa : h.choose = a := subsingleton_isBot _ h.choose_spec ha
    have A : hf.exists_vectorMeasure_le_measureAux.choose {a} = 0 := by
      rw [← botSet_eq_singleton_of_isBot ha]
      exact hf.exists_vectorMeasure_le_measureAux.choose_spec.2.1
    simp only [vectorMeasure, h, ↓reduceDIte, add_apply, A, zero_add]
    rw [VectorMeasure.dirac_apply_of_mem (MeasurableSet.singleton a)]
    · simpa only [heqa, sub_right_inj] using (leftLim_eq_of_isBot ha).symm
    · simp [heqa]
  obtain ⟨b, hb⟩ : exists b, b < a := by simpa only [IsBot, not_forall, not_le] using ha
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
      exists u : Nat -> α, StrictMono u ∧ (forall n : Nat, u n in Ioo b a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto' hb
  replace u_lt_a n : u n < a := (u_lt_a n).2
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine Subset.antisymm (fun x hx => by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx => ?_
    replace hx : forall (i : Nat), u i < x ∧ x <= a := by simpa using hx
    have : a <= x := le_of_tendsto' u_lim fun n => (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n => hf.vectorMeasure (Ioc (u n) a)) atTop (𝓝 (hf.vectorMeasure {a})) := by
    rw [A]
    apply VectorMeasure.tendsto_vectorMeasure_iInter_atTop_nat ?_ (fun n => measurableSet_Ioc)
    exact fun m n hmn => Ioc_subset_Ioc_left (u_mono.monotone hmn)
  have L2 : Tendsto (fun n => hf.vectorMeasure (Ioc (u n) a)) atTop
      (𝓝 (f.rightLim a - f.leftLim a)) := by
    simp_rw [hf.vectorMeasure_Ioc (u_lt_a _).le]
    apply tendsto_const_nhds.sub
    have : Tendsto u atTop (𝓝[<] a) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      u_lim (Eventually.of_forall u_lt_a)
    convert! (hf.rightLim.tendsto_leftLim a).comp this using 2
    have : (𝓝[<] a).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot]; rw [closure_Iio' ⟨b]; rw [hb⟩]
      exact self_mem_Iic
    exact (leftLim_rightLim (hf.tendsto_leftLim _)).symm
  exact tendsto_nhds_unique L1 L2

/--
lemma `vectorMeasure_Icc` / 引理 `vectorMeasure_Icc`

English:
lemma vectorMeasure_Icc
  given: (hf : BoundedVariationOn f univ) (h : a <= b)
  proof: by
  rw [← Icc_union_Ioc_eq_Icc le_rfl h]; rw [VectorMeasure.of_union (by simp)
    measurableSet_Icc measurableSet_Ioc]; rw [Icc_self]; rw [hf.vectorMeasure_singleton]; rw [hf.vectorMeasure_Ioc h]
  simp

中文:
引理 vectorMeasure_Icc
  条件: (hf : BoundedVariationOn f univ) (h : a <= b)
  证明: by
  rw [← Icc_union_Ioc_eq_Icc le_rfl h]; rw [VectorMeasure.of_union (by simp)
    measurableSet_Icc measurableSet_Ioc]; rw [Icc_self]; rw [hf.vectorMeasure_singleton]; rw [hf.vectorMeasure_Ioc h]
  simp

Depends on / 依赖: Icc_self, Icc_union_Ioc_eq_Icc, VectorMeasure, VectorMeasure.of_union, hf.vectorMeasure_Ioc, hf.vectorMeasure_singleton, le_rfl, measurableSet_Icc, measurableSet_Ioc, of_union, vectorMeasure_Ioc, vectorMeasure_singleton
-/
lemma vectorMeasure_Icc (hf : BoundedVariationOn f univ) (h : a <= b) :
    hf.vectorMeasure (Icc a b) = f.rightLim b - f.leftLim a := by
  rw [← Icc_union_Ioc_eq_Icc le_rfl h]; rw [VectorMeasure.of_union (by simp)
    measurableSet_Icc measurableSet_Ioc]; rw [Icc_self]; rw [hf.vectorMeasure_singleton]; rw [hf.vectorMeasure_Ioc h]
  simp

/--
theorem `vectorMeasure_Ioo` / 定理 `vectorMeasure_Ioo`

English:
theorem vectorMeasure_Ioo
  given: (hf : BoundedVariationOn f univ) (h : a < b)
  proof: by
  have := hf.vectorMeasure_Ioc h.le
  rw [← Ioo_union_Icc_eq_Ioc h le_rfl]; rw [VectorMeasure.of_union (by simp) measurableSet_Ioo
    measurableSet_Icc]; rw [hf.vectorMeasure_Icc le_rfl] at this
  grind

中文:
定理 vectorMeasure_Ioo
  条件: (hf : BoundedVariationOn f univ) (h : a < b)
  证明: by
  have := hf.vectorMeasure_Ioc h.le
  rw [← Ioo_union_Icc_eq_Ioc h le_rfl]; rw [VectorMeasure.of_union (by simp) measurableSet_Ioo
    measurableSet_Icc]; rw [hf.vectorMeasure_Icc le_rfl] at this
  grind

Depends on / 依赖: Ioo_union_Icc_eq_Ioc, VectorMeasure, VectorMeasure.of_union, h.le, hf.vectorMeasure_Icc, hf.vectorMeasure_Ioc, le_rfl, measurableSet_Icc, measurableSet_Ioo, of_union, vectorMeasure_Icc, vectorMeasure_Ioc
-/
theorem vectorMeasure_Ioo (hf : BoundedVariationOn f univ) (h : a < b) :
    hf.vectorMeasure (Ioo a b) = f.leftLim b - f.rightLim a := by
  have := hf.vectorMeasure_Ioc h.le
  rw [← Ioo_union_Icc_eq_Ioc h le_rfl]; rw [VectorMeasure.of_union (by simp) measurableSet_Ioo
    measurableSet_Icc]; rw [hf.vectorMeasure_Icc le_rfl] at this
  grind

/--
theorem `vectorMeasure_Ico` / 定理 `vectorMeasure_Ico`

English:
theorem vectorMeasure_Ico
  given: (hf : BoundedVariationOn f univ) (h : a <= b)
  proof: by
  rcases h.eq_or_lt with rfl | h'
  · simp
  rw [← Icc_union_Ioo_eq_Ico le_rfl h']; rw [VectorMeasure.of_union (by simp) measurableSet_Icc
    measurableSet_Ioo]; rw [hf.vectorMeasure_Icc le_rfl]; rw [hf.vectorMeasure_Ioo h']
  abel

中文:
定理 vectorMeasure_Ico
  条件: (hf : BoundedVariationOn f univ) (h : a <= b)
  证明: by
  rcases h.eq_or_lt with rfl | h'
  · simp
  rw [← Icc_union_Ioo_eq_Ico le_rfl h']; rw [VectorMeasure.of_union (by simp) measurableSet_Icc
    measurableSet_Ioo]; rw [hf.vectorMeasure_Icc le_rfl]; rw [hf.vectorMeasure_Ioo h']
  abel

Depends on / 依赖: Icc_union_Ioo_eq_Ico, VectorMeasure, VectorMeasure.of_union, eq_or_lt, h.eq_or_lt, hf.vectorMeasure_Icc, hf.vectorMeasure_Ioo, le_rfl, measurableSet_Icc, measurableSet_Ioo, of_union, vectorMeasure_Icc, vectorMeasure_Ioo
-/
theorem vectorMeasure_Ico (hf : BoundedVariationOn f univ) (h : a <= b) :
    hf.vectorMeasure (Ico a b) = f.leftLim b - f.leftLim a := by
  rcases h.eq_or_lt with rfl | h'
  · simp
  rw [← Icc_union_Ioo_eq_Ico le_rfl h']; rw [VectorMeasure.of_union (by simp) measurableSet_Icc
    measurableSet_Ioo]; rw [hf.vectorMeasure_Icc le_rfl]; rw [hf.vectorMeasure_Ioo h']
  abel

/--
theorem `vectorMeasure_Ici` / 定理 `vectorMeasure_Ici`

English:
theorem vectorMeasure_Ici
  given: (hf : BoundedVariationOn f univ) (a : α)
  proof: by
  have : Nonempty α := ⟨a⟩
  have hlim : Tendsto f atTop (𝓝 (limUnder atTop f)) := hf.tendsto_atTop_limUnder
  obtain ⟨u, u_mono, hu⟩ : exists u, Monotone u ∧ Tendsto u atTop atTop :=
    Filter.exists_seq_monotone_tendsto_atTop_atTop α
  have A : Tendsto (fun n => hf.vectorMeasure (Icc a (u n)))

中文:
定理 vectorMeasure_Ici
  条件: (hf : BoundedVariationOn f univ) (a : α)
  证明: by
  have : Nonempty α := ⟨a⟩
  have hlim : Tendsto f atTop (𝓝 (limUnder atTop f)) := hf.tendsto_atTop_limUnder
  obtain ⟨u, u_mono, hu⟩ : exists u, Monotone u ∧ Tendsto u atTop atTop :=
    Filter.exists_seq_monotone_tendsto_atTop_atTop α
  have A : Tendsto (fun n => hf.vectorMeasure (Icc a (u n)))

Depends on / 依赖: Filter, Filter.exists_seq_monotone_tendsto_atTop_atTop, Icc_subset_Ici_self, Ici_mem_atTop, Monotone, Nonempty, Tendsto, eventually, exists_seq_monotone_tendsto_atTop_atTop, hf.tendsto_atTop_limUnder, hf.vectorMeasure, hu.eventually, le_antisymm, limUnder, tendsto_atTop_limUnder, u_mono, vectorMeasure
-/
theorem vectorMeasure_Ici (hf : BoundedVariationOn f univ) (a : α) :
    hf.vectorMeasure (Ici a) = limUnder atTop f - f.leftLim a := by
  have : Nonempty α := ⟨a⟩
  have hlim : Tendsto f atTop (𝓝 (limUnder atTop f)) := hf.tendsto_atTop_limUnder
  obtain ⟨u, u_mono, hu⟩ : exists u, Monotone u ∧ Tendsto u atTop atTop :=
    Filter.exists_seq_monotone_tendsto_atTop_atTop α
  have A : Tendsto (fun n => hf.vectorMeasure (Icc a (u n))) atTop
      (𝓝 (hf.vectorMeasure (Ici a))) := by
    have : Ici a = ⋃ n, Icc a (u n) := by
      apply le_antisymm ?_ (by simp [Icc_subset_Ici_self])
      intro x (hx : a <= x)
      simpa [hx] using (hu.eventually (Ici_mem_atTop x)).exists
    rw [this]
    exact hf.vectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat (s := fun n => Icc a (u n))
      (fun i j hij x hx => by grind [Monotone]) (fun i => measurableSet_Icc)
  have B : Tendsto (fun n => hf.vectorMeasure (Icc a (u n))) atTop
      (𝓝 (limUnder atTop f - f.leftLim a)) := by
    have : (fun n => f.rightLim (u n) - f.leftLim a) =ᶠ[atTop]
        (fun n => hf.vectorMeasure (Icc a (u n))) := by
      have : forallᶠ n in atTop, a <= u n := by
        simp only [tendsto_atTop, eventually_atTop] at hu
        simp [hu]
      filter_upwards [this] with n hn using by rw [hf.vectorMeasure_Icc hn]
    apply Tendsto.congr' this
    apply Tendsto.sub ?_ tendsto_const_nhds
    exact (tendsto_rightLim_atTop_of_tendsto hlim).comp hu
  exact tendsto_nhds_unique A B

/--
theorem `vectorMeasure_Ioi` / 定理 `vectorMeasure_Ioi`

English:
theorem vectorMeasure_Ioi
  given: (hf : BoundedVariationOn f univ) (a : α)
  proof: by
  have := hf.vectorMeasure_Ici a
  rw [← Icc_union_Ioi_eq_Ici le_rfl]; rw [VectorMeasure.of_union (by simp) measurableSet_Icc
    measurableSet_Ioi]; rw [hf.vectorMeasure_Icc le_rfl] at this
  grind

中文:
定理 vectorMeasure_Ioi
  条件: (hf : BoundedVariationOn f univ) (a : α)
  证明: by
  have := hf.vectorMeasure_Ici a
  rw [← Icc_union_Ioi_eq_Ici le_rfl]; rw [VectorMeasure.of_union (by simp) measurableSet_Icc
    measurableSet_Ioi]; rw [hf.vectorMeasure_Icc le_rfl] at this
  grind

Depends on / 依赖: Icc_union_Ioi_eq_Ici, VectorMeasure, VectorMeasure.of_union, hf.vectorMeasure_Icc, hf.vectorMeasure_Ici, le_rfl, measurableSet_Icc, measurableSet_Ioi, of_union, vectorMeasure_Icc, vectorMeasure_Ici
-/
theorem vectorMeasure_Ioi (hf : BoundedVariationOn f univ) (a : α) :
    hf.vectorMeasure (Ioi a) = limUnder atTop f - f.rightLim a := by
  have := hf.vectorMeasure_Ici a
  rw [← Icc_union_Ioi_eq_Ici le_rfl]; rw [VectorMeasure.of_union (by simp) measurableSet_Icc
    measurableSet_Ioi]; rw [hf.vectorMeasure_Icc le_rfl] at this
  grind

/--
theorem `vectorMeasure_Iic` / 定理 `vectorMeasure_Iic`

English:
theorem vectorMeasure_Iic
  given: (hf : BoundedVariationOn f univ) (a : α)
  proof: by
  have : Nonempty α := ⟨a⟩
  have hlim : Tendsto f atBot (𝓝 (limUnder atBot f)) := hf.tendsto_atBot_limUnder
  obtain ⟨u, u_anti, hu⟩ : exists u, Antitone u ∧ Tendsto u atTop atBot :=
    Filter.exists_seq_antitone_tendsto_atTop_atBot α
  have A : Tendsto (fun n => hf.vectorMeasure (Icc (u n) a))

中文:
定理 vectorMeasure_Iic
  条件: (hf : BoundedVariationOn f univ) (a : α)
  证明: by
  have : Nonempty α := ⟨a⟩
  have hlim : Tendsto f atBot (𝓝 (limUnder atBot f)) := hf.tendsto_atBot_limUnder
  obtain ⟨u, u_anti, hu⟩ : exists u, Antitone u ∧ Tendsto u atTop atBot :=
    Filter.exists_seq_antitone_tendsto_atTop_atBot α
  have A : Tendsto (fun n => hf.vectorMeasure (Icc (u n) a))

Depends on / 依赖: Antitone, Filter, Filter.exists_seq_antitone_tendsto_atTop_atBot, Icc_subset_Iic_self, Iic_mem_atBot, Nonempty, Tendsto, eventually, exists_seq_antitone_tendsto_atTop_atBot, hf.tendsto_atBot_limUnder, hf.vectorMeasure, hu.eventually, le_antisymm, limUnder, tendsto_atBot_limUnder, u_anti, vectorMeasure
-/
theorem vectorMeasure_Iic (hf : BoundedVariationOn f univ) (a : α) :
    hf.vectorMeasure (Iic a) = f.rightLim a - limUnder atBot f := by
  have : Nonempty α := ⟨a⟩
  have hlim : Tendsto f atBot (𝓝 (limUnder atBot f)) := hf.tendsto_atBot_limUnder
  obtain ⟨u, u_anti, hu⟩ : exists u, Antitone u ∧ Tendsto u atTop atBot :=
    Filter.exists_seq_antitone_tendsto_atTop_atBot α
  have A : Tendsto (fun n => hf.vectorMeasure (Icc (u n) a)) atTop
      (𝓝 (hf.vectorMeasure (Iic a))) := by
    have : Iic a = ⋃ n, Icc (u n) a := by
      apply le_antisymm ?_ (by simp [Icc_subset_Iic_self])
      intro x (hx : x <= a)
      simpa [hx] using (hu.eventually (Iic_mem_atBot x)).exists
    rw [this]
    exact hf.vectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat (s := fun n => Icc (u n) a)
      (fun i j hij x hx => by grind [Antitone]) (fun i => measurableSet_Icc)
  have B : Tendsto (fun n => hf.vectorMeasure (Icc (u n) a)) atTop
      (𝓝 (f.rightLim a - limUnder atBot f)) := by
    have : (fun n => f.rightLim a - f.leftLim (u n)) =ᶠ[atTop]
        (fun n => hf.vectorMeasure (Icc (u n) a)) := by
      have : forallᶠ n in atTop, u n <= a := by
        simp only [tendsto_atBot, eventually_atTop] at hu
        simp [hu]
      filter_upwards [this] with n hn using by rw [hf.vectorMeasure_Icc hn]
    apply Tendsto.congr' this
    apply Tendsto.sub tendsto_const_nhds
    exact (tendsto_leftLim_atBot_of_tendsto hf.tendsto_atBot_limUnder).comp hu
  exact tendsto_nhds_unique A B

/--
theorem `vectorMeasure_Iio` / 定理 `vectorMeasure_Iio`

English:
theorem vectorMeasure_Iio
  given: (hf : BoundedVariationOn f univ) (a : α)
  proof: by
  have := hf.vectorMeasure_Iic a
  rw [← Iio_union_Icc_eq_Iic le_rfl]; rw [VectorMeasure.of_union (by simp) measurableSet_Iio
    measurableSet_Icc]; rw [hf.vectorMeasure_Icc le_rfl] at this
  grind

中文:
定理 vectorMeasure_Iio
  条件: (hf : BoundedVariationOn f univ) (a : α)
  证明: by
  have := hf.vectorMeasure_Iic a
  rw [← Iio_union_Icc_eq_Iic le_rfl]; rw [VectorMeasure.of_union (by simp) measurableSet_Iio
    measurableSet_Icc]; rw [hf.vectorMeasure_Icc le_rfl] at this
  grind

Depends on / 依赖: Iio_union_Icc_eq_Iic, VectorMeasure, VectorMeasure.of_union, hf.vectorMeasure_Icc, hf.vectorMeasure_Iic, le_rfl, measurableSet_Icc, measurableSet_Iio, of_union, vectorMeasure_Icc, vectorMeasure_Iic
-/
theorem vectorMeasure_Iio (hf : BoundedVariationOn f univ) (a : α) :
    hf.vectorMeasure (Iio a) = f.leftLim a - limUnder atBot f := by
  have := hf.vectorMeasure_Iic a
  rw [← Iio_union_Icc_eq_Iic le_rfl]; rw [VectorMeasure.of_union (by simp) measurableSet_Iio
    measurableSet_Icc]; rw [hf.vectorMeasure_Icc le_rfl] at this
  grind

/--
theorem `vectorMeasure_univ` / 定理 `vectorMeasure_univ`

English:
theorem vectorMeasure_univ
  given: (hf : BoundedVariationOn f univ)
  proof: by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [eq_empty_of_isEmpty, filter_eq_bot_of_isEmpty]
  rw [← Iio_union_Ici (a := hα.some)]; rw [VectorMeasure.of_union (by simp) measurableSet_Iio
    measurableSet_Ici]; rw [hf.vectorMeasure_Iio]; rw [hf.vectorMeasure_Ici]
  abel

中文:
定理 vectorMeasure_univ
  条件: (hf : BoundedVariationOn f univ)
  证明: by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [eq_empty_of_isEmpty, filter_eq_bot_of_isEmpty]
  rw [← Iio_union_Ici (a := hα.some)]; rw [VectorMeasure.of_union (by simp) measurableSet_Iio
    measurableSet_Ici]; rw [hf.vectorMeasure_Iio]; rw [hf.vectorMeasure_Ici]
  abel

Depends on / 依赖: Iio_union_Ici, VectorMeasure, VectorMeasure.of_union, eq_empty_of_isEmpty, filter_eq_bot_of_isEmpty, hf.vectorMeasure_Ici, hf.vectorMeasure_Iio, isEmpty_or_nonempty, measurableSet_Ici, measurableSet_Iio, of_union, vectorMeasure_Ici, vectorMeasure_Iio
-/
theorem vectorMeasure_univ (hf : BoundedVariationOn f univ) :
    hf.vectorMeasure univ = limUnder atTop f - limUnder atBot f := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [eq_empty_of_isEmpty, filter_eq_bot_of_isEmpty]
  rw [← Iio_union_Ici (a := hα.some)]; rw [VectorMeasure.of_union (by simp) measurableSet_Iio
    measurableSet_Ici]; rw [hf.vectorMeasure_Iio]; rw [hf.vectorMeasure_Ici]
  abel

end BoundedVariationOn
