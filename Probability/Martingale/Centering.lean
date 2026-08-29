/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# Centering lemma for stochastic processes

Any `ℕ`-indexed stochastic process which is strongly adapted and integrable can be written as the
sum of a martingale and a predictable process. This result is also known as
**Doob's decomposition theorem**. From a process `f`, a filtration `ℱ` and a measure `μ`, we define
two processes `martingalePart f ℱ μ` and `predictablePart f ℱ μ`.

## Main definitions

* `MeasureTheory.predictablePart f ℱ μ`: a predictable process such that
  `f = predictablePart f ℱ μ + martingalePart f ℱ μ`
* `MeasureTheory.martingalePart f ℱ μ`: a martingale such that
  `f = predictablePart f ℱ μ + martingalePart f ℱ μ`

## Main statements

* `MeasureTheory.stronglyAdapted_predictablePart`: `(fun n => predictablePart f ℱ μ (n+1))`
  is strongly adapted.
  That is, `predictablePart` is predictable.
* `MeasureTheory.martingale_martingalePart`: `martingalePart f ℱ μ` is a martingale.

-/

@[expose] public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace Real E] {f g : Nat -> Ω -> E} {ℱ : Filtration Nat m0}

/--
Definition of `predictablePart` / `predictablePart` 的定义

English:
definition predictablePart
  signature: {m0 : MeasurableSpace Ω} (f : Nat -> Ω -> E) (ℱ : Filtration Nat m0)
  body: fun n => ∑ i in Finset.range n, μ[f (i + 1) - f i | ℱ i]

@[simp]

中文:
定义 predictablePart
  签名: {m0 : MeasurableSpace Ω} (f : 自然数 -> Ω -> E) (ℱ : Filtration 自然数 m0)
  定义体: fun n => ∑ i in Finset.range n, μ[f (i + 1) - f i | ℱ i]

@[simp]

Depends on / 依赖: Finset, Finset.range
-/
noncomputable def predictablePart {m0 : MeasurableSpace Ω} (f : Nat -> Ω -> E) (ℱ : Filtration Nat m0)
    (μ : Measure Ω) : Nat -> Ω -> E := fun n => ∑ i in Finset.range n, μ[f (i + 1) - f i | ℱ i]

@[simp]
/--
theorem `predictablePart_zero` / 定理 `predictablePart_zero`

English:
theorem predictablePart_zero
  statement: predictablePart f ℱ μ 0 = 0
  proof: by
  simp_rw [predictablePart, Finset.range_zero, Finset.sum_empty]

中文:
定理 predictablePart_zero
  结论: predictablePart f ℱ μ 0 = 0
  证明: by
  simp_rw [predictablePart, Finset.range_zero, Finset.sum_empty]

Depends on / 依赖: Finset, Finset.range_zero, Finset.sum_empty, predictablePart, range_zero, simp_rw, sum_empty
-/
theorem predictablePart_zero : predictablePart f ℱ μ 0 = 0 := by
  simp_rw [predictablePart, Finset.range_zero, Finset.sum_empty]

/--
lemma `predictablePart_add_one` / 引理 `predictablePart_add_one`

English:
lemma predictablePart_add_one
  given: (n : Nat)
  proof: by
  simp [predictablePart, Finset.sum_range_add]

中文:
引理 predictablePart_add_one
  条件: (n : 自然数)
  证明: by
  simp [predictablePart, Finset.sum_range_add]

Depends on / 依赖: Finset, Finset.sum_range_add, predictablePart, sum_range_add
-/
lemma predictablePart_add_one (n : Nat) :
    predictablePart f ℱ μ (n + 1) =
      predictablePart f ℱ μ n + μ[f (n + 1) - f n | ℱ n] := by
  simp [predictablePart, Finset.sum_range_add]

/--
lemma `predictablePart_smul` / 引理 `predictablePart_smul`

English:
lemma predictablePart_smul
  given: [CompleteSpace E] (c : Real) (n : Nat)
  proof: by
  simp only [predictablePart, Finset.smul_sum]
  refine eventuallyEq_sum fun i hi => ?_
  simp [← smul_sub, condExp_smul]

中文:
引理 predictablePart_smul
  条件: [CompleteSpace E] (c : 实数) (n : 自然数)
  证明: by
  simp only [predictablePart, Finset.smul_sum]
  refine eventuallyEq_sum fun i hi => ?_
  simp [← smul_sub, condExp_smul]

Depends on / 依赖: Finset, Finset.smul_sum, condExp_smul, eventuallyEq_sum, predictablePart, smul_sub, smul_sum
-/
lemma predictablePart_smul [CompleteSpace E] (c : Real) (n : Nat) :
    predictablePart (c • f) ℱ μ n =ᵐ[μ] c • predictablePart f ℱ μ n := by
  simp only [predictablePart, Finset.smul_sum]
  refine eventuallyEq_sum fun i hi => ?_
  simp [← smul_sub, condExp_smul]

/--
lemma `predictablePart_add` / 引理 `predictablePart_add`

English:
lemma predictablePart_add
  statement: [CompleteSpace E] (hfint : forall n, Integrable (f n) μ)
  proof: by
  simp only [predictablePart, ← Finset.sum_add_distrib]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[(f (i + 1) - f i) + (g (i + 1) - g i) | ℱ i] := by simp; abel_nf; rfl
  _ =ᵐ[μ] _ := by apply condExp_add ((hfint (i + 1)).sub (hfint i)) ((hgint (i + 1)).sub (hgint i))

中文:
引理 predictablePart_add
  结论: [CompleteSpace E] (hfint : 对任意 n, 整数egrable (f n) μ)
  证明: by
  simp only [predictablePart, ← Finset.sum_add_distrib]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[(f (i + 1) - f i) + (g (i + 1) - g i) | ℱ i] := by simp; abel_nf; rfl
  _ =ᵐ[μ] _ := by apply condExp_add ((hfint (i + 1)).sub (hfint i)) ((hgint (i + 1)).sub (hgint i))

Depends on / 依赖: Finset, Finset.sum_add_distrib, abel_nf, condExp_add, eventuallyEq_sum, predictablePart, sum_add_distrib
-/
lemma predictablePart_add [CompleteSpace E] (hfint : forall n, Integrable (f n) μ)
    (hgint : forall n, Integrable (g n) μ) (n : Nat) :
    predictablePart (f + g) ℱ μ n =ᵐ[μ] predictablePart f ℱ μ n + predictablePart g ℱ μ n := by
  simp only [predictablePart, ← Finset.sum_add_distrib]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[(f (i + 1) - f i) + (g (i + 1) - g i) | ℱ i] := by simp; abel_nf; rfl
  _ =ᵐ[μ] _ := by apply condExp_add ((hfint (i + 1)).sub (hfint i)) ((hgint (i + 1)).sub (hgint i))

/--
lemma `Martingale.predictablePart_eq_zero` / 引理 `Martingale.predictablePart_eq_zero`

English:
lemma Martingale.predictablePart_eq_zero
  given: [CompleteSpace E] (hf : Martingale f ℱ μ) (n : Nat)
  proof: by
  rw [predictablePart]; rw [← Finset.sum_const_zero (s := Finset.range n)]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[f (i + 1) | ℱ i] - μ[f i | ℱ i] := by
    simp [condExp_sub (hf.integrable (i + 1)) (hf.integrable i) (ℱ i)]
  _ =ᵐ[μ] f i - f i := (hf.condExp_ae_eq (Nat.le_succ

中文:
引理 Martingale.predictablePart_eq_zero
  条件: [CompleteSpace E] (hf : Martingale f ℱ μ) (n : 自然数)
  证明: by
  rw [predictablePart]; rw [← Finset.sum_const_zero (s := Finset.range n)]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[f (i + 1) | ℱ i] - μ[f i | ℱ i] := by
    simp [condExp_sub (hf.integrable (i + 1)) (hf.integrable i) (ℱ i)]
  _ =ᵐ[μ] f i - f i := (hf.condExp_ae_eq (Nat.le_succ

Depends on / 依赖: Finset, Finset.range, Finset.sum_const_zero, Nat.le_succ, condExp_ae_eq, condExp_sub, eventuallyEq_sum, hf.condExp_ae_eq, hf.integrable, integrable, le_rfl, le_succ, predictablePart, sum_const_zero
-/
lemma Martingale.predictablePart_eq_zero [CompleteSpace E] (hf : Martingale f ℱ μ) (n : Nat) :
    predictablePart f ℱ μ n =ᵐ[μ] 0 := by
  rw [predictablePart]; rw [← Finset.sum_const_zero (s := Finset.range n)]
  refine eventuallyEq_sum fun i hi => ?_
  calc
  _ =ᵐ[μ] μ[f (i + 1) | ℱ i] - μ[f i | ℱ i] := by
    simp [condExp_sub (hf.integrable (i + 1)) (hf.integrable i) (ℱ i)]
  _ =ᵐ[μ] f i - f i := (hf.condExp_ae_eq (Nat.le_succ i)).sub (hf.condExp_ae_eq le_rfl)
  _ =ᵐ[μ] 0 := by simp

/--
lemma `Submartingale.monotone_predictablePart` / 引理 `Submartingale.monotone_predictablePart`

English:
lemma Submartingale.monotone_predictablePart
  proof: by
have := ae_all_iff.2 fun n : Nat => hf.condExp_sub_nonneg n.le_succ
  filter_upwards [this] with ω h
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, ← ge_iff_le] at h
  refine monotone_nat_of_le_succ fun n => (?_ : _ >= _)
  grw [predictablePart_add_one, Pi.add_apply, h n, add_zero]

中文:
引理 Submartingale.monotone_predictablePart
  证明: by
have := ae_all_iff.2 fun n : Nat => hf.condExp_sub_nonneg n.le_succ
  filter_upwards [this] with ω h
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, ← ge_iff_le] at h
  refine monotone_nat_of_le_succ fun n => (?_ : _ >= _)
  grw [predictablePart_add_one, Pi.add_apply, h n, add_zero]

Depends on / 依赖: Nat.succ_eq_add_one, Pi.add_apply, Pi.zero_apply, add_apply, add_zero, ae_all_iff, condExp_sub_nonneg, filter_upwards, ge_iff_le, hf.condExp_sub_nonneg, le_succ, monotone_nat_of_le_succ, n.le_succ, predictablePart_add_one, succ_eq_add_one, zero_apply
-/
lemma Submartingale.monotone_predictablePart
    [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E]
    (hf : Submartingale f ℱ μ) :
    forallᵐ ω ∂μ, Monotone (predictablePart f ℱ μ · ω) := by
have := ae_all_iff.2 fun n : Nat => hf.condExp_sub_nonneg n.le_succ
  filter_upwards [this] with ω h
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, ← ge_iff_le] at h
  refine monotone_nat_of_le_succ fun n => (?_ : _ >= _)
  grw [predictablePart_add_one, Pi.add_apply, h n, add_zero]

/--
lemma `Submartingale.predictablePart_nonneg` / 引理 `Submartingale.predictablePart_nonneg`

English:
lemma Submartingale.predictablePart_nonneg
  proof: by
  filter_upwards [hf.monotone_predictablePart] with ω hω n
  simpa [predictablePart_zero] using hω (Nat.zero_le n)

中文:
引理 Submartingale.predictablePart_nonneg
  证明: by
  filter_upwards [hf.monotone_predictablePart] with ω hω n
  simpa [predictablePart_zero] using hω (Nat.zero_le n)

Depends on / 依赖: Nat.zero_le, filter_upwards, hf.monotone_predictablePart, monotone_predictablePart, predictablePart_zero, zero_le
-/
lemma Submartingale.predictablePart_nonneg
    [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E]
    (hf : Submartingale f ℱ μ) :
    forallᵐ ω ∂μ, forall n, 0 <= predictablePart f ℱ μ n ω := by
  filter_upwards [hf.monotone_predictablePart] with ω hω n
  simpa [predictablePart_zero] using hω (Nat.zero_le n)

/--
lemma `IsStronglyPredictable.predictablePart_eq` / 引理 `IsStronglyPredictable.predictablePart_eq`

English:
lemma IsStronglyPredictable.predictablePart_eq
  proof: by
  simp only [predictablePart, ← Finset.sum_range_sub]
  exact eventuallyEq_sum fun i hi => (condExp_of_stronglyMeasurable (ℱ.le i)
    ((hf.measurable_add_one i).sub (hf.stronglyAdapted i))
    ((hfint (i + 1)).sub (hfint i))).eventuallyEq

中文:
引理 IsStronglyPredictable.predictablePart_eq
  证明: by
  simp only [predictablePart, ← Finset.sum_range_sub]
  exact eventuallyEq_sum fun i hi => (condExp_of_stronglyMeasurable (ℱ.le i)
    ((hf.measurable_add_one i).sub (hf.stronglyAdapted i))
    ((hfint (i + 1)).sub (hfint i))).eventuallyEq

Depends on / 依赖: Finset, Finset.sum_range_sub, condExp_of_stronglyMeasurable, eventuallyEq, eventuallyEq_sum, hf.measurable_add_one, hf.stronglyAdapted, measurable_add_one, predictablePart, stronglyAdapted, sum_range_sub
-/
lemma IsStronglyPredictable.predictablePart_eq
    [SigmaFiniteFiltration μ ℱ] (hf : IsStronglyPredictable ℱ f)
    (hfint : forall n, Integrable (f n) μ) (n : Nat) :
    predictablePart f ℱ μ n =ᵐ[μ] f n - f 0 := by
  simp only [predictablePart, ← Finset.sum_range_sub]
  exact eventuallyEq_sum fun i hi => (condExp_of_stronglyMeasurable (ℱ.le i)
    ((hf.measurable_add_one i).sub (hf.stronglyAdapted i))
    ((hfint (i + 1)).sub (hfint i))).eventuallyEq

/--
theorem `stronglyAdapted_predictablePart` / 定理 `stronglyAdapted_predictablePart`

English:
theorem stronglyAdapted_predictablePart
  proof: fun _ => Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_succ_iff.mp hin))

中文:
定理 stronglyAdapted_predictablePart
  证明: fun _ => Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_succ_iff.mp hin))

Depends on / 依赖: Finset, Finset.mem_range_succ_iff.mp, Finset.stronglyMeasurable_sum, mem_range_succ_iff, stronglyMeasurable_condExp, stronglyMeasurable_condExp.mono, stronglyMeasurable_sum
-/
theorem stronglyAdapted_predictablePart :
    StronglyAdapted ℱ fun n => predictablePart f ℱ μ (n + 1) :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_succ_iff.mp hin))

/--
lemma `isPredictable_predictablePart` / 引理 `isPredictable_predictablePart`

English:
lemma isPredictable_predictablePart
  given: [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  proof: IsStronglyPredictable.of_measurable_add_one (by measurability)
    fun n => (stronglyAdapted_predictablePart n)

中文:
引理 isPredictable_predictablePart
  条件: [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  证明: IsStronglyPredictable.of_measurable_add_one (by measurability)
    fun n => (stronglyAdapted_predictablePart n)

Depends on / 依赖: IsStronglyPredictable, IsStronglyPredictable.of_measurable_add_one, measurability, of_measurable_add_one, stronglyAdapted_predictablePart
-/
lemma isPredictable_predictablePart [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] :
    IsStronglyPredictable ℱ (predictablePart f ℱ μ) :=
  IsStronglyPredictable.of_measurable_add_one (by measurability)
    fun n => (stronglyAdapted_predictablePart n)

/--
theorem `stronglyAdapted_predictablePart'` / 定理 `stronglyAdapted_predictablePart'`

English:
theorem stronglyAdapted_predictablePart'
  statement: StronglyAdapted ℱ fun n => predictablePart f ℱ μ n
  proof: fun _ => Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_le hin))

中文:
定理 stronglyAdapted_predictablePart'
  结论: StronglyAdapted ℱ fun n => predictablePart f ℱ μ n
  证明: fun _ => Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_le hin))

Depends on / 依赖: Finset, Finset.mem_range_le, Finset.stronglyMeasurable_sum, mem_range_le, stronglyMeasurable_condExp, stronglyMeasurable_condExp.mono, stronglyMeasurable_sum
-/
theorem stronglyAdapted_predictablePart' : StronglyAdapted ℱ fun n => predictablePart f ℱ μ n :=
  fun _ => Finset.stronglyMeasurable_sum _ fun _ hin =>
    stronglyMeasurable_condExp.mono (ℱ.mono (Finset.mem_range_le hin))

/--
Definition of `martingalePart` / `martingalePart` 的定义

English:
definition martingalePart
  signature: {m0 : MeasurableSpace Ω} (f : Nat -> Ω -> E) (ℱ : Filtration Nat m0)
  body: fun n => f n - predictablePart f ℱ μ n

@[simp]

中文:
定义 martingalePart
  签名: {m0 : MeasurableSpace Ω} (f : 自然数 -> Ω -> E) (ℱ : Filtration 自然数 m0)
  定义体: fun n => f n - predictablePart f ℱ μ n

@[simp]

Depends on / 依赖: predictablePart
-/
noncomputable def martingalePart {m0 : MeasurableSpace Ω} (f : Nat -> Ω -> E) (ℱ : Filtration Nat m0)
    (μ : Measure Ω) : Nat -> Ω -> E := fun n => f n - predictablePart f ℱ μ n

@[simp]
/--
lemma `martingalePart_zero` / 引理 `martingalePart_zero`

English:
lemma martingalePart_zero
  statement: martingalePart f ℱ μ 0 = f 0
  proof: by
  simp [martingalePart]

中文:
引理 martingalePart_zero
  结论: martingalePart f ℱ μ 0 = f 0
  证明: by
  simp [martingalePart]

Depends on / 依赖: martingalePart
-/
lemma martingalePart_zero : martingalePart f ℱ μ 0 = f 0 := by
  simp [martingalePart]

/--
lemma `martingalePart_smul` / 引理 `martingalePart_smul`

English:
lemma martingalePart_smul
  given: [CompleteSpace E] (c : Real) (n : Nat)
  proof: by
  filter_upwards [predictablePart_smul (f := f) c n] with ω hω
  simpa [martingalePart, smul_sub]

中文:
引理 martingalePart_smul
  条件: [CompleteSpace E] (c : 实数) (n : 自然数)
  证明: by
  filter_upwards [predictablePart_smul (f := f) c n] with ω hω
  simpa [martingalePart, smul_sub]

Depends on / 依赖: filter_upwards, martingalePart, predictablePart_smul, smul_sub
-/
lemma martingalePart_smul [CompleteSpace E] (c : Real) (n : Nat) :
    martingalePart (c • f) ℱ μ n =ᵐ[μ] c • martingalePart f ℱ μ n := by
  filter_upwards [predictablePart_smul (f := f) c n] with ω hω
  simpa [martingalePart, smul_sub]

/--
lemma `martingalePart_add` / 引理 `martingalePart_add`

English:
lemma martingalePart_add
  statement: [CompleteSpace E] (hfint : forall n, Integrable (f n) μ)
  proof: by
  filter_upwards [predictablePart_add (ℱ := ℱ) hfint hgint n] with ω hω
  simp_all [martingalePart]
  abel

中文:
引理 martingalePart_add
  结论: [CompleteSpace E] (hfint : 对任意 n, 整数egrable (f n) μ)
  证明: by
  filter_upwards [predictablePart_add (ℱ := ℱ) hfint hgint n] with ω hω
  simp_all [martingalePart]
  abel

Depends on / 依赖: filter_upwards, martingalePart, predictablePart_add
-/
lemma martingalePart_add [CompleteSpace E] (hfint : forall n, Integrable (f n) μ)
    (hgint : forall n, Integrable (g n) μ) (n : Nat) :
    martingalePart (f + g) ℱ μ n =ᵐ[μ] martingalePart f ℱ μ n + martingalePart g ℱ μ n := by
  filter_upwards [predictablePart_add (ℱ := ℱ) hfint hgint n] with ω hω
  simp_all [martingalePart]
  abel

/--
lemma `Martingale.martingalePart_eq` / 引理 `Martingale.martingalePart_eq`

English:
lemma Martingale.martingalePart_eq
  given: [CompleteSpace E] (hf : Martingale f ℱ μ) (n : Nat)
  proof: by
  filter_upwards [hf.predictablePart_eq_zero n] with ω hω
  simp [martingalePart, hω]

中文:
引理 Martingale.martingalePart_eq
  条件: [CompleteSpace E] (hf : Martingale f ℱ μ) (n : 自然数)
  证明: by
  filter_upwards [hf.predictablePart_eq_zero n] with ω hω
  simp [martingalePart, hω]

Depends on / 依赖: filter_upwards, hf.predictablePart_eq_zero, martingalePart, predictablePart_eq_zero
-/
lemma Martingale.martingalePart_eq [CompleteSpace E] (hf : Martingale f ℱ μ) (n : Nat) :
    martingalePart f ℱ μ n =ᵐ[μ] f n := by
  filter_upwards [hf.predictablePart_eq_zero n] with ω hω
  simp [martingalePart, hω]

/--
lemma `IsPredictable.martingalePart_eq` / 引理 `IsPredictable.martingalePart_eq`

English:
lemma IsPredictable.martingalePart_eq
  statement: [SigmaFiniteFiltration μ ℱ] (hf : IsStronglyPredictable ℱ f)
  proof: by
  filter_upwards [hf.predictablePart_eq (μ := μ) hfint n] with ω hω
  simp [martingalePart, hω, sub_eq_add_neg]

中文:
引理 IsPredictable.martingalePart_eq
  结论: [SigmaFiniteFiltration μ ℱ] (hf : IsStronglyPredictable ℱ f)
  证明: by
  filter_upwards [hf.predictablePart_eq (μ := μ) hfint n] with ω hω
  simp [martingalePart, hω, sub_eq_add_neg]

Depends on / 依赖: filter_upwards, hf.predictablePart_eq, martingalePart, predictablePart_eq, sub_eq_add_neg
-/
lemma IsPredictable.martingalePart_eq [SigmaFiniteFiltration μ ℱ] (hf : IsStronglyPredictable ℱ f)
    (hfint : forall n, Integrable (f n) μ) (n : Nat) :
    martingalePart f ℱ μ n =ᵐ[μ] f 0 := by
  filter_upwards [hf.predictablePart_eq (μ := μ) hfint n] with ω hω
  simp [martingalePart, hω, sub_eq_add_neg]

/--
theorem `martingalePart_add_predictablePart` / 定理 `martingalePart_add_predictablePart`

English:
theorem martingalePart_add_predictablePart
  given: (ℱ : Filtration Nat m0) (μ : Measure Ω) (f : Nat -> Ω -> E)
  proof: sub_add_cancel _ _

中文:
定理 martingalePart_add_predictablePart
  条件: (ℱ : Filtration 自然数 m0) (μ : Measure Ω) (f : 自然数 -> Ω -> E)
  证明: sub_add_cancel _ _

Depends on / 依赖: sub_add_cancel
-/
theorem martingalePart_add_predictablePart (ℱ : Filtration Nat m0) (μ : Measure Ω) (f : Nat -> Ω -> E) :
    martingalePart f ℱ μ + predictablePart f ℱ μ = f :=
  sub_add_cancel _ _

/--
theorem `martingalePart_eq_sum` / 定理 `martingalePart_eq_sum`

English:
theorem martingalePart_eq_sum
  statement: martingalePart f ℱ μ = fun n =>
  proof: by
  unfold martingalePart predictablePart
  ext1 n
  rw [Finset.eq_sum_range_sub f n]; rw [← add_sub]; rw [← Finset.sum_sub_distrib]

中文:
定理 martingalePart_eq_sum
  结论: martingalePart f ℱ μ = fun n =>
  证明: by
  unfold martingalePart predictablePart
  ext1 n
  rw [Finset.eq_sum_range_sub f n]; rw [← add_sub]; rw [← Finset.sum_sub_distrib]

Depends on / 依赖: Finset, Finset.eq_sum_range_sub, Finset.sum_sub_distrib, add_sub, eq_sum_range_sub, martingalePart, predictablePart, sum_sub_distrib
-/
theorem martingalePart_eq_sum : martingalePart f ℱ μ = fun n =>
    f 0 + ∑ i in Finset.range n, (f (i + 1) - f i - μ[f (i + 1) - f i | ℱ i]) := by
  unfold martingalePart predictablePart
  ext1 n
  rw [Finset.eq_sum_range_sub f n]; rw [← add_sub]; rw [← Finset.sum_sub_distrib]

/--
theorem `stronglyAdapted_martingalePart` / 定理 `stronglyAdapted_martingalePart`

English:
theorem stronglyAdapted_martingalePart
  given: (hf : StronglyAdapted ℱ f)
  proof: hf.sub stronglyAdapted_predictablePart'

中文:
定理 stronglyAdapted_martingalePart
  条件: (hf : StronglyAdapted ℱ f)
  证明: hf.sub stronglyAdapted_predictablePart'

Depends on / 依赖: hf.sub, stronglyAdapted_predictablePart
-/
theorem stronglyAdapted_martingalePart (hf : StronglyAdapted ℱ f) :
  StronglyAdapted ℱ (martingalePart f ℱ μ) := hf.sub stronglyAdapted_predictablePart'

/--
theorem `integrable_martingalePart` / 定理 `integrable_martingalePart`

English:
theorem integrable_martingalePart
  given: [CompleteSpace E] (hf_int : forall n, Integrable (f n) μ) (n : Nat)
  proof: by
  rw [martingalePart_eq_sum]
  fun_prop

中文:
定理 integrable_martingalePart
  条件: [CompleteSpace E] (hf_int : 对任意 n, 整数egrable (f n) μ) (n : 自然数)
  证明: by
  rw [martingalePart_eq_sum]
  fun_prop

Depends on / 依赖: fun_prop, martingalePart_eq_sum
-/
theorem integrable_martingalePart [CompleteSpace E] (hf_int : forall n, Integrable (f n) μ) (n : Nat) :
    Integrable (martingalePart f ℱ μ n) μ := by
  rw [martingalePart_eq_sum]
  fun_prop

/--
theorem `martingale_martingalePart` / 定理 `martingale_martingalePart`

English:
theorem martingale_martingalePart
  statement: [CompleteSpace E]
  proof: by
  refine ⟨stronglyAdapted_martingalePart hf, fun i j hij => ?_⟩
  -- ⊢ μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ] martingalePart f ℱ μ i
  have h_eq_sum : μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ]
      f 0 + ∑ k in Finset.range j,
        (μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i]) := 

中文:
定理 martingale_martingalePart
  结论: [CompleteSpace E]
  证明: by
  refine ⟨stronglyAdapted_martingalePart hf, fun i j hij => ?_⟩
  -- ⊢ μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ] martingalePart f ℱ μ i
  have h_eq_sum : μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ]
      f 0 + ∑ k in Finset.range j,
        (μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i]) := 

Depends on / 依赖: IsSemisimpleRing, Subsingleton, stronglyAdapted_martingalePart
-/
theorem martingale_martingalePart [CompleteSpace E]
    (hf : StronglyAdapted ℱ f) (hf_int : forall n, Integrable (f n) μ)
    [SigmaFiniteFiltration μ ℱ] : Martingale (martingalePart f ℱ μ) ℱ μ := by
  refine ⟨stronglyAdapted_martingalePart hf, fun i j hij => ?_⟩
  -- ⊢ μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ] martingalePart f ℱ μ i
  have h_eq_sum : μ[martingalePart f ℱ μ j | ℱ i] =ᵐ[μ]
      f 0 + ∑ k in Finset.range j,
        (μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i]) := by
    rw [martingalePart_eq_sum]
    refine (condExp_add (hf_int 0) (by fun_prop) _).trans ?_
    refine (EventuallyEq.rfl.add (condExp_finsetSum (fun i _ => by fun_prop) _)).trans ?_
    refine EventuallyEq.add ?_ ?_
    · rw [condExp_of_stronglyMeasurable (ℱ.le _) _ (hf_int 0)]
      · exact (hf 0).mono (ℱ.mono zero_le)
    · exact eventuallyEq_sum fun k _ => condExp_sub (by fun_prop) integrable_condExp _
  refine h_eq_sum.trans ?_
  have h_ge : forall k, i <= k ->
      μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ] 0 := by
    intro k hk
    have : μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ] μ[f (k + 1) - f k | ℱ i] :=
      condExp_condExp_of_le (ℱ.mono hk) (ℱ.le k)
    filter_upwards [this] with x hx
    rw [Pi.sub_apply]; rw [Pi.zero_apply]; rw [hx]; rw [sub_self]
  have h_lt : forall k, k < i -> μ[f (k + 1) - f k | ℱ i] - μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ]
      f (k + 1) - f k - μ[f (k + 1) - f k | ℱ k] := by
    refine fun k hk => EventuallyEq.sub ?_ ?_
    · rw [condExp_of_stronglyMeasurable]
      · exact ((hf (k + 1)).mono (ℱ.mono (Nat.succ_le_of_lt hk))).sub ((hf k).mono (ℱ.mono hk.le))
      · exact (hf_int _).sub (hf_int _)
    · rw [condExp_of_stronglyMeasurable]
      · exact stronglyMeasurable_condExp.mono (ℱ.mono hk.le)
      · exact integrable_condExp
  rw [martingalePart_eq_sum]
  refine EventuallyEq.add EventuallyEq.rfl ?_
  rw [← Finset.sum_range_add_sum_Ico _ hij]; rw [←
    add_zero (∑ i in Finset.range i]; rw [(f (i + 1) - f i - μ[f (i + 1) - f i | ℱ i]))]
  refine (eventuallyEq_sum fun k hk => h_lt k (Finset.mem_range.mp hk)).add ?_
  refine (eventuallyEq_sum fun k hk => h_ge k (Finset.mem_Ico.mp hk).1).trans ?_
  simp only [Finset.sum_const_zero]
  rfl

-- The following two lemmas demonstrate the essential uniqueness of the decomposition
/--
theorem `martingalePart_add_ae_eq` / 定理 `martingalePart_add_ae_eq`

English:
theorem martingalePart_add_ae_eq
  statement: [CompleteSpace E] [SigmaFiniteFiltration μ ℱ] {f g : Nat -> Ω -> E}
  proof: by
  set h := f - martingalePart (f + g) ℱ μ with hhdef
  have hh : h = predictablePart (f + g) ℱ μ - g := by
    rw [hhdef]; rw [sub_eq_sub_iff_add_eq_add]; rw [add_comm (predictablePart (f + g) ℱ μ)]; rw [martingalePart_add_predictablePart]
  have hhpred : StronglyAdapted ℱ fun n => h (n + 1) := b

中文:
定理 martingalePart_add_ae_eq
  结论: [CompleteSpace E] [SigmaFiniteFiltration μ ℱ] {f g : 自然数 -> Ω -> E}
  证明: by
  set h := f - martingalePart (f + g) ℱ μ with hhdef
  have hh : h = predictablePart (f + g) ℱ μ - g := by
    rw [hhdef]; rw [sub_eq_sub_iff_add_eq_add]; rw [add_comm (predictablePart (f + g) ℱ μ)]; rw [martingalePart_add_predictablePart]
  have hhpred : StronglyAdapted ℱ fun n => h (n + 1) := b

Depends on / 依赖: IsStronglyPredictable, IsStronglyPredictable.of_measurable_add_one, Martingale, StronglyAdapted, add_comm, hf.sub, hg0.symm, hhmgle, hhpred, martingalePart, martingalePart_add_predictablePart, martingale_martinga, of_measurable_add_one, predictablePart, stronglyAdapted_predictablePart, stronglyAdapted_predictablePart.sub, stronglyMeasurable_zero, sub_eq_sub_iff_add_eq_add
-/
theorem martingalePart_add_ae_eq [CompleteSpace E] [SigmaFiniteFiltration μ ℱ] {f g : Nat -> Ω -> E}
    (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ fun n => g (n + 1)) (hg0 : g 0 = 0)
    (hgint : forall n, Integrable (g n) μ) (n : Nat) : martingalePart (f + g) ℱ μ n =ᵐ[μ] f n := by
  set h := f - martingalePart (f + g) ℱ μ with hhdef
  have hh : h = predictablePart (f + g) ℱ μ - g := by
    rw [hhdef]; rw [sub_eq_sub_iff_add_eq_add]; rw [add_comm (predictablePart (f + g) ℱ μ)]; rw [martingalePart_add_predictablePart]
  have hhpred : StronglyAdapted ℱ fun n => h (n + 1) := by
    rw [hh]
    exact stronglyAdapted_predictablePart.sub hg
  have := (IsStronglyPredictable.of_measurable_add_one (hg0.symm ▸ stronglyMeasurable_zero) hg)
  have hhmgle : Martingale h ℱ μ := hf.sub (martingale_martingalePart
(hf.stronglyAdapted.add this.stronglyAdapted) fun n => (hf.integrable n).add hgint n)
  refine (eventuallyEq_iff_sub.2 ?_).symm
  filter_upwards [hhmgle.eq_zero_of_predictable hhpred n] with ω hω
  unfold h at hω
  rw [Pi.sub_apply] at hω
  rw [hω]; rw [Pi.sub_apply]; rw [martingalePart]
  simp [hg0]

/--
theorem `predictablePart_add_ae_eq` / 定理 `predictablePart_add_ae_eq`

English:
theorem predictablePart_add_ae_eq
  statement: [CompleteSpace E] [SigmaFiniteFiltration μ ℱ] {f g : Nat -> Ω -> E}
  proof: by
  filter_upwards [martingalePart_add_ae_eq hf hg hg0 hgint n] with ω hω
  rw [← add_right_inj (f n ω)]
  conv_rhs => rw [← Pi.add_apply, ← Pi.add_apply, ← martingalePart_add_predictablePart ℱ μ (f + g)]
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [hω]

中文:
定理 predictablePart_add_ae_eq
  结论: [CompleteSpace E] [SigmaFiniteFiltration μ ℱ] {f g : 自然数 -> Ω -> E}
  证明: by
  filter_upwards [martingalePart_add_ae_eq hf hg hg0 hgint n] with ω hω
  rw [← add_right_inj (f n ω)]
  conv_rhs => rw [← Pi.add_apply, ← Pi.add_apply, ← martingalePart_add_predictablePart ℱ μ (f + g)]
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [hω]

Depends on / 依赖: Pi.add_apply, add_apply, add_right_inj, conv_rhs, filter_upwards, martingalePart_add_ae_eq, martingalePart_add_predictablePart
-/
theorem predictablePart_add_ae_eq [CompleteSpace E] [SigmaFiniteFiltration μ ℱ] {f g : Nat -> Ω -> E}
    (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ fun n => g (n + 1)) (hg0 : g 0 = 0)
    (hgint : forall n, Integrable (g n) μ) (n : Nat) : predictablePart (f + g) ℱ μ n =ᵐ[μ] g n := by
  filter_upwards [martingalePart_add_ae_eq hf hg hg0 hgint n] with ω hω
  rw [← add_right_inj (f n ω)]
  conv_rhs => rw [← Pi.add_apply, ← Pi.add_apply, ← martingalePart_add_predictablePart ℱ μ (f + g)]
  rw [Pi.add_apply]; rw [Pi.add_apply]; rw [hω]

section Difference

/--
theorem `predictablePart_bdd_difference` / 定理 `predictablePart_bdd_difference`

English:
theorem predictablePart_bdd_difference
  statement: [CompleteSpace E] {R : Real} {f : Nat -> Ω -> E}
  proof: by
  simp_rw [predictablePart, Finset.sum_apply, Finset.sum_range_succ_sub_sum]
exact ae_all_iff.2 fun i => ae_bdd_norm_condExp_of_ae_bdd_norm ae_all_iff.1 hbdd i

中文:
定理 predictablePart_bdd_difference
  结论: [CompleteSpace E] {R : 实数} {f : 自然数 -> Ω -> E}
  证明: by
  simp_rw [predictablePart, Finset.sum_apply, Finset.sum_range_succ_sub_sum]
exact ae_all_iff.2 fun i => ae_bdd_norm_condExp_of_ae_bdd_norm ae_all_iff.1 hbdd i

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_range_succ_sub_sum, ae_all_iff, ae_bdd_norm_condExp_of_ae_bdd_norm, predictablePart, simp_rw, sum_apply, sum_range_succ_sub_sum
-/
theorem predictablePart_bdd_difference [CompleteSpace E] {R : Real} {f : Nat -> Ω -> E}
    (ℱ : Filtration Nat m0) (hbdd : forallᵐ ω ∂μ, forall i, ‖f (i + 1) ω - f i ω‖ <= R) :
    forallᵐ ω ∂μ, forall i, ‖predictablePart f ℱ μ (i + 1) ω - predictablePart f ℱ μ i ω‖ <= R := by
  simp_rw [predictablePart, Finset.sum_apply, Finset.sum_range_succ_sub_sum]
exact ae_all_iff.2 fun i => ae_bdd_norm_condExp_of_ae_bdd_norm ae_all_iff.1 hbdd i

/--
theorem `martingalePart_bdd_difference` / 定理 `martingalePart_bdd_difference`

English:
theorem martingalePart_bdd_difference
  statement: [CompleteSpace E] {R : Real} {f : Nat -> Ω -> E}
  proof: by
  filter_upwards [hbdd, predictablePart_bdd_difference ℱ hbdd] with ω hω₁ hω₂ i
  simpa [two_mul, martingalePart, sub_sub_sub_comm] using
    (norm_sub_le _ _).trans (add_le_add (hω₁ i) (hω₂ i))

中文:
定理 martingalePart_bdd_difference
  结论: [CompleteSpace E] {R : 实数} {f : 自然数 -> Ω -> E}
  证明: by
  filter_upwards [hbdd, predictablePart_bdd_difference ℱ hbdd] with ω hω₁ hω₂ i
  simpa [two_mul, martingalePart, sub_sub_sub_comm] using
    (norm_sub_le _ _).trans (add_le_add (hω₁ i) (hω₂ i))

Depends on / 依赖: add_le_add, filter_upwards, martingalePart, norm_sub_le, predictablePart_bdd_difference, sub_sub_sub_comm, two_mul
-/
theorem martingalePart_bdd_difference [CompleteSpace E] {R : Real} {f : Nat -> Ω -> E}
    (ℱ : Filtration Nat m0) (hbdd : forallᵐ ω ∂μ, forall i, ‖f (i + 1) ω - f i ω‖ <= R) :
    forallᵐ ω ∂μ, forall i, ‖martingalePart f ℱ μ (i + 1) ω - martingalePart f ℱ μ i ω‖ <= 2 * R := by
  filter_upwards [hbdd, predictablePart_bdd_difference ℱ hbdd] with ω hω₁ hω₂ i
  simpa [two_mul, martingalePart, sub_sub_sub_comm] using
    (norm_sub_le _ _).trans (add_le_add (hω₁ i) (hω₂ i))

end Difference

end MeasureTheory
