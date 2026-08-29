/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Disintegration.Basic
public import Mathlib.Probability.Kernel.Disintegration.CondCDF
public import Mathlib.Probability.Kernel.Disintegration.Density
public import Mathlib.Probability.Kernel.Disintegration.CDFToKernel
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Existence of disintegration of measures and kernels for standard Borel spaces

Let `κ : Kernel α (β × Ω)` be a finite kernel, where `Ω` is a standard Borel space. Then if `α` is
countable or `β` has a countably generated σ-algebra (for example if it is standard Borel), then
there exists a `Kernel (α × β) Ω` called conditional kernel and denoted by `condKernel κ` such that
`κ = fst κ ⊗ₖ condKernel κ`.
We also define a conditional kernel for a measure `ρ : Measure (β × Ω)`, where `Ω` is a standard
Borel space. This is a `Kernel β Ω` denoted by `ρ.condKernel` such that `ρ = ρ.fst ⊗ₘ ρ.condKernel`.

In order to obtain a disintegration for any standard Borel space `Ω`, we use that these spaces embed
measurably into `ℝ`: it then suffices to define a suitable kernel for `Ω = ℝ`.

For `κ : Kernel α (β × ℝ)`, the construction of the conditional kernel proceeds as follows:
* Build a measurable function `f : (α × β) → ℚ → ℝ` such that for all measurable sets
  `s` and all `q : ℚ`, `∫ x in s, f (a, x) q ∂(Kernel.fst κ a) = (κ a).real (s ×ˢ Iic (q : ℝ))`.
  We restrict to `ℚ` here to be able to prove the measurability.
* Extend that function to `(α × β) → StieltjesFunction ℝ`. See the file `MeasurableStieltjes.lean`.
* Finally obtain from the measurable Stieltjes function a measure on `ℝ` for each element of `α × β`
  in a measurable way: we have obtained a `Kernel (α × β) ℝ`.
  See the file `CDFToKernel.lean` for that step.

The first step (building the measurable function on `ℚ`) is done differently depending on whether
`α` is countable or not.
* If `α` is countable, we can provide for each `a : α` a function `f : β → ℚ → ℝ` and proceed as
  above to obtain a `Kernel β ℝ`. Since `α` is countable, measurability is not an issue and we can
  put those together into a `Kernel (α × β) ℝ`. The construction of that `f` is done in
  the `CondCDF.lean` file.
* If `α` is not countable, we can't proceed separately for each `a : α` and have to build a function
  `f : α × β → ℚ → ℝ` which is measurable on the product. We are able to do so if `β` has a
  countably generated σ-algebra (this is the case in particular for standard Borel spaces).
  See the file `Density.lean`.

The conditional kernel is defined under the typeclass assumption
`CountableOrCountablyGenerated α β`, which encodes the property
`Countable α ∨ CountablyGenerated β`.

Properties of integrals involving `condKernel` are collated in the file `Integral.lean`.
The conditional kernel is unique (almost everywhere w.r.t. `fst κ`): this is proved in the file
`Unique.lean`.

## Main definitions

* `ProbabilityTheory.Kernel.condKernel κ : Kernel (α × β) Ω`: conditional kernel described above.
* `MeasureTheory.Measure.condKernel ρ : Kernel β Ω`: conditional kernel of a measure.

## Main statements

* `ProbabilityTheory.Kernel.compProd_fst_condKernel`: `fst κ ⊗ₖ condKernel κ = κ`
* `MeasureTheory.Measure.compProd_fst_condKernel`: `ρ.fst ⊗ₘ ρ.condKernel = ρ`
-/

@[expose] public section

open MeasureTheory Set Filter MeasurableSpace

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α β γ Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} [MeasurableSpace.CountablyGenerated γ]
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]

section Real


/--
lemma `isRatCondKernelCDFAux_density_Iic` / 引理 `isRatCondKernelCDFAux_density_Iic`

English:
lemma isRatCondKernelCDFAux_density_Iic
  given: (κ : Kernel α (γ × Real)) [IsFiniteKernel κ]
  proof: measurable_pi_iff.mpr fun _ => measurable_density κ (fst κ) measurableSet_Iic
  mono' a q r hqr :=
    ae_of_all _ fun c => density_mono_set le_rfl a c (Iic_subset_Iic.mpr (by exact_mod_cast hqr))
  nonneg' _ _ := ae_of_all _ fun _ => density_nonneg le_rfl _ _ _
  le_one' _ _ := ae_of_all _ fun _ =>

中文:
引理 isRatCondKernelCDFAux_density_Iic
  条件: (κ : 核 α (γ × 实数)) [是FiniteKernel κ]
  证明: measurable_pi_iff.mpr fun _ => measurable_density κ (fst κ) measurableSet_Iic
  mono' a q r hqr :=
    ae_of_all _ fun c => density_mono_set le_rfl a c (Iic_subset_Iic.mpr (by exact_mod_cast hqr))
  nonneg' _ _ := ae_of_all _ fun _ => density_nonneg le_rfl _ _ _
  le_one' _ _ := ae_of_all _ fun _ =>

Depends on / 依赖: measurableSet_Iic, measurable_density, measurable_pi_iff, measurable_pi_iff.mpr
-/
lemma isRatCondKernelCDFAux_density_Iic (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] :
    IsRatCondKernelCDFAux (fun (p : α × γ) q => density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) where
  measurable := measurable_pi_iff.mpr fun _ => measurable_density κ (fst κ) measurableSet_Iic
  mono' a q r hqr :=
    ae_of_all _ fun c => density_mono_set le_rfl a c (Iic_subset_Iic.mpr (by exact_mod_cast hqr))
  nonneg' _ _ := ae_of_all _ fun _ => density_nonneg le_rfl _ _ _
  le_one' _ _ := ae_of_all _ fun _ => density_le_one le_rfl _ _ _
  tendsto_integral_of_antitone a s hs_anti hs_tendsto := by
    let s' : Nat -> Set Real := fun n => Iic (s n)
    refine tendsto_integral_density_of_antitone le_rfl a s' ?_ ?_ (fun _ => measurableSet_Iic)
    · refine fun i j hij => Iic_subset_Iic.mpr ?_
      exact mod_cast hs_anti hij
    · ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le, s']
      rw [tendsto_atTop_atBot] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_lt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, lt_of_le_of_lt ?_ hq⟩
      exact mod_cast hi i le_rfl
  tendsto_integral_of_monotone a s hs_mono hs_tendsto := by
    rw [fst_real_apply _ _ MeasurableSet.univ]
    let s' : Nat -> Set Real := fun n => Iic (s n)
    refine tendsto_integral_density_of_monotone (le_rfl : fst κ <= fst κ)
      a s' ?_ ?_ (fun _ => measurableSet_Iic)
    · exact fun i j hij => Iic_subset_Iic.mpr (by exact mod_cast hs_mono hij)
    · ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      rw [tendsto_atTop_atTop] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_gt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, hq.le.trans ?_⟩
      exact mod_cast hi i le_rfl
  integrable a _ := integrable_density le_rfl a measurableSet_Iic
  setIntegral a _ hA _ := setIntegral_density le_rfl a measurableSet_Iic hA

/--
lemma `isRatCondKernelCDF_density_Iic` / 引理 `isRatCondKernelCDF_density_Iic`

English:
lemma isRatCondKernelCDF_density_Iic
  given: (κ : Kernel α (γ × Real)) [IsFiniteKernel κ]
  proof: (isRatCondKernelCDFAux_density_Iic κ).isRatCondKernelCDF

中文:
引理 isRatCondKernelCDF_density_Iic
  条件: (κ : 核 α (γ × 实数)) [是FiniteKernel κ]
  证明: (isRatCondKernelCDFAux_density_Iic κ).isRatCondKernelCDF

Depends on / 依赖: isRatCondKernelCDF, isRatCondKernelCDFAux_density_Iic
-/
lemma isRatCondKernelCDF_density_Iic (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] :
    IsRatCondKernelCDF (fun (p : α × γ) q => density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) :=
  (isRatCondKernelCDFAux_density_Iic κ).isRatCondKernelCDF

/-- The conditional kernel CDF of a kernel `κ : Kernel α (γ × ℝ)`, where `γ` is countably generated.
-/
noncomputable
/--
Definition of `condKernelCDF` / `condKernelCDF` 的定义

English:
definition condKernelCDF
  signature: (κ : Kernel α (γ × Real)) [IsFiniteKernel κ]
  body: stieltjesOfMeasurableRat (fun (p : α × γ) q => density κ (fst κ) p.1 p.2 (Iic q))
    (isRatCondKernelCDF_density_Iic κ).measurable

中文:
定义 condKernelCDF
  签名: (κ : 核 α (γ × 实数)) [是FiniteKernel κ]
  定义体: stieltjesOfMeasurableRat (fun (p : α × γ) q => density κ (fst κ) p.1 p.2 (Iic q))
    (isRatCondKernelCDF_density_Iic κ).measurable

Depends on / 依赖: density, isRatCondKernelCDF_density_Iic, measurable, stieltjesOfMeasurableRat
-/
def condKernelCDF (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] : α × γ -> StieltjesFunction Real :=
  stieltjesOfMeasurableRat (fun (p : α × γ) q => density κ (fst κ) p.1 p.2 (Iic q))
    (isRatCondKernelCDF_density_Iic κ).measurable

/--
lemma `isCondKernelCDF_condKernelCDF` / 引理 `isCondKernelCDF_condKernelCDF`

English:
lemma isCondKernelCDF_condKernelCDF
  given: (κ : Kernel α (γ × Real)) [IsFiniteKernel κ]
  proof: isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_density_Iic κ)

中文:
引理 isCondKernelCDF_condKernelCDF
  条件: (κ : 核 α (γ × 实数)) [是FiniteKernel κ]
  证明: isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_density_Iic κ)

Depends on / 依赖: isCondKernelCDF_stieltjesOfMeasurableRat, isRatCondKernelCDF_density_Iic
-/
lemma isCondKernelCDF_condKernelCDF (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] :
    IsCondKernelCDF (condKernelCDF κ) κ (fst κ) :=
  isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_density_Iic κ)

/-- Auxiliary definition for `ProbabilityTheory.Kernel.condKernel`.
A conditional kernel for `κ : Kernel α (γ × ℝ)` where `γ` is countably generated. -/
noncomputable
/--
Definition of `condKernelReal` / `condKernelReal` 的定义

English:
definition condKernelReal
  signature: (κ : Kernel α (γ × Real)) [IsFiniteKernel κ]
  body: (isCondKernelCDF_condKernelCDF κ).toKernel

中文:
定义 condKernel实数
  签名: (κ : 核 α (γ × 实数)) [是FiniteKernel κ]
  定义体: (isCondKernelCDF_condKernelCDF κ).toKernel

Depends on / 依赖: isCondKernelCDF_condKernelCDF, toKernel
-/
def condKernelReal (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] : Kernel (α × γ) Real :=
  (isCondKernelCDF_condKernelCDF κ).toKernel

/--
Instance `instIsMarkovKernelCondKernelReal` / 实例 `instIsMarkovKernelCondKernelReal`

English:
instance instIsMarkovKernelCondKernelReal
  signature: (κ : Kernel α (γ × Real)) [IsFiniteKernel κ]
  body: by
  rw [condKernelReal]
  infer_instance

中文:
实例 instIsMarkovKernelCondKernel实数
  签名: (κ : 核 α (γ × 实数)) [是FiniteKernel κ]
  定义体: by
  rw [condKernelReal]
  infer_instance

Depends on / 依赖: condKernelReal, infer_instance
-/
instance instIsMarkovKernelCondKernelReal (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelReal κ) := by
  rw [condKernelReal]
  infer_instance

/--
lemma `compProd_fst_condKernelReal` / 引理 `compProd_fst_condKernelReal`

English:
lemma compProd_fst_condKernelReal
  given: (κ : Kernel α (γ × Real)) [IsFiniteKernel κ]
  proof: by
  rw [condKernelReal]; rw [compProd_toKernel]

中文:
引理 compProd_fst_condKernel实数
  条件: (κ : 核 α (γ × 实数)) [是FiniteKernel κ]
  证明: by
  rw [condKernelReal]; rw [compProd_toKernel]

Depends on / 依赖: compProd_toKernel, condKernelReal
-/
lemma compProd_fst_condKernelReal (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] :
    fst κ otimesₖ condKernelReal κ = κ := by
  rw [condKernelReal]; rw [compProd_toKernel]

/-- Auxiliary definition for `MeasureTheory.Measure.condKernel` and
`ProbabilityTheory.Kernel.condKernel`.
A conditional kernel for `κ : Kernel Unit (α × ℝ)`. -/
noncomputable
/--
Definition of `condKernelUnitReal` / `condKernelUnitReal` 的定义

English:
definition condKernelUnitReal
  signature: (κ : Kernel Unit (α × Real)) [IsFiniteKernel κ]
  body: (isCondKernelCDF_condCDF (κ ())).toKernel

中文:
定义 condKernelUnit实数
  签名: (κ : 核 单元 (α × 实数)) [是FiniteKernel κ]
  定义体: (isCondKernelCDF_condCDF (κ ())).toKernel

Depends on / 依赖: isCondKernelCDF_condCDF, toKernel
-/
def condKernelUnitReal (κ : Kernel Unit (α × Real)) [IsFiniteKernel κ] : Kernel (Unit × α) Real :=
  (isCondKernelCDF_condCDF (κ ())).toKernel

/--
Instance `instIsMarkovKernelCondKernelUnitReal` / 实例 `instIsMarkovKernelCondKernelUnitReal`

English:
instance instIsMarkovKernelCondKernelUnitReal
  signature: (κ : Kernel Unit (α × Real)) [IsFiniteKernel κ]
  body: by
  rw [condKernelUnitReal]
  infer_instance

中文:
实例 instIsMarkovKernelCondKernelUnit实数
  签名: (κ : 核 单元 (α × 实数)) [是FiniteKernel κ]
  定义体: by
  rw [condKernelUnitReal]
  infer_instance

Depends on / 依赖: condKernelUnitReal, infer_instance
-/
instance instIsMarkovKernelCondKernelUnitReal (κ : Kernel Unit (α × Real)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelUnitReal κ) := by
  rw [condKernelUnitReal]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `condKernelUnitReal.instIsCondKernel` / 实例 `condKernelUnitReal.instIsCondKernel`

English:
instance condKernelUnitReal.instIsCondKernel
  signature: (κ : Kernel Unit (α × Real)) [IsFiniteKernel κ]
  body: by rw [condKernelUnitReal, compProd_toKernel]; ext; simp

中文:
实例 condKernelUnit实数.instIsCondKernel
  签名: (κ : 核 单元 (α × 实数)) [是FiniteKernel κ]
  定义体: by rw [condKernelUnitReal, compProd_toKernel]; ext; simp

Depends on / 依赖: compProd_toKernel, condKernelUnitReal
-/
instance condKernelUnitReal.instIsCondKernel (κ : Kernel Unit (α × Real)) [IsFiniteKernel κ] :
    κ.IsCondKernel κ.condKernelUnitReal where
  disintegrate := by rw [condKernelUnitReal, compProd_toKernel]; ext; simp

end Real

section BorelSnd

/-! ### Disintegration of kernels on standard Borel spaces

Since every standard Borel space embeds measurably into `ℝ`, we can generalize a disintegration
property on `ℝ` to all these spaces. -/

open scoped Classical in
/-- Auxiliary definition for `ProbabilityTheory.Kernel.condKernel`.
A Borel space `Ω` embeds measurably into `ℝ` (with embedding `e`), hence we can get a `Kernel α Ω`
from a `Kernel α ℝ` by taking the comap by `e`.
Here we take the comap of a modification of `η : Kernel α ℝ`, useful when `η a` is a probability
measure with all its mass on `range e` almost everywhere with respect to some measure and we want to
ensure that the comap is a Markov kernel.
We thus take the comap by `e` of a kernel defined piecewise: `η` when
`η a (range (embeddingReal Ω))ᶜ = 0`, and an arbitrary deterministic kernel otherwise. -/
noncomputable
/--
Definition of `borelMarkovFromReal` / `borelMarkovFromReal` 的定义

English:
definition borelMarkovFromReal
  signature: (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
  body: have he := measurableEmbedding_embeddingReal Ω
  let x₀ := (range_nonempty (embeddingReal Ω)).choose
  comapRight
    (piecewise ((Kernel.measurable_coe η he.measurableSet_range.compl) (measurableSet_singleton 0) :
        MeasurableSet {a | η a (range (embeddingReal Ω))ᶜ = 0})
      η (deterministi

中文:
定义 borelMarkovFrom实数
  签名: (Ω : 类型) [非空 Ω] [可测空间 Ω] [StandardBorel空间 Ω]
  定义体: have he := measurableEmbedding_embeddingReal Ω
  let x₀ := (range_nonempty (embeddingReal Ω)).choose
  comapRight
    (piecewise ((Kernel.measurable_coe η he.measurableSet_range.compl) (measurableSet_singleton 0) :
        MeasurableSet {a | η a (range (embeddingReal Ω))ᶜ = 0})
      η (deterministi

Depends on / 依赖: Kernel, Kernel.measurable_coe, MeasurableSet, comapRight, deterministic, embeddingReal, he.measurableSet_range.compl, measurableEmbedding_embeddingReal, measurableSet_range, measurableSet_singleton, measurable_coe, measurable_const, piecewise, range_nonempty
-/
def borelMarkovFromReal (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α Real) :
    Kernel α Ω :=
  have he := measurableEmbedding_embeddingReal Ω
  let x₀ := (range_nonempty (embeddingReal Ω)).choose
  comapRight
    (piecewise ((Kernel.measurable_coe η he.measurableSet_range.compl) (measurableSet_singleton 0) :
        MeasurableSet {a | η a (range (embeddingReal Ω))ᶜ = 0})
      η (deterministic (fun _ => x₀) measurable_const)) he

/--
lemma `borelMarkovFromReal_apply` / 引理 `borelMarkovFromReal_apply`

English:
lemma borelMarkovFromReal_apply
  statement: (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
  proof: by
  classical
  rw [borelMarkovFromReal]; rw [comapRight_apply]; rw [piecewise_apply]; rw [deterministic_apply]
  simp only [mem_preimage, mem_singleton_iff]
  split_ifs <;> rfl

中文:
引理 borelMarkovFrom实数_apply
  结论: (Ω : 类型) [非空 Ω] [可测空间 Ω] [StandardBorel空间 Ω]
  证明: by
  classical
  rw [borelMarkovFromReal]; rw [comapRight_apply]; rw [piecewise_apply]; rw [deterministic_apply]
  simp only [mem_preimage, mem_singleton_iff]
  split_ifs <;> rfl

Depends on / 依赖: borelMarkovFromReal, classical, comapRight_apply, deterministic_apply, mem_preimage, mem_singleton_iff, piecewise_apply, split_ifs
-/
lemma borelMarkovFromReal_apply (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α Real) (a : α) :
    borelMarkovFromReal Ω η a
      = if η a (range (embeddingReal Ω))ᶜ = 0 then (η a).comap (embeddingReal Ω)
        else (Measure.dirac (range_nonempty (embeddingReal Ω)).choose).comap (embeddingReal Ω) := by
  classical
  rw [borelMarkovFromReal]; rw [comapRight_apply]; rw [piecewise_apply]; rw [deterministic_apply]
  simp only [mem_preimage, mem_singleton_iff]
  split_ifs <;> rfl

/--
lemma `borelMarkovFromReal_apply'` / 引理 `borelMarkovFromReal_apply'`

English:
lemma borelMarkovFromReal_apply'
  statement: (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
  proof: by
  have he := measurableEmbedding_embeddingReal Ω
  rw [borelMarkovFromReal_apply]
  split_ifs with h
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs]
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs, Measure.dirac_apply]

中文:
引理 borelMarkovFrom实数_apply'
  结论: (Ω : 类型) [非空 Ω] [可测空间 Ω] [StandardBorel空间 Ω]
  证明: by
  have he := measurableEmbedding_embeddingReal Ω
  rw [borelMarkovFromReal_apply]
  split_ifs with h
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs]
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs, Measure.dirac_apply]

Depends on / 依赖: Measure, Measure.comap_apply, Measure.dirac_apply, borelMarkovFromReal_apply, comap_apply, dirac_apply, he.injective, he.measurableSet_image, injective, measurableEmbedding_embeddingReal, measurableSet_image, split_ifs
-/
lemma borelMarkovFromReal_apply' (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α Real) (a : α) {s : Set Ω} (hs : MeasurableSet s) :
    borelMarkovFromReal Ω η a s
      = if η a (range (embeddingReal Ω))ᶜ = 0 then η a (embeddingReal Ω '' s)
        else (embeddingReal Ω '' s).indicator 1 (range_nonempty (embeddingReal Ω)).choose := by
  have he := measurableEmbedding_embeddingReal Ω
  rw [borelMarkovFromReal_apply]
  split_ifs with h
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs]
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs, Measure.dirac_apply]

/--
Instance `instIsSFiniteKernelBorelMarkovFromReal` / 实例 `instIsSFiniteKernelBorelMarkovFromReal`

English:
instance instIsSFiniteKernelBorelMarkovFromReal
  signature: (η : Kernel α Real) [IsSFiniteKernel η]
  body: IsSFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)

中文:
实例 instIsSFiniteKernelBorelMarkovFrom实数
  签名: (η : 核 α 实数) [是SFiniteKernel η]
  定义体: IsSFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)

Depends on / 依赖: IsSFiniteKernel, IsSFiniteKernel.comapRight, comapRight, measurableEmbedding_embeddingReal
-/
instance instIsSFiniteKernelBorelMarkovFromReal (η : Kernel α Real) [IsSFiniteKernel η] :
    IsSFiniteKernel (borelMarkovFromReal Ω η) :=
  IsSFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)

/--
Instance `instIsFiniteKernelBorelMarkovFromReal` / 实例 `instIsFiniteKernelBorelMarkovFromReal`

English:
instance instIsFiniteKernelBorelMarkovFromReal
  signature: (η : Kernel α Real) [IsFiniteKernel η]
  body: IsFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)

中文:
实例 instIsFiniteKernelBorelMarkovFrom实数
  签名: (η : 核 α 实数) [是FiniteKernel η]
  定义体: IsFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)

Depends on / 依赖: IsFiniteKernel, IsFiniteKernel.comapRight, comapRight, measurableEmbedding_embeddingReal
-/
instance instIsFiniteKernelBorelMarkovFromReal (η : Kernel α Real) [IsFiniteKernel η] :
    IsFiniteKernel (borelMarkovFromReal Ω η) :=
  IsFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)

/--
Instance `instIsMarkovKernelBorelMarkovFromReal` / 实例 `instIsMarkovKernelBorelMarkovFromReal`

English:
instance instIsMarkovKernelBorelMarkovFromReal
  signature: (η : Kernel α Real) [IsMarkovKernel η]
  body: by
  refine IsMarkovKernel.comapRight _ (measurableEmbedding_embeddingReal Ω) (fun a => ?_)
  classical
  rw [piecewise_apply]
  split_ifs with h
  · rwa [← prob_compl_eq_zero_iff (measurableEmbedding_embeddingReal Ω).measurableSet_range]
  · rw [deterministic_apply]
    simp [(range_nonempty (embed

中文:
实例 instIsMarkovKernelBorelMarkovFrom实数
  签名: (η : 核 α 实数) [是MarkovKernel η]
  定义体: by
  refine IsMarkovKernel.comapRight _ (measurableEmbedding_embeddingReal Ω) (fun a => ?_)
  classical
  rw [piecewise_apply]
  split_ifs with h
  · rwa [← prob_compl_eq_zero_iff (measurableEmbedding_embeddingReal Ω).measurableSet_range]
  · rw [deterministic_apply]
    simp [(range_nonempty (embed

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.comapRight, choose_spec, classical, comapRight, deterministic_apply, embeddingReal, measurableEmbedding_embeddingReal, measurableSet_range, piecewise_apply, prob_compl_eq_zero_iff, range_nonempty, split_ifs
-/
instance instIsMarkovKernelBorelMarkovFromReal (η : Kernel α Real) [IsMarkovKernel η] :
    IsMarkovKernel (borelMarkovFromReal Ω η) := by
  refine IsMarkovKernel.comapRight _ (measurableEmbedding_embeddingReal Ω) (fun a => ?_)
  classical
  rw [piecewise_apply]
  split_ifs with h
  · rwa [← prob_compl_eq_zero_iff (measurableEmbedding_embeddingReal Ω).measurableSet_range]
  · rw [deterministic_apply]
    simp [(range_nonempty (embeddingReal Ω)).choose_spec]

/--
lemma `compProd_fst_borelMarkovFromReal_eq_comapRight_compProd` / 引理 `compProd_fst_borelMarkovFromReal_eq_comapRight_compProd`

English:
lemma compProd_fst_borelMarkovFromReal_eq_comapRight_compProd
  proof: by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β -> β) e)
  have hη' : fst κ' otimesₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β -> β) e) :=
    MeasurableEmbedding.id.prodMap he
  change fst κ otimesₖ bor

中文:
引理 compProd_fst_borelMarkovFrom实数_eq_comapRight_compProd
  证明: by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β -> β) e)
  have hη' : fst κ' otimesₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β -> β) e) :=
    MeasurableEmbedding.id.prodMap he
  change fst κ otimesₖ bor

Depends on / 依赖: Measur, MeasurableEmbedding, MeasurableEmbedding.id.prodMap, Prod.map, borelMarkovFromReal, comapRight, comapRight_compProd_id_prod, embeddingReal, fst_apply, fun_prop, h_fst, h_prod_embed, map_apply, measurableEmbedding_embeddingReal, prodMap
-/
lemma compProd_fst_borelMarkovFromReal_eq_comapRight_compProd
    (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ] (η : Kernel (α × β) Real) [IsSFiniteKernel η]
    (hη : (fst (map κ (Prod.map (id : β -> β) (embeddingReal Ω)))) otimesₖ η
      = map κ (Prod.map (id : β -> β) (embeddingReal Ω))) :
    fst κ otimesₖ borelMarkovFromReal Ω η
      = comapRight (fst (map κ (Prod.map (id : β -> β) (embeddingReal Ω))) otimesₖ η)
        (MeasurableEmbedding.id.prodMap (measurableEmbedding_embeddingReal Ω)) := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β -> β) e)
  have hη' : fst κ' otimesₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β -> β) e) :=
    MeasurableEmbedding.id.prodMap he
  change fst κ otimesₖ borelMarkovFromReal Ω η = comapRight (fst κ' otimesₖ η) h_prod_embed
  rw [comapRight_compProd_id_prod _ _ he]
  have h_fst : fst κ' = fst κ := by
    ext a u
    unfold κ'
    rw [fst_apply]; rw [map_apply _ (by fun_prop)]; rw [Measure.map_map measurable_fst h_prod_embed.measurable]; rw [fst_apply]
    congr
  rw [h_fst]
  ext a t ht : 2
  simp_rw [compProd_apply ht]
  refine lintegral_congr_ae ?_
  have h_ae : forallᵐ t ∂(fst κ a), (a, t) in {p : α × β | η p (range e)ᶜ = 0} := by
    rw [← h_fst]
    have h_compProd : κ' a (univ ×ˢ range e)ᶜ = 0 := by
      unfold κ'
      rw [map_apply' _ (by fun_prop)]
      swap; · exact (MeasurableSet.univ.prod he.measurableSet_range).compl
      suffices Prod.map id e ⁻¹' (univ ×ˢ range e)ᶜ = ∅ by rw [this]; simp
      ext x
      simp
    rw [← hη']; rw [compProd_null] at h_compProd
    swap; · exact (MeasurableSet.univ.prod he.measurableSet_range).compl
    simp only [preimage_compl, mem_univ, mk_preimage_prod_right] at h_compProd
    exact h_compProd
  filter_upwards [h_ae] with a ha
  rw [borelMarkovFromReal]; rw [comapRight_apply']; rw [comapRight_apply']
  rotate_left
  · exact measurable_prodMk_left ht
  · exact measurable_prodMk_left ht
  classical
  rw [piecewise_apply]; rw [if_pos]
  exact ha

/--
lemma `compProd_fst_borelMarkovFromReal` / 引理 `compProd_fst_borelMarkovFromReal`

English:
lemma compProd_fst_borelMarkovFromReal
  statement: (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ]
  proof: by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β -> β) e)
  have hη' : fst κ' otimesₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β -> β) e) :=
    MeasurableEmbedding.id.prodMap he
  have : κ = comapRight κ'

中文:
引理 compProd_fst_borelMarkovFrom实数
  结论: (κ : 核 α (β × Ω)) [是SFiniteKernel κ]
  证明: by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β -> β) e)
  have hη' : fst κ' otimesₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β -> β) e) :=
    MeasurableEmbedding.id.prodMap he
  have : κ = comapRight κ'

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.id.prodMap, Prod.map, comapRight, comapRight_apply, comap_map, compProd_fst_borelMarkovFromReal_eq_comapRight_compProd, conv_rhs, embeddingReal, fun_prop, h_prod_embed, h_prod_embed.comap_map, map_apply, measurableEmbedding_embeddingReal, prodMap
-/
lemma compProd_fst_borelMarkovFromReal (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ]
    (η : Kernel (α × β) Real) [IsSFiniteKernel η]
    (hη : (fst (map κ (Prod.map (id : β -> β) (embeddingReal Ω)))) otimesₖ η
      = map κ (Prod.map (id : β -> β) (embeddingReal Ω))) :
    fst κ otimesₖ borelMarkovFromReal Ω η = κ := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β -> β) e)
  have hη' : fst κ' otimesₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β -> β) e) :=
    MeasurableEmbedding.id.prodMap he
  have : κ = comapRight κ' h_prod_embed := by
    ext c t : 2
    unfold κ'
    rw [comapRight_apply]; rw [map_apply _ (by fun_prop)]; rw [h_prod_embed.comap_map]
  conv_rhs => rw [this, ← hη']
  exact compProd_fst_borelMarkovFromReal_eq_comapRight_compProd κ η hη

end BorelSnd

section CountablyGenerated

open ProbabilityTheory.Kernel

/-- Auxiliary definition for `ProbabilityTheory.Kernel.condKernel`.
A conditional kernel for `κ : Kernel α (γ × Ω)` where `γ` is countably generated and `Ω` is
standard Borel. -/
noncomputable
/--
Definition of `condKernelBorel` / `condKernelBorel` 的定义

English:
definition condKernelBorel
  signature: (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ]
  body: let κ' := map κ (Prod.map (id : γ -> γ) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelReal κ')

中文:
定义 condKernelBorel
  签名: (κ : 核 α (γ × Ω)) [是FiniteKernel κ]
  定义体: let κ' := map κ (Prod.map (id : γ -> γ) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelReal κ')

Depends on / 依赖: Prod.map, borelMarkovFromReal, condKernelReal, embeddingReal
-/
def condKernelBorel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] : Kernel (α × γ) Ω :=
  let κ' := map κ (Prod.map (id : γ -> γ) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelReal κ')

/--
Instance `instIsMarkovKernelCondKernelBorel` / 实例 `instIsMarkovKernelCondKernelBorel`

English:
instance instIsMarkovKernelCondKernelBorel
  signature: (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ]
  body: by
  rw [condKernelBorel]
  infer_instance

中文:
实例 instIsMarkovKernelCondKernelBorel
  签名: (κ : 核 α (γ × Ω)) [是FiniteKernel κ]
  定义体: by
  rw [condKernelBorel]
  infer_instance

Depends on / 依赖: condKernelBorel, infer_instance
-/
instance instIsMarkovKernelCondKernelBorel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelBorel κ) := by
  rw [condKernelBorel]
  infer_instance

/--
Instance `condKernelBorel.instIsCondKernel` / 实例 `condKernelBorel.instIsCondKernel`

English:
instance condKernelBorel.instIsCondKernel
  signature: (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ]
  body: by
    rw [condKernelBorel]; rw [compProd_fst_borelMarkovFromReal _ _ (compProd_fst_condKernelReal _)]

中文:
实例 condKernelBorel.instIsCondKernel
  签名: (κ : 核 α (γ × Ω)) [是FiniteKernel κ]
  定义体: by
    rw [condKernelBorel]; rw [compProd_fst_borelMarkovFromReal _ _ (compProd_fst_condKernelReal _)]

Depends on / 依赖: compProd_fst_borelMarkovFromReal, compProd_fst_condKernelReal, condKernelBorel
-/
instance condKernelBorel.instIsCondKernel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] :
    κ.IsCondKernel κ.condKernelBorel where
  disintegrate := by
    rw [condKernelBorel]; rw [compProd_fst_borelMarkovFromReal _ _ (compProd_fst_condKernelReal _)]

end CountablyGenerated

section Unit
variable (κ : Kernel Unit (α × Ω)) [IsFiniteKernel κ]

/-- Auxiliary definition for `MeasureTheory.Measure.condKernel` and
`ProbabilityTheory.Kernel.condKernel`.
A conditional kernel for `κ : Kernel Unit (α × Ω)` where `Ω` is standard Borel. -/
noncomputable
/--
Definition of `condKernelUnitBorel` / `condKernelUnitBorel` 的定义

English:
definition condKernelUnitBorel
  signature: : Kernel (Unit × α) Ω
  body: let κ' := map κ (Prod.map (id : α -> α) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelUnitReal κ')

中文:
定义 condKernelUnitBorel
  签名: : 核 (单元 × α) Ω
  定义体: let κ' := map κ (Prod.map (id : α -> α) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelUnitReal κ')

Depends on / 依赖: Prod.map, borelMarkovFromReal, condKernelUnitReal, embeddingReal
-/
def condKernelUnitBorel : Kernel (Unit × α) Ω :=
  let κ' := map κ (Prod.map (id : α -> α) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelUnitReal κ')

/--
Instance `instIsMarkovKernelCondKernelUnitBorel` / 实例 `instIsMarkovKernelCondKernelUnitBorel`

English:
instance instIsMarkovKernelCondKernelUnitBorel
  signature: : IsMarkovKernel κ.condKernelUnitBorel
  body: by
  rw [condKernelUnitBorel]
  infer_instance

中文:
实例 instIsMarkovKernelCondKernelUnitBorel
  签名: : 是MarkovKernel κ.condKernelUnitBorel
  定义体: by
  rw [condKernelUnitBorel]
  infer_instance

Depends on / 依赖: condKernelUnitBorel, infer_instance
-/
instance instIsMarkovKernelCondKernelUnitBorel : IsMarkovKernel κ.condKernelUnitBorel := by
  rw [condKernelUnitBorel]
  infer_instance

/--
Instance `condKernelUnitBorel.instIsCondKernel` / 实例 `condKernelUnitBorel.instIsCondKernel`

English:
instance condKernelUnitBorel.instIsCondKernel
  signature: : κ.IsCondKernel κ.condKernelUnitBorel where
  body: by
    rw [condKernelUnitBorel]; rw [compProd_fst_borelMarkovFromReal _ _ (disintegrate _ _)]

中文:
实例 condKernelUnitBorel.instIsCondKernel
  签名: : κ.是余ndKernel κ.condKernelUnitBorel where
  定义体: by
    rw [condKernelUnitBorel]; rw [compProd_fst_borelMarkovFromReal _ _ (disintegrate _ _)]

Depends on / 依赖: compProd_fst_borelMarkovFromReal, condKernelUnitBorel, disintegrate
-/
instance condKernelUnitBorel.instIsCondKernel : κ.IsCondKernel κ.condKernelUnitBorel where
  disintegrate := by
    rw [condKernelUnitBorel]; rw [compProd_fst_borelMarkovFromReal _ _ (disintegrate _ _)]

end Unit

section Measure

variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/-- Conditional kernel of a measure on a product space: a Markov kernel such that
`ρ = ρ.fst ⊗ₘ ρ.condKernel` (see `MeasureTheory.Measure.compProd_fst_condKernel`). -/
noncomputable
irreducible_def _root_.MeasureTheory.Measure.condKernel (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    Kernel α Ω :=
  comap (condKernelUnitBorel (const Unit ρ)) (fun a => ((), a)) measurable_prodMk_left

/--
lemma `_root_.MeasureTheory.Measure.condKernel_apply` / 引理 `_root_.MeasureTheory.Measure.condKernel_apply`

English:
lemma _root_.MeasureTheory.Measure.condKernel_apply
  statement: (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]
  proof: by
  rw [Measure.condKernel]; rfl

中文:
引理 _root_.测度论.测度.condKernel_apply
  结论: (ρ : 测度 (α × Ω)) [是有限测度 ρ]
  证明: by
  rw [Measure.condKernel]; rfl

Depends on / 依赖: Measure, Measure.condKernel, condKernel
-/
lemma _root_.MeasureTheory.Measure.condKernel_apply (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]
    (a : α) :
    ρ.condKernel a = condKernelUnitBorel (const Unit ρ) ((), a) := by
  rw [Measure.condKernel]; rfl

/--
Instance `_root_.MeasureTheory.Measure.condKernel.instIsCondKernel` / 实例 `_root_.MeasureTheory.Measure.condKernel.instIsCondKernel`

English:
instance _root_.MeasureTheory.Measure.condKernel.instIsCondKernel
  signature: (ρ : Measure (α × Ω))
  body: by
    have h1 : const Unit (Measure.fst ρ) = fst (const Unit ρ) := by
      ext
      simp only [fst_apply, Measure.fst, const_apply]
    have h2 : prodMkLeft Unit (Measure.condKernel ρ) = condKernelUnitBorel (const Unit ρ) := by
      ext
      simp only [prodMkLeft_apply, Measure.condKernel_apply

中文:
实例 _root_.测度论.测度.condKernel.instIsCondKernel
  签名: (ρ : 测度 (α × Ω))
  定义体: by
    have h1 : const Unit (Measure.fst ρ) = fst (const Unit ρ) := by
      ext
      simp only [fst_apply, Measure.fst, const_apply]
    have h2 : prodMkLeft Unit (Measure.condKernel ρ) = condKernelUnitBorel (const Unit ρ) := by
      ext
      simp only [prodMkLeft_apply, Measure.condKernel_apply

Depends on / 依赖: Measure, Measure.compProd, Measure.condKernel, Measure.condKernel_apply, Measure.fst, compProd, condKernel, condKernelUnitBorel, condKernel_apply, const_apply, disintegrate, fst_apply, prodMkLeft, prodMkLeft_apply
-/
instance _root_.MeasureTheory.Measure.condKernel.instIsCondKernel (ρ : Measure (α × Ω))
    [IsFiniteMeasure ρ] : ρ.IsCondKernel ρ.condKernel where
  disintegrate := by
    have h1 : const Unit (Measure.fst ρ) = fst (const Unit ρ) := by
      ext
      simp only [fst_apply, Measure.fst, const_apply]
    have h2 : prodMkLeft Unit (Measure.condKernel ρ) = condKernelUnitBorel (const Unit ρ) := by
      ext
      simp only [prodMkLeft_apply, Measure.condKernel_apply]
    rw [Measure.compProd]; rw [h1]; rw [h2]; rw [disintegrate]
    simp

/--
Instance `_root_.MeasureTheory.Measure.instIsMarkovKernelCondKernel` / 实例 `_root_.MeasureTheory.Measure.instIsMarkovKernelCondKernel`

English:
instance _root_.MeasureTheory.Measure.instIsMarkovKernelCondKernel
  body: by
  rw [Measure.condKernel]
  infer_instance

中文:
实例 _root_.测度论.测度.instIsMarkovKernelCondKernel
  定义体: by
  rw [Measure.condKernel]
  infer_instance

Depends on / 依赖: Measure, Measure.condKernel, condKernel, infer_instance
-/
instance _root_.MeasureTheory.Measure.instIsMarkovKernelCondKernel
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] : IsMarkovKernel ρ.condKernel := by
  rw [Measure.condKernel]
  infer_instance

/--
lemma `_root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero` / 引理 `_root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero`

English:
lemma _root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero
  statement: [MeasurableSingletonClass α]
  proof: Measure.IsCondKernel.apply_of_ne_zero _ _ hx _

中文:
引理 _root_.测度论.测度.condKernel_apply_of_ne_zero
  结论: [MeasurableSingleton类 α]
  证明: Measure.IsCondKernel.apply_of_ne_zero _ _ hx _

Depends on / 依赖: IsCondKernel, Measure, Measure.IsCondKernel.apply_of_ne_zero, apply_of_ne_zero
-/
lemma _root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero [MeasurableSingletonClass α]
    {x : α} (hx : ρ.fst {x} != 0) (s : Set Ω) :
    ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) :=
  Measure.IsCondKernel.apply_of_ne_zero _ _ hx _

end Measure

section CountableOrCountablyGenerated
variable [h : CountableOrCountablyGenerated α β] (κ : Kernel α (β × Ω)) [IsFiniteKernel κ]

open scoped Classical in
/-- Conditional kernel of a kernel `κ : Kernel α (β × Ω)`: a Markov kernel such that
`fst κ ⊗ₖ condKernel κ = κ` (see `MeasureTheory.Measure.compProd_fst_condKernel`).
It exists whenever `Ω` is standard Borel and either `α` is countable
or `β` is countably generated. -/
noncomputable
irreducible_def condKernel : Kernel (α × β) Ω :=
  if hα : Countable α then
    condKernelCountable (fun a => (κ a).condKernel)
      fun x y h => by simp [apply_congr_of_mem_measurableAtom _ h]
  else letI := h.countableOrCountablyGenerated.resolve_left hα; condKernelBorel κ

/--
Instance `instIsMarkovKernelCondKernel` / 实例 `instIsMarkovKernelCondKernel`

English:
instance instIsMarkovKernelCondKernel
  signature: : IsMarkovKernel (condKernel κ)
  body: by
  rw [condKernel_def]
  split_ifs <;> infer_instance

中文:
实例 instIsMarkovKernelCondKernel
  签名: : 是MarkovKernel (condKernel κ)
  定义体: by
  rw [condKernel_def]
  split_ifs <;> infer_instance

Depends on / 依赖: condKernel_def, infer_instance, split_ifs
-/
instance instIsMarkovKernelCondKernel : IsMarkovKernel (condKernel κ) := by
  rw [condKernel_def]
  split_ifs <;> infer_instance

/--
Instance `condKernel.instIsCondKernel` / 实例 `condKernel.instIsCondKernel`

English:
instance condKernel.instIsCondKernel
  signature: : κ.IsCondKernel κ.condKernel where
  body: by rw [condKernel_def]; split_ifs with hα <;> exact disintegrate _ _

中文:
实例 condKernel.instIsCondKernel
  签名: : κ.是余ndKernel κ.condKernel where
  定义体: by rw [condKernel_def]; split_ifs with hα <;> exact disintegrate _ _

Depends on / 依赖: condKernel_def, disintegrate, split_ifs
-/
instance condKernel.instIsCondKernel : κ.IsCondKernel κ.condKernel where
  disintegrate := by rw [condKernel_def]; split_ifs with hα <;> exact disintegrate _ _

end CountableOrCountablyGenerated

end ProbabilityTheory.Kernel
