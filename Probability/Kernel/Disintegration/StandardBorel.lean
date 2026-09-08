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

/-! ### Disintegration of kernels from `α` to `γ × ℝ` for countably generated `γ` -/

/-
**ProbabilityTheory.Kernel.isRatCondKernelCDFAux_density_Iic** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isRatCondKernelCDFAux_density_Iic (κ : Kernel α (γ × Real)) [IsFiniteKerne
l κ] : IsRatCondKernelCDFAux (fun (p : α × γ) q => density κ (fst κ) p.1 p.2 (Ii
c q)) κ (fst κ) where measurable
参数：κ : Kernel α (γ × Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用引理 `ProbabilityTheory.Kernel.measurable_density`：measurable_density (κ : Ker
nel α (γ × β)) (ν : Kernel α γ) {s : Set β} (hs : MeasurableSet s) : Measurable 
(fun (p : α × γ) => density κ ν p…
· 使用定理 `measurableSet_Iic`：measurableSet_Iic [ClosedIicTopology α] : MeasurableS
et (Iic a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.density_mono_set`：density_mono_set (hκν : fst κ
 <= ν) (a : α) (x : γ) {s s' : Set β} (h : s subseteq s') : density κ ν a x s <=
 density κ ν a x s'
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.density_nonneg`：density_nonneg (hκν : fst κ <= 
ν) (a : α) (x : γ) (s : Set β) : 0 <= density κ ν a x s
· 使用引理 `ProbabilityTheory.Kernel.density_le_one`：density_le_one (hκν : fst κ <= 
ν) (a : α) (x : γ) (s : Set β) : density κ ν a x s <= 1
· 使用引理 `ProbabilityTheory.Kernel.tendsto_integral_density_of_antitone`：tendsto_i
ntegral_density_of_antitone (hκν : fst κ <= ν) [IsFiniteKernel ν] (a : α) (seq :
 Nat -> Set β) (hseq : Antitone seq) (hseq_iInter :…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.fst`：∀ {α : Type u_1} {β : Type 
u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Me
asurableSpace γ} (κ : Probability…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_rat_lt`：exists_rat_lt (x : K) : exists q : Rat, (q : K) < x
· 使用定理 `Filter.tendsto_atTop_atBot`：tendsto_atTop_atBot : Tendsto f atTop atBot 
↔ forall b : β, exists i : α, forall a : α, i <= a -> f a <= b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
### Disintegration of kernels from `α` to `γ × ℝ` for countably generated `γ`
-/
lemma isRatCondKernelCDFAux_density_Iic (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDFAux (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) where
  measurable := measurable_pi_iff.mpr fun _ ↦ measurable_density κ (fst κ) measurableSet_Iic
  mono' a q r hqr :=
    ae_of_all _ fun c ↦ density_mono_set le_rfl a c (Iic_subset_Iic.mpr (by exact_mod_cast hqr))
  nonneg' _ _ := ae_of_all _ fun _ ↦ density_nonneg le_rfl _ _ _
  le_one' _ _ := ae_of_all _ fun _ ↦ density_le_one le_rfl _ _ _
  tendsto_integral_of_antitone a s hs_anti hs_tendsto := by
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    refine tendsto_integral_density_of_antitone le_rfl a s' ?_ ?_ (fun _ ↦ measurableSet_Iic)
    · refine fun i j hij ↦ Iic_subset_Iic.mpr ?_
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
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    refine tendsto_integral_density_of_monotone (le_rfl : fst κ ≤ fst κ)
      a s' ?_ ?_ (fun _ ↦ measurableSet_Iic)
    · exact fun i j hij ↦ Iic_subset_Iic.mpr (by exact mod_cast hs_mono hij)
    · ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      rw [tendsto_atTop_atTop] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_gt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, hq.le.trans ?_⟩
      exact mod_cast hi i le_rfl
  integrable a _ := integrable_density le_rfl a measurableSet_Iic
  setIntegral a _ hA _ := setIntegral_density le_rfl a measurableSet_Iic hA

/-- Taking the kernel density of intervals `Iic q` for `q : ℚ` gives a function with the property
`isRatCondKernelCDF`. -/
/-
**ProbabilityTheory.Kernel.isRatCondKernelCDF_density_Iic** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isRatCondKernelCDF_density_Iic (κ : Kernel α (γ × Real)) [IsFiniteKernel κ
] : IsRatCondKernelCDF (fun (p : α × γ) q => density κ (fst κ) p.1 p.2 (Iic q)) 
κ (fst κ)
参数：κ : Kernel α (γ × Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.isRatCondKernelCDF`：∀ {α : Type 
u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : Pro
babilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用引理 `ProbabilityTheory.Kernel.isRatCondKernelCDFAux_density_Iic`：isRatCondKer
nelCDFAux_density_Iic (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] : IsRatCondKe
rnelCDFAux (fun (p : α × γ) q => density κ (fst …
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.fst`：∀ {α : Type u_1} {β : Type 
u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Me
asurableSpace γ} (κ : Probability…

--- 原说明 ---
Taking the kernel density of intervals `Iic q` for `q : ℚ` gives a function with
 the property
`isRatCondKernelCDF`.
-/
lemma isRatCondKernelCDF_density_Iic (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDF (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) :=
  (isRatCondKernelCDFAux_density_Iic κ).isRatCondKernelCDF

/-- The conditional kernel CDF of a kernel `κ : Kernel α (γ × ℝ)`, where `γ` is countably generated.
-/
noncomputable
/-
**ProbabilityTheory.Kernel.condKernelCDF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：condKernelCDF (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] : α × γ -> Stie
ltjesFunction Real
参数：κ : Kernel α (γ × Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def condKernelCDF (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] : α × γ → StieltjesFunction ℝ :=
  stieltjesOfMeasurableRat (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q))
    (isRatCondKernelCDF_density_Iic κ).measurable
/-
**ProbabilityTheory.Kernel.isCondKernelCDF_condKernelCDF** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory.Kernel`。
形式化陈述：isCondKernelCDF_condKernelCDF (κ : Kernel α (γ × Real)) [IsFiniteKernel κ]
 : IsCondKernelCDF (condKernelCDF κ) κ (fst κ)
参数：κ : Kernel α (γ × Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.isCondKernelCDF_stieltjesOfMeasurableRat`：isCondKernel
CDF_stieltjesOfMeasurableRat {f : α × β -> Rat -> Real} (hf : IsRatCondKernelCDF
 f κ ν) [IsFiniteKernel κ] : IsCondKernelCDF (st…
· 使用引理 `ProbabilityTheory.Kernel.isRatCondKernelCDF_density_Iic`：isRatCondKernel
CDF_density_Iic (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] : IsRatCondKernelCD
F (fun (p : α × γ) q => density κ (fst κ) p.1…
-/
lemma isCondKernelCDF_condKernelCDF (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsCondKernelCDF (condKernelCDF κ) κ (fst κ) :=
  isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_density_Iic κ)

/-- Auxiliary definition for `ProbabilityTheory.Kernel.condKernel`.
A conditional kernel for `κ : Kernel α (γ × ℝ)` where `γ` is countably generated. -/
noncomputable
/-
**ProbabilityTheory.Kernel.condKernelReal** 是 Mathlib 中的一个定义，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：condKernelReal (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] : Kernel (α × 
γ) Real
参数：κ : Kernel α (γ × Real)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.isCondKernelCDF_condKernelCDF`：isCondKernelCDF_
condKernelCDF (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] : IsCondKernelCDF (co
ndKernelCDF κ) κ (fst κ)
-/
def condKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] : Kernel (α × γ) ℝ :=
  (isCondKernelCDF_condKernelCDF κ).toKernel
/-
**ProbabilityTheory.Kernel.instIsMarkovKernelCondKernelReal** 是 Mathlib 中的一个实例，位
于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：instIsMarkovKernelCondKernelReal (κ : Kernel α (γ × Real)) [IsFiniteKernel
 κ] : IsMarkovKernel (condKernelReal κ)
参数：κ : Kernel α (γ × Real)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.isCondKernelCDF_condKernelCDF`：isCondKernelCDF_
condKernelCDF (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] : IsCondKernelCDF (co
ndKernelCDF κ) κ (fst κ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.condKernelReal.eq_1`：∀ {α : Type u_1} {γ : Type
 u_3} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [inst : MeasurableSpac
e.CountablyGenerated γ] (κ : Proba…
-/
instance instIsMarkovKernelCondKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelReal κ) := by
  rw [condKernelReal]
  infer_instance
/-
**ProbabilityTheory.Kernel.compProd_fst_condKernelReal** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：compProd_fst_condKernelReal (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] :
 fst κ otimesₖ condKernelReal κ = κ
参数：κ : Kernel α (γ × Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.isCondKernelCDF_condKernelCDF`：isCondKernelCDF_
condKernelCDF (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] : IsCondKernelCDF (co
ndKernelCDF κ) κ (fst κ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.condKernelReal.eq_1`：∀ {α : Type u_1} {γ : Type
 u_3} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [inst : MeasurableSpac
e.CountablyGenerated γ] (κ : Proba…
· 使用引理 `ProbabilityTheory.compProd_toKernel`：compProd_toKernel [IsFiniteKernel κ
] [IsSFiniteKernel ν] (hf : IsCondKernelCDF f κ ν) : ν otimesₖ hf.toKernel f = κ
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma compProd_fst_condKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelReal κ = κ := by
  rw [condKernelReal, compProd_toKernel]

/-- Auxiliary definition for `MeasureTheory.Measure.condKernel` and
`ProbabilityTheory.Kernel.condKernel`.
A conditional kernel for `κ : Kernel Unit (α × ℝ)`. -/
noncomputable
/-
**ProbabilityTheory.Kernel.condKernelUnitReal** 是 Mathlib 中的一个定义，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：condKernelUnitReal (κ : Kernel Unit (α × Real)) [IsFiniteKernel κ] : Kerne
l (Unit × α) Real
参数：κ : Kernel Unit (α × Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def condKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] : Kernel (Unit × α) ℝ :=
  (isCondKernelCDF_condCDF (κ ())).toKernel
/-
**ProbabilityTheory.Kernel.instIsMarkovKernelCondKernelUnitReal** 是 Mathlib 中的一个
实例，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：instIsMarkovKernelCondKernelUnitReal (κ : Kernel Unit (α × Real)) [IsFinit
eKernel κ] : IsMarkovKernel (condKernelUnitReal κ)
参数：κ : Kernel Unit (α × Real)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.condKernelUnitReal.eq_1`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} (κ : ProbabilityTheory.Kernel Unit (α × ℝ))   [inst : Probab
ilityTheory.IsFiniteKernel κ],   κ.con…
-/
instance instIsMarkovKernelCondKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelUnitReal κ) := by
  rw [condKernelUnitReal]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**ProbabilityTheory.Kernel.condKernelUnitReal.instIsCondKernel** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory.Kernel.condKernelUnitReal`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} (κ : ProbabilityTheory.Kernel Un
it (α × ℝ))   [inst : ProbabilityTheory.IsFiniteKernel κ], κ.IsCondKernel κ.cond
KernelUnitReal
参数：κ : ProbabilityTheory.Kernel Unit (α × ℝ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.condKernelUnitReal.eq_1`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} (κ : ProbabilityTheory.Kernel Unit (α × ℝ))   [inst : Probab
ilityTheory.IsFiniteKernel κ],   κ.con…
· 使用引理 `ProbabilityTheory.compProd_toKernel`：compProd_toKernel [IsFiniteKernel κ
] [IsSFiniteKernel ν] (hf : IsCondKernelCDF f κ ν) : ν otimesₖ hf.toKernel f = κ
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance condKernelUnitReal.instIsCondKernel (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
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
/-
**ProbabilityTheory.Kernel.borelMarkovFromReal** 是 Mathlib 中的一个定义，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：borelMarkovFromReal (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [Standard
BorelSpace Ω] (η : Kernel α Real) : Kernel α Ω
参数：Ω : Type*；η : Kernel α Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
def borelMarkovFromReal (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α ℝ) :
    Kernel α Ω :=
  have he := measurableEmbedding_embeddingReal Ω
  let x₀ := (range_nonempty (embeddingReal Ω)).choose
  comapRight
    (piecewise ((Kernel.measurable_coe η he.measurableSet_range.compl) (measurableSet_singleton 0) :
        MeasurableSet {a | η a (range (embeddingReal Ω))ᶜ = 0})
      η (deterministic (fun _ ↦ x₀) measurable_const)) he
/-
**ProbabilityTheory.Kernel.borelMarkovFromReal_apply** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：borelMarkovFromReal_apply (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [St
andardBorelSpace Ω] (η : Kernel α Real) (a : α) : borelMarkovFromReal Ω η a = if
 η a (range (embeddingReal Ω))ᶜ = 0 then (η a).comap (embeddingReal Ω) else (Mea
sure.dirac (range_nonempty (embeddingReal Ω)).choose).comap (embeddingReal Ω)
参数：Ω : Type*；η : Kernel α Real；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.borelMarkovFromReal.eq_1`：∀ {α : Type u_1} {mα 
: MeasurableSpace α} (Ω : Type u_5) [inst : Nonempty Ω] [inst_1 : MeasurableSpac
e Ω]   [inst_2 : StandardBorelSpace Ω] …
· 使用定理 `ProbabilityTheory.Kernel.comapRight_apply`：comapRight_apply (κ : Kernel 
α β) (hf : MeasurableEmbedding f) (a : α) : comapRight κ hf a = Measure.comap f 
(κ a)
· 使用定理 `ProbabilityTheory.Kernel.piecewise_apply`：piecewise_apply (a : α) : piec
ewise hs κ η a = if a in s then κ a else η a
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma borelMarkovFromReal_apply (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α ℝ) (a : α) :
    borelMarkovFromReal Ω η a
      = if η a (range (embeddingReal Ω))ᶜ = 0 then (η a).comap (embeddingReal Ω)
        else (Measure.dirac (range_nonempty (embeddingReal Ω)).choose).comap (embeddingReal Ω) := by
  classical
  rw [borelMarkovFromReal, comapRight_apply, piecewise_apply, deterministic_apply]
  simp only [mem_preimage, mem_singleton_iff]
  split_ifs <;> rfl
/-
**ProbabilityTheory.Kernel.borelMarkovFromReal_apply'** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：borelMarkovFromReal_apply' (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [S
tandardBorelSpace Ω] (η : Kernel α Real) (a : α) {s : Set Ω} (hs : MeasurableSet
 s) : borelMarkovFromReal Ω η a s = if η a (range (embeddingReal Ω))ᶜ = 0 then η
 a (embeddingReal Ω '' s) else (embeddingReal Ω '' s).indicator 1 (range_nonempt
y (embeddingReal Ω)).choose
参数：Ω : Type*；η : Kernel α Real；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.borelMarkovFromReal_apply`：borelMarkovFromReal_
apply (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω] (η : K
ernel α Real) (a : α) : borelMarkovFromR…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `MeasurableEmbedding.measurableSet_image'`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measura
bleEmbedding f → ∀ ⦃s : Set α⦄…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.Measure.dirac_apply`：dirac_apply [MeasurableSingletonClass
 α] (a : α) (s : Set α) : dirac a s = s.indicator 1 a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
lemma borelMarkovFromReal_apply' (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α ℝ) (a : α) {s : Set Ω} (hs : MeasurableSet s) :
    borelMarkovFromReal Ω η a s
      = if η a (range (embeddingReal Ω))ᶜ = 0 then η a (embeddingReal Ω '' s)
        else (embeddingReal Ω '' s).indicator 1 (range_nonempty (embeddingReal Ω)).choose := by
  have he := measurableEmbedding_embeddingReal Ω
  rw [borelMarkovFromReal_apply]
  split_ifs with h
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs]
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs, Measure.dirac_apply]

/-- When `η` is an s-finite kernel, `borelMarkovFromReal Ω η` is an s-finite kernel. -/
/-
**ProbabilityTheory.Kernel.instIsSFiniteKernelBorelMarkovFromReal** 是 Mathlib 中的
一个实例，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：instIsSFiniteKernelBorelMarkovFromReal (η : Kernel α Real) [IsSFiniteKerne
l η] : IsSFiniteKernel (borelMarkovFromReal Ω η)
参数：η : Kernel α Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comapRight`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   
{mγ : MeasurableSpace γ} {f : γ → β} (κ :…
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.piecewise`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : Probability
Theory.Kernel α β}   {s : Set α} {hs : M…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…

--- 原说明 ---
When `η` is an s-finite kernel, `borelMarkovFromReal Ω η` is an s-finite kernel.
-/
instance instIsSFiniteKernelBorelMarkovFromReal (η : Kernel α ℝ) [IsSFiniteKernel η] :
    IsSFiniteKernel (borelMarkovFromReal Ω η) :=
  IsSFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)

/-- When `η` is a finite kernel, `borelMarkovFromReal Ω η` is a finite kernel. -/
/-
**ProbabilityTheory.Kernel.instIsFiniteKernelBorelMarkovFromReal** 是 Mathlib 中的一
个实例，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：instIsFiniteKernelBorelMarkovFromReal (η : Kernel α Real) [IsFiniteKernel 
η] : IsFiniteKernel (borelMarkovFromReal Ω η)
参数：η : Kernel α Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comapRight`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {
mγ : MeasurableSpace γ} {f : γ → β} (κ :…
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.piecewise`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : ProbabilityT
heory.Kernel α β}   {s : Set α} {hs : M…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…

--- 原说明 ---
When `η` is a finite kernel, `borelMarkovFromReal Ω η` is a finite kernel.
-/
instance instIsFiniteKernelBorelMarkovFromReal (η : Kernel α ℝ) [IsFiniteKernel η] :
    IsFiniteKernel (borelMarkovFromReal Ω η) :=
  IsFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)

/-- When `η` is a Markov kernel, `borelMarkovFromReal Ω η` is a Markov kernel. -/
/-
**ProbabilityTheory.Kernel.instIsMarkovKernelBorelMarkovFromReal** 是 Mathlib 中的一
个实例，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：instIsMarkovKernelBorelMarkovFromReal (η : Kernel α Real) [IsMarkovKernel 
η] : IsMarkovKernel (borelMarkovFromReal Ω η)
参数：η : Kernel α Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.comapRight`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {
mγ : MeasurableSpace γ} {f : γ → β} (κ :…
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.piecewise_apply`：piecewise_apply (a : α) : piec
ewise hs κ η a = if a in s then κ a else η a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.prob_compl_eq_zero_iff`：prob_compl_eq_zero_iff (hs : Measu
rableSet s) : μ sᶜ = 0 ↔ μ s = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasurableEmbedding.measurableSet_range`：measurableSet_range (hf : Measu
rableEmbedding f) : MeasurableSet (range f)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.dirac_apply_of_mem`：dirac_apply_of_mem {a : α} (h 
: a in s) : dirac a s = 1
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When `η` is a Markov kernel, `borelMarkovFromReal Ω η` is a Markov kernel.
-/
instance instIsMarkovKernelBorelMarkovFromReal (η : Kernel α ℝ) [IsMarkovKernel η] :
    IsMarkovKernel (borelMarkovFromReal Ω η) := by
  refine IsMarkovKernel.comapRight _ (measurableEmbedding_embeddingReal Ω) (fun a ↦ ?_)
  classical
  rw [piecewise_apply]
  split_ifs with h
  · rwa [← prob_compl_eq_zero_iff (measurableEmbedding_embeddingReal Ω).measurableSet_range]
  · rw [deterministic_apply]
    simp [(range_nonempty (embeddingReal Ω)).choose_spec]

/-- For `κ' := map κ (Prod.map (id : β → β) e)`, the hypothesis `hη` is `fst κ' ⊗ₖ η = κ'`.
The conclusion of the lemma is `fst κ ⊗ₖ borelMarkovFromReal Ω η = comapRight (fst κ' ⊗ₖ η) _`. -/
/-
**ProbabilityTheory.Kernel.compProd_fst_borelMarkovFromReal_eq_comapRight_compPr
od** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：compProd_fst_borelMarkovFromReal_eq_comapRight_compProd (κ : Kernel α (β ×
 Ω)) [IsSFiniteKernel κ] (η : Kernel (α × β) Real) [IsSFiniteKernel η] (hη : (fs
t (map κ (Prod.map (id : β -> β) (embeddingReal Ω)))) otimesₖ η = map κ (Prod.ma
p (id : β -> β) (embeddingReal Ω))) : fst κ otimesₖ borelMarkovFromReal Ω η = co
mapRight (fst (map κ (Prod.map (id : β -> β) (embeddingReal Ω))) otimesₖ η) (Mea
surableEmbedding.id.prodMap (measurableEmbedding_embeddingReal Ω))
参数：κ : Kernel α (β × Ω)；η : Kernel (α × β) Real；hη : (fst (map κ (Prod.map (id :
 β -> β) (embeddingReal Ω)))) otimesₖ η = map κ (Prod.map (id : β -> β) (embeddi
ngReal Ω))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
· 使用引理 `MeasurableEmbedding.prodMap`：MeasurableEmbedding.prodMap {α β γ δ : Type
*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {m
δ : MeasurableSpa…
· 使用定理 `MeasurableEmbedding.id`：id : MeasurableEmbedding (id : α -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.comapRight_compProd_id_prod`：comapRight_compPro
d_id_prod {δ : Type*} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKernel
 κ] (η : Kernel (α × β) γ) [IsSFiniteKerne…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `ProbabilityTheory.Kernel.fst_apply`：fst_apply (κ : Kernel α (β × γ)) (a 
: α) : fst κ a = (κ a).map Prod.fst
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用引理 `MeasureTheory.measurable_embeddingReal`：measurable_embeddingReal (Ω : Ty
pe*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : Measurable (embeddingReal Ω)
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comapRight`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   
{mγ : MeasurableSpace γ} {f : γ → β} (κ :…
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasurableEmbedding.measurableSet_range`：measurableSet_range (hf : Measu
rableEmbedding f) : MeasurableSet (range f)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
For `κ' := map κ (Prod.map (id : β → β) e)`, the hypothesis `hη` is `fst κ' ⊗ₖ η
 = κ'`.
The conclusion of the lemma is `fst κ ⊗ₖ borelMarkovFromReal Ω η = comapRight (f
st κ' ⊗ₖ η) _`.
-/
lemma compProd_fst_borelMarkovFromReal_eq_comapRight_compProd
    (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ] (η : Kernel (α × β) ℝ) [IsSFiniteKernel η]
    (hη : (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω)))) ⊗ₖ η
      = map κ (Prod.map (id : β → β) (embeddingReal Ω))) :
    fst κ ⊗ₖ borelMarkovFromReal Ω η
      = comapRight (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω))) ⊗ₖ η)
        (MeasurableEmbedding.id.prodMap (measurableEmbedding_embeddingReal Ω)) := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β → β) e)
  have hη' : fst κ' ⊗ₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β → β) e) :=
    MeasurableEmbedding.id.prodMap he
  change fst κ ⊗ₖ borelMarkovFromReal Ω η = comapRight (fst κ' ⊗ₖ η) h_prod_embed
  rw [comapRight_compProd_id_prod _ _ he]
  have h_fst : fst κ' = fst κ := by
    ext a u
    unfold κ'
    rw [fst_apply, map_apply _ (by fun_prop),
      Measure.map_map measurable_fst h_prod_embed.measurable, fst_apply]
    congr
  rw [h_fst]
  ext a t ht : 2
  simp_rw [compProd_apply ht]
  refine lintegral_congr_ae ?_
  have h_ae : ∀ᵐ t ∂(fst κ a), (a, t) ∈ {p : α × β | η p (range e)ᶜ = 0} := by
    rw [← h_fst]
    have h_compProd : κ' a (univ ×ˢ range e)ᶜ = 0 := by
      unfold κ'
      rw [map_apply' _ (by fun_prop)]
      swap; · exact (MeasurableSet.univ.prod he.measurableSet_range).compl
      suffices Prod.map id e ⁻¹' (univ ×ˢ range e)ᶜ = ∅ by rw [this]; simp
      ext x
      simp
    rw [← hη', compProd_null] at h_compProd
    swap; · exact (MeasurableSet.univ.prod he.measurableSet_range).compl
    simp only [preimage_compl, mem_univ, mk_preimage_prod_right] at h_compProd
    exact h_compProd
  filter_upwards [h_ae] with a ha
  rw [borelMarkovFromReal, comapRight_apply', comapRight_apply']
  rotate_left
  · exact measurable_prodMk_left ht
  · exact measurable_prodMk_left ht
  classical
  rw [piecewise_apply, if_pos]
  exact ha

/-- For `κ' := map κ (Prod.map (id : β → β) e)`, the hypothesis `hη` is `fst κ' ⊗ₖ η = κ'`.
With that hypothesis, `fst κ ⊗ₖ borelMarkovFromReal κ η = κ`. -/
/-
**ProbabilityTheory.Kernel.compProd_fst_borelMarkovFromReal** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：compProd_fst_borelMarkovFromReal (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ
] (η : Kernel (α × β) Real) [IsSFiniteKernel η] (hη : (fst (map κ (Prod.map (id 
: β -> β) (embeddingReal Ω)))) otimesₖ η = map κ (Prod.map (id : β -> β) (embedd
ingReal Ω))) : fst κ otimesₖ borelMarkovFromReal Ω η = κ
参数：κ : Kernel α (β × Ω)；η : Kernel (α × β) Real；hη : (fst (map κ (Prod.map (id :
 β -> β) (embeddingReal Ω)))) otimesₖ η = map κ (Prod.map (id : β -> β) (embeddi
ngReal Ω))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
· 使用引理 `MeasurableEmbedding.prodMap`：MeasurableEmbedding.prodMap {α β γ δ : Type
*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {m
δ : MeasurableSpa…
· 使用定理 `MeasurableEmbedding.id`：id : MeasurableEmbedding (id : α -> α)
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comapRight_apply`：comapRight_apply (κ : Kernel 
α β) (hf : MeasurableEmbedding f) (a : α) : comapRight κ hf a = Measure.comap f 
(κ a)
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用引理 `MeasureTheory.measurable_embeddingReal`：measurable_embeddingReal (Ω : Ty
pe*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : Measurable (embeddingReal Ω)
· 使用定理 `MeasurableEmbedding.comap_map`：comap_map (μ : Measure α) : (map f μ).com
ap f = μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.compProd_fst_borelMarkovFromReal_eq_comapRight_
compProd`：compProd_fst_borelMarkovFromReal_eq_comapRight_compProd (κ : Kernel α 
(β × Ω)) [IsSFiniteKernel κ] (η : Kernel (α × β) Real) [IsSFiniteKerne…

--- 原说明 ---
For `κ' := map κ (Prod.map (id : β → β) e)`, the hypothesis `hη` is `fst κ' ⊗ₖ η
 = κ'`.
With that hypothesis, `fst κ ⊗ₖ borelMarkovFromReal κ η = κ`.
-/
lemma compProd_fst_borelMarkovFromReal (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ]
    (η : Kernel (α × β) ℝ) [IsSFiniteKernel η]
    (hη : (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω)))) ⊗ₖ η
      = map κ (Prod.map (id : β → β) (embeddingReal Ω))) :
    fst κ ⊗ₖ borelMarkovFromReal Ω η = κ := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β → β) e)
  have hη' : fst κ' ⊗ₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β → β) e) :=
    MeasurableEmbedding.id.prodMap he
  have : κ = comapRight κ' h_prod_embed := by
    ext c t : 2
    unfold κ'
    rw [comapRight_apply, map_apply _ (by fun_prop), h_prod_embed.comap_map]
  conv_rhs => rw [this, ← hη']
  exact compProd_fst_borelMarkovFromReal_eq_comapRight_compProd κ η hη

end BorelSnd

section CountablyGenerated

open ProbabilityTheory.Kernel

/-- Auxiliary definition for `ProbabilityTheory.Kernel.condKernel`.
A conditional kernel for `κ : Kernel α (γ × Ω)` where `γ` is countably generated and `Ω` is
standard Borel. -/
noncomputable
/-
**ProbabilityTheory.Kernel.condKernelBorel** 是 Mathlib 中的一个定义，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：condKernelBorel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] : Kernel (α × γ)
 Ω
参数：κ : Kernel α (γ × Ω)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def condKernelBorel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] : Kernel (α × γ) Ω :=
  let κ' := map κ (Prod.map (id : γ → γ) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelReal κ')
/-
**ProbabilityTheory.Kernel.instIsMarkovKernelCondKernelBorel** 是 Mathlib 中的一个实例，
位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：instIsMarkovKernelCondKernelBorel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ
] : IsMarkovKernel (condKernelBorel κ)
参数：κ : Kernel α (γ × Ω)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.condKernelBorel.eq_1`：∀ {α : Type u_1} {γ : Typ
e u_3} {Ω : Type u_4} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [inst 
: MeasurableSpace.CountablyGenerate…
-/
instance instIsMarkovKernelCondKernelBorel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelBorel κ) := by
  rw [condKernelBorel]
  infer_instance
/-
**ProbabilityTheory.Kernel.condKernelBorel.instIsCondKernel** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.Kernel.condKernelBorel`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} {Ω : Type u_4} {mα : MeasurableSpace α} {m
γ : MeasurableSpace γ}   [inst : MeasurableSpace.CountablyGenerated γ] {mΩ : Mea
surableSpace Ω} [inst_1 : StandardBorelSpace Ω]   [inst_2 : Nonempty Ω] (κ : Pro
babilityTheory.Kernel α (γ × Ω)) [inst_3 : ProbabilityTheory.IsFiniteKernel κ], 
  κ.IsCondKernel κ.condKernelBorel
参数：κ : ProbabilityTheory.Kernel α (γ × Ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.condKernelBorel.eq_1`：∀ {α : Type u_1} {γ : Typ
e u_3} {Ω : Type u_4} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [inst 
: MeasurableSpace.CountablyGenerate…
· 使用引理 `ProbabilityTheory.Kernel.compProd_fst_borelMarkovFromReal`：compProd_fst_
borelMarkovFromReal (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ] (η : Kernel (α × 
β) Real) [IsSFiniteKernel η] (hη : (fst (map κ …
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.Kernel.compProd_fst_condKernelReal`：compProd_fst_condK
ernelReal (κ : Kernel α (γ × Real)) [IsFiniteKernel κ] : fst κ otimesₖ condKerne
lReal κ = κ
-/
instance condKernelBorel.instIsCondKernel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] :
    κ.IsCondKernel κ.condKernelBorel where
  disintegrate := by
    rw [condKernelBorel, compProd_fst_borelMarkovFromReal _ _ (compProd_fst_condKernelReal _)]

end CountablyGenerated

section Unit
variable (κ : Kernel Unit (α × Ω)) [IsFiniteKernel κ]

/-- Auxiliary definition for `MeasureTheory.Measure.condKernel` and
`ProbabilityTheory.Kernel.condKernel`.
A conditional kernel for `κ : Kernel Unit (α × Ω)` where `Ω` is standard Borel. -/
noncomputable
/-
**ProbabilityTheory.Kernel.condKernelUnitBorel** 是 Mathlib 中的一个定义，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：condKernelUnitBorel : Kernel (Unit × α) Ω
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def condKernelUnitBorel : Kernel (Unit × α) Ω :=
  let κ' := map κ (Prod.map (id : α → α) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelUnitReal κ')
/-
**ProbabilityTheory.Kernel.instIsMarkovKernelCondKernelUnitBorel** 是 Mathlib 中的一
个实例，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：instIsMarkovKernelCondKernelUnitBorel : IsMarkovKernel κ.condKernelUnitBor
el
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.condKernelUnitBorel.eq_1`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (κ :…
-/
instance instIsMarkovKernelCondKernelUnitBorel : IsMarkovKernel κ.condKernelUnitBorel := by
  rw [condKernelUnitBorel]
  infer_instance
/-
**ProbabilityTheory.Kernel.condKernelUnitBorel.instIsCondKernel** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.Kernel.condKernelUnitBorel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableS
pace Ω} [inst : StandardBorelSpace Ω]   [inst_1 : Nonempty Ω] (κ : ProbabilityTh
eory.Kernel Unit (α × Ω)) [inst_2 : ProbabilityTheory.IsFiniteKernel κ],   κ.IsC
ondKernel κ.condKernelUnitBorel
参数：κ : ProbabilityTheory.Kernel Unit (α × Ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.condKernelUnitBorel.eq_1`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (κ :…
· 使用引理 `ProbabilityTheory.Kernel.compProd_fst_borelMarkovFromReal`：compProd_fst_
borelMarkovFromReal (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ] (η : Kernel (α × 
β) Real) [IsSFiniteKernel η] (hη : (fst (map κ …
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.Kernel.disintegrate`：disintegrate [κ.IsCondKernel κCon
d] : κ.fst otimesₖ κCond = κ
· 使用定理 `ProbabilityTheory.Kernel.condKernelUnitReal.instIsCondKernel`：∀ {α : Typ
e u_1} {mα : MeasurableSpace α} (κ : ProbabilityTheory.Kernel Unit (α × ℝ))   [i
nst : ProbabilityTheory.IsFiniteKernel κ], κ.IsCon…
-/
instance condKernelUnitBorel.instIsCondKernel : κ.IsCondKernel κ.condKernelUnitBorel where
  disintegrate := by
    rw [condKernelUnitBorel, compProd_fst_borelMarkovFromReal _ _ (disintegrate _ _)]

end Unit

section Measure

variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/-- Conditional kernel of a measure on a product space: a Markov kernel such that
`ρ = ρ.fst ⊗ₘ ρ.condKernel` (see `MeasureTheory.Measure.compProd_fst_condKernel`). -/
noncomputable
irreducible_def _root_.MeasureTheory.Measure.condKernel (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    Kernel α Ω :=
  comap (condKernelUnitBorel (const Unit ρ)) (fun a ↦ ((), a)) measurable_prodMk_left

/-
**ProbabilityTheory.Kernel._root_.MeasureTheory.Measure.condKernel_apply** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.Measure.condKernel_apply (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]
    (a : α) :
    ρ.condKernel a = condKernelUnitBorel (const Unit ρ) ((), a) := by
  rw [Measure.condKernel]; rfl
/-
**ProbabilityTheory.Kernel._root_.MeasureTheory.Measure.condKernel.instIsCondKer
nel** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
    rw [Measure.compProd, h1, h2, disintegrate]
    simp
/-
**ProbabilityTheory.Kernel._root_.MeasureTheory.Measure.instIsMarkovKernelCondKe
rnel** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.MeasureTheory.Measure.instIsMarkovKernelCondKernel
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] : IsMarkovKernel ρ.condKernel := by
  rw [Measure.condKernel]
  infer_instance

/-- If the singleton `{x}` has non-zero mass for `ρ.fst`, then for all `s : Set Ω`,
`ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)` . -/
/-
**ProbabilityTheory.Kernel._root_.MeasureTheory.Measure.condKernel_apply_of_ne_z
ero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the singleton `{x}` has non-zero mass for `ρ.fst`, then for all `s : Set Ω`,
`ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)` .
-/
lemma _root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero [MeasurableSingletonClass α]
    {x : α} (hx : ρ.fst {x} ≠ 0) (s : Set Ω) :
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
    condKernelCountable (fun a ↦ (κ a).condKernel)
      fun x y h ↦ by simp [apply_congr_of_mem_measurableAtom _ h]
  else letI := h.countableOrCountablyGenerated.resolve_left hα; condKernelBorel κ

/-- `condKernel κ` is a Markov kernel. -/
/-
**ProbabilityTheory.Kernel.instIsMarkovKernelCondKernel** 是 Mathlib 中的一个实例，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：instIsMarkovKernelCondKernel : IsMarkovKernel (condKernel κ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.condKernel_def`：∀ {α : Type u_5} {β : Type u_6}
 {Ω : Type u_7} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mΩ : Measur
ableSpace Ω} [inst : Standard…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ProbabilityTheory.Kernel.condKernelCountable.instIsMarkovKernel`：∀ {α : 
Type u_1} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {mβ : Measurabl
eSpace β}   {mΩ : MeasurableSpace Ω} [inst : Countabl…
· 使用定理 `MeasureTheory.Measure.instIsMarkovKernelCondKernel`：∀ {α : Type u_1} {Ω 
: Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBo
relSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc

--- 原说明 ---
`condKernel κ` is a Markov kernel.
-/
instance instIsMarkovKernelCondKernel : IsMarkovKernel (condKernel κ) := by
  rw [condKernel_def]
  split_ifs <;> infer_instance
/-
**ProbabilityTheory.Kernel.condKernel.instIsCondKernel** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.condKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {Ω : Type u_4} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mΩ : MeasurableSpace Ω} [inst : StandardBorelSpace Ω] 
[inst_1 : Nonempty Ω]   [h : MeasurableSpace.CountableOrCountablyGenerated α β] 
(κ : ProbabilityTheory.Kernel α (β × Ω))   [inst_2 : ProbabilityTheory.IsFiniteK
ernel κ], κ.IsCondKernel κ.condKernel
参数：κ : ProbabilityTheory.Kernel α (β × Ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.condKernel_def`：∀ {α : Type u_5} {β : Type u_6}
 {Ω : Type u_7} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mΩ : Measur
ableSpace Ω} [inst : Standard…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `ProbabilityTheory.Kernel.disintegrate`：disintegrate [κ.IsCondKernel κCon
d] : κ.fst otimesₖ κCond = κ
· 使用定理 `ProbabilityTheory.Kernel.condKernelCountable.instIsCondKernel`：∀ {α : Ty
pe u_1} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {mΩ : MeasurableSpace Ω} [inst : Countabl…
· 使用定理 `MeasureTheory.Measure.instIsMarkovKernelCondKernel`：∀ {α : Type u_1} {Ω 
: Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBo
relSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.condKernel.instIsCondKernel`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `ProbabilityTheory.Kernel.condKernelBorel.instIsCondKernel`：∀ {α : Type u
_1} {γ : Type u_3} {Ω : Type u_4} {mα : MeasurableSpace α} {mγ : MeasurableSpace
 γ}   [inst : MeasurableSpace.CountablyGenerate…
-/
instance condKernel.instIsCondKernel : κ.IsCondKernel κ.condKernel where
  disintegrate := by rw [condKernel_def]; split_ifs with hα <;> exact disintegrate _ _

end CountableOrCountablyGenerated

end ProbabilityTheory.Kernel

