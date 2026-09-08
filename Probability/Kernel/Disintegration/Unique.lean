/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Uniqueness of the conditional kernel

We prove that the conditional kernels `ProbabilityTheory.Kernel.condKernel` and
`MeasureTheory.Measure.condKernel` are almost everywhere unique.

## Main statements

* `ProbabilityTheory.eq_condKernel_of_kernel_eq_compProd`: a.e. uniqueness of
  `ProbabilityTheory.Kernel.condKernel`
* `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`: a.e. uniqueness of
  `MeasureTheory.Measure.condKernel`
* `ProbabilityTheory.Kernel.condKernel_apply_eq_condKernel`: the kernel `condKernel` is almost
  everywhere equal to the measure `condKernel`.
-/

public section

open MeasureTheory Set Filter MeasurableSpace

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Measure

variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/-! ### Uniqueness of `Measure.condKernel`

The conditional kernel of a measure is unique almost everywhere. -/

/-- An s-finite kernel which satisfies the disintegration property of the given measure `ρ` is
almost everywhere equal to the disintegration kernel of `ρ` when evaluated on a measurable set.

This theorem in the case of finite kernels is weaker than `eq_condKernel_of_measure_eq_compProd`
which asserts that the kernels are equal almost everywhere and not just on a given measurable
set. -/
/-
**ProbabilityTheory.eq_condKernel_of_measure_eq_compProd'** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：eq_condKernel_of_measure_eq_compProd' (κ : Kernel α Ω) [IsSFiniteKernel κ]
 (hκ : ρ = ρ.fst otimesₘ κ) {s : Set Ω} (hs : MeasurableSet s) : forallᵐ x ∂ρ.fs
t, κ x s = ρ.condKernel x s
参数：κ : Kernel α Ω；hκ : ρ = ρ.fst otimesₘ κ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`：ae_eq_of_f
orall_setLIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf :
 Measurable f) (hg : Measurable g) (h : forall s, …
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.fst.instIsFiniteMeasure`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureThe
ory.Measure (α × β)} [MeasureTheory…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.setLIntegral_condKernel_eq_measure_prod`：setLInteg
ral_condKernel_eq_measure_prod {s : Set β} (hs : MeasurableSet s) {t : Set Ω} (h
t : MeasurableSet t) : ∫⁻ b in s, ρ.condKernel b t …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.compProd_apply_prod`：compProd_apply_prod [SFinite 
μ] [IsSFiniteKernel κ] {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : Meas
urableSet t) : (μ otimesₘ κ) (s…
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ

--- 原说明 ---
An s-finite kernel which satisfies the disintegration property of the given meas
ure `ρ` is
almost everywhere equal to the disintegration kernel of `ρ` when evaluated on a 
measurable set.

This theorem in the case of finite kernels is weaker than `eq_condKernel_of_meas
ure_eq_compProd`
which asserts that the kernels are equal almost everywhere and not just on a giv
en measurable
set.
-/
theorem eq_condKernel_of_measure_eq_compProd' (κ : Kernel α Ω) [IsSFiniteKernel κ]
    (hκ : ρ = ρ.fst ⊗ₘ κ) {s : Set Ω} (hs : MeasurableSet s) :
    ∀ᵐ x ∂ρ.fst, κ x s = ρ.condKernel x s := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Kernel.measurable_coe κ hs) (Kernel.measurable_coe ρ.condKernel hs) (fun t ht _ ↦ ?_)
  conv_rhs => rw [Measure.setLIntegral_condKernel_eq_measure_prod ht hs, hκ]
  exact (Measure.compProd_apply_prod ht hs).symm

/-- Auxiliary lemma for `eq_condKernel_of_measure_eq_compProd`.
Uniqueness of the disintegration kernel on ℝ. -/
/-
**ProbabilityTheory.eq_condKernel_of_measure_eq_compProd_real** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：eq_condKernel_of_measure_eq_compProd_real {ρ : Measure (α × Real)} [IsFini
teMeasure ρ] (κ : Kernel α Real) [IsFiniteKernel κ] (hκ : ρ = ρ.fst otimesₘ κ) :
 forallᵐ x ∂ρ.fst, κ x = ρ.condKernel x
参数：α × Real；κ : Kernel α Real；hκ : ρ = ρ.fst otimesₘ κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd'`：eq_condKernel_o
f_measure_eq_compProd' (κ : Kernel α Ω) [IsSFiniteKernel κ] (hκ : ρ = ρ.fst otim
esₘ κ) {s : Set Ω} (hs : MeasurableSet s) : f…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasurableSpace.ae_induction_on_inter`：∀ {α : Type u_6} {β : Type u_7} [
inst : MeasurableSpace β] {μ : MeasureTheory.Measure β} {C : β → Set α → Prop}  
 {s : Set (Set α)} [m : Mea…
· 使用定理 `Real.borel_eq_generateFrom_Iic_rat`：borel_eq_generateFrom_Iic_rat : bore
l Real = .generateFrom (⋃ a : Rat, {Iic (a : Real)})
· 使用定理 `Real.isPiSystem_Iic_rat`：isPiSystem_Iic_rat : IsPiSystem (⋃ a : Rat, {Ii
c (a : Real)})
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `eq_condKernel_of_measure_eq_compProd`.
Uniqueness of the disintegration kernel on ℝ.
-/
lemma eq_condKernel_of_measure_eq_compProd_real {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    (κ : Kernel α ℝ) [IsFiniteKernel κ] (hκ : ρ = ρ.fst ⊗ₘ κ) :
    ∀ᵐ x ∂ρ.fst, κ x = ρ.condKernel x := by
  have huniv : ∀ᵐ x ∂ρ.fst, κ x Set.univ = ρ.condKernel x Set.univ :=
    eq_condKernel_of_measure_eq_compProd' κ hκ MeasurableSet.univ
  suffices ∀ᵐ x ∂ρ.fst, ∀ ⦃t⦄, MeasurableSet t → κ x t = ρ.condKernel x t by
    filter_upwards [this] with x hx
    ext t ht; exact hx ht
  apply MeasurableSpace.ae_induction_on_inter Real.borel_eq_generateFrom_Iic_rat
    Real.isPiSystem_Iic_rat
  · simp
  · simp only [iUnion_singleton_eq_range, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact ae_all_iff.2 fun q ↦ eq_condKernel_of_measure_eq_compProd' κ hκ measurableSet_Iic
  · filter_upwards [huniv] with x hxuniv t ht heq
    rw [measure_compl ht <| measure_ne_top _ _, heq, hxuniv, measure_compl ht <| measure_ne_top _ _]
  · refine ae_of_all _ (fun x f hdisj hf heq ↦ ?_)
    rw [measure_iUnion hdisj hf, measure_iUnion hdisj hf]
    exact tsum_congr heq

/-- A finite kernel which satisfies the disintegration property is almost everywhere equal to the
disintegration kernel. -/
/-
**ProbabilityTheory.eq_condKernel_of_measure_eq_compProd** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：eq_condKernel_of_measure_eq_compProd (κ : Kernel α Ω) [IsFiniteKernel κ] (
hκ : ρ = ρ.fst otimesₘ κ) : forallᵐ x ∂ρ.fst, κ x = ρ.condKernel x
参数：κ : Kernel α Ω；hκ : ρ = ρ.fst otimesₘ κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.fst_apply`：fst_apply {s : Set α} (hs : MeasurableS
et s) : ρ.fst s = ρ (Prod.fst ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Measurable.prod`：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun 
a => (f a).1) (hf₂ : Measurable fun a => (f a).2) : Measurable f
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd_real`：eq_condKern
el_of_measure_eq_compProd_real {ρ : Measure (α × Real)} [IsFiniteMeasure ρ] (κ :
 Kernel α Real) [IsFiniteKernel κ] (hκ : ρ = ρ.fs…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} (κ : Probability…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
A finite kernel which satisfies the disintegration property is almost everywhere
 equal to the
disintegration kernel.
-/
theorem eq_condKernel_of_measure_eq_compProd (κ : Kernel α Ω) [IsFiniteKernel κ]
    (hκ : ρ = ρ.fst ⊗ₘ κ) :
    ∀ᵐ x ∂ρ.fst, κ x = ρ.condKernel x := by
  -- The idea is to transport the question to `ℝ` from `Ω` using `embeddingReal`
  -- and then construct a measure on `α × ℝ`
  let f := embeddingReal Ω
  have hf := measurableEmbedding_embeddingReal Ω
  set ρ' : Measure (α × ℝ) := ρ.map (Prod.map id f) with hρ'def
  have hρ' : ρ'.fst = ρ.fst := by
    ext s hs
    rw [hρ'def, Measure.fst_apply, Measure.fst_apply, Measure.map_apply]
    exacts [rfl, Measurable.prod measurable_fst <| hf.measurable.comp measurable_snd,
      measurable_fst hs, hs, hs]
  have hρ'' : ∀ᵐ x ∂ρ.fst, Kernel.map κ f x = ρ'.condKernel x := by
    rw [← hρ']
    refine eq_condKernel_of_measure_eq_compProd_real (Kernel.map κ f) ?_
    ext s hs
    conv_lhs => rw [hρ'def, hκ]
    rw [Measure.map_apply (measurable_id.prodMap hf.measurable) hs, hρ',
      Measure.compProd_apply hs, Measure.compProd_apply (measurable_id.prodMap hf.measurable hs)]
    congr with a
    rw [Kernel.map_apply' _ hf.measurable]
    exacts [rfl, measurable_prodMk_left hs]
  suffices ∀ᵐ x ∂ρ.fst, ∀ s, MeasurableSet s → ρ'.condKernel x s = ρ.condKernel x (f ⁻¹' s) by
    filter_upwards [hρ'', this] with x hx h
    rw [Kernel.map_apply _ hf.measurable] at hx
    ext s hs
    rw [← Set.preimage_image_eq s hf.injective,
      ← Measure.map_apply hf.measurable <| hf.measurableSet_image.2 hs, hx,
      h _ <| hf.measurableSet_image.2 hs]
  suffices ρ.map (Prod.map id f) = (ρ.fst ⊗ₘ (Kernel.map ρ.condKernel f)) by
    rw [← hρ'] at this
    have heq := eq_condKernel_of_measure_eq_compProd_real _ this
    rw [hρ'] at heq
    filter_upwards [heq] with x hx s hs
    rw [← hx, Kernel.map_apply _ hf.measurable, Measure.map_apply hf.measurable hs]
  ext s hs
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.compProd_apply hs, Measure.map_apply (measurable_id.prodMap hf.measurable) hs,
    Measure.compProd_apply]
  · congr with a
    rw [Kernel.map_apply' _ hf.measurable]
    exacts [rfl, measurable_prodMk_left hs]
  · exact measurable_id.prodMap hf.measurable hs
/-
**ProbabilityTheory.condKernel_compProd** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：condKernel_compProd (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α Ω) [
IsMarkovKernel κ] : (μ otimesₘ κ).condKernel =ᵐ[μ] κ
参数：μ : Measure α；κ : Kernel α Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`：eq_condKernel_of
_measure_eq_compProd (κ : Kernel α Ω) [IsFiniteKernel κ] (hκ : ρ = ρ.fst otimesₘ
 κ) : forallᵐ x ∂ρ.fst, κ x = ρ.condKernel x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.fst_compProd`：fst_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsMarkovKernel κ] : (μ otimesₘ κ).fst = μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
lemma condKernel_compProd (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α Ω) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).condKernel =ᵐ[μ] κ := by
  suffices κ =ᵐ[(μ ⊗ₘ κ).fst] (μ ⊗ₘ κ).condKernel by symm; rwa [Measure.fst_compProd] at this
  refine eq_condKernel_of_measure_eq_compProd _ ?_
  rw [Measure.fst_compProd]

end Measure

section KernelAndMeasure

/-
**ProbabilityTheory.Kernel.apply_eq_measure_condKernel_of_compProd_eq** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace
 Ω] [inst_2 : Nonempty Ω]   {ρ : ProbabilityTheory.Kernel α (β × Ω)} [inst_3 : P
robabilityTheory.IsFiniteKernel ρ]   {κ : ProbabilityTheory.Kernel (α × β) Ω} [P
robabilityTheory.IsFiniteKernel κ],   ρ.fst.compProd κ = ρ → ∀ (a : α), (fun b =
> κ (a, b)) =ᵐ[ρ.fst a] ⇑(ρ a).condKernel
参数：β × Ω；α × β；a : α；fun b => κ (a, b)；ρ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`：eq_condKernel_of
_measure_eq_compProd (κ : Kernel α Ω) [IsFiniteKernel κ] (hκ : ρ = ρ.fst otimesₘ
 κ) : forallᵐ x ∂ρ.fst, κ x = ρ.condKernel x
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comap`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} {g : γ → α} (κ :…
· 使用定理 `ProbabilityTheory.Kernel.fst_apply`：fst_apply (κ : Kernel α (β × γ)) (a 
: α) : fst κ a = (κ a).map Prod.fst
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.Kernel.comap_apply`：comap_apply (κ : Kernel α β) (hg :
 Measurable g) (c : γ) : comap κ g hg c = κ (g c)
-/
lemma Kernel.apply_eq_measure_condKernel_of_compProd_eq
    {ρ : Kernel α (β × Ω)} [IsFiniteKernel ρ] {κ : Kernel (α × β) Ω} [IsFiniteKernel κ]
    (hκ : Kernel.fst ρ ⊗ₖ κ = ρ) (a : α) :
    (fun b ↦ κ (a, b)) =ᵐ[Kernel.fst ρ a] (ρ a).condKernel := by
  have : ρ a = (ρ a).fst ⊗ₘ Kernel.comap κ (fun b ↦ (a, b)) measurable_prodMk_left := by
    ext s hs
    conv_lhs => rw [← hκ]
    rw [Measure.compProd_apply hs, Kernel.compProd_apply hs]
    rfl
  have h := eq_condKernel_of_measure_eq_compProd _ this
  rw [Kernel.fst_apply]
  filter_upwards [h] with b hb
  rw [← hb, Kernel.comap_apply]

/-- For `fst κ a`-almost all `b`, the conditional kernel `Kernel.condKernel κ` applied to `(a, b)`
is equal to the conditional kernel of the measure `κ a` applied to `b`. -/
/-
**ProbabilityTheory.Kernel.condKernel_apply_eq_condKernel** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace
 Ω] [inst_2 : Nonempty Ω]   [inst_3 : MeasurableSpace.CountableOrCountablyGenera
ted α β] (κ : ProbabilityTheory.Kernel α (β × Ω))   [inst_4 : ProbabilityTheory.
IsFiniteKernel κ] (a : α), (fun b => κ.condKernel (a, b)) =ᵐ[κ.fst a] ⇑(κ a).con
dKernel
参数：κ : ProbabilityTheory.Kernel α (β × Ω)；a : α；fun b => κ.condKernel (a, b)；κ a
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.apply_eq_measure_condKernel_of_compProd_eq`：∀ {
α : Type u_1} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {mβ : Measu
rableSpace β}   [inst : MeasurableSpace Ω] [inst_1 : Stan…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.Kernel.disintegrate`：disintegrate [κ.IsCondKernel κCon
d] : κ.fst otimesₖ κCond = κ
· 使用定理 `ProbabilityTheory.Kernel.condKernel.instIsCondKernel`：∀ {α : Type u_1} {
β : Type u_2} {Ω : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mΩ : MeasurableSpace Ω} [inst : Standard…

--- 原说明 ---
For `fst κ a`-almost all `b`, the conditional kernel `Kernel.condKernel κ` appli
ed to `(a, b)`
is equal to the conditional kernel of the measure `κ a` applied to `b`.
-/
lemma Kernel.condKernel_apply_eq_condKernel [CountableOrCountablyGenerated α β]
    (κ : Kernel α (β × Ω)) [IsFiniteKernel κ] (a : α) :
    (fun b ↦ Kernel.condKernel κ (a, b)) =ᵐ[Kernel.fst κ a] (κ a).condKernel :=
  Kernel.apply_eq_measure_condKernel_of_compProd_eq (κ.disintegrate _) a
/-
**ProbabilityTheory.condKernel_const** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：condKernel_const [CountableOrCountablyGenerated α β] (ρ : Measure (β × Ω))
 [IsFiniteMeasure ρ] (a : α) : (fun b => Kernel.condKernel (Kernel.const α ρ) (a
, b)) =ᵐ[ρ.fst] ρ.condKernel
参数：ρ : Measure (β × Ω)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.condKernel_apply_eq_condKernel`：∀ {α : Type u_1
} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β
}   [inst : MeasurableSpace Ω] [inst_1 : Stan…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma condKernel_const [CountableOrCountablyGenerated α β] (ρ : Measure (β × Ω)) [IsFiniteMeasure ρ]
    (a : α) :
    (fun b ↦ Kernel.condKernel (Kernel.const α ρ) (a, b)) =ᵐ[ρ.fst] ρ.condKernel := by
  have h := Kernel.condKernel_apply_eq_condKernel (Kernel.const α ρ) a
  simp_rw [Kernel.fst_apply, Kernel.const_apply] at h
  filter_upwards [h] with b hb using hb

end KernelAndMeasure

section Kernel

/-! ### Uniqueness of `Kernel.condKernel`

The conditional kernel is unique almost everywhere. -/

/-- A finite kernel which satisfies the disintegration property is almost everywhere equal to the
disintegration kernel. -/
/-
**ProbabilityTheory.eq_condKernel_of_kernel_eq_compProd** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：eq_condKernel_of_kernel_eq_compProd [CountableOrCountablyGenerated α β] {ρ
 : Kernel α (β × Ω)} [IsFiniteKernel ρ] {κ : Kernel (α × β) Ω} [IsFiniteKernel κ
] (hκ : Kernel.fst ρ otimesₖ κ = ρ) (a : α) : forallᵐ x ∂(Kernel.fst ρ a), κ (a,
 x) = Kernel.condKernel ρ (a, x)
参数：β × Ω；α × β；hκ : Kernel.fst ρ otimesₖ κ = ρ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.apply_eq_measure_condKernel_of_compProd_eq`：∀ {
α : Type u_1} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {mβ : Measu
rableSpace β}   [inst : MeasurableSpace Ω] [inst_1 : Stan…
· 使用定理 `ProbabilityTheory.Kernel.condKernel_apply_eq_condKernel`：∀ {α : Type u_1
} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β
}   [inst : MeasurableSpace Ω] [inst_1 : Stan…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
A finite kernel which satisfies the disintegration property is almost everywhere
 equal to the
disintegration kernel.
-/
theorem eq_condKernel_of_kernel_eq_compProd [CountableOrCountablyGenerated α β]
    {ρ : Kernel α (β × Ω)} [IsFiniteKernel ρ] {κ : Kernel (α × β) Ω} [IsFiniteKernel κ]
    (hκ : Kernel.fst ρ ⊗ₖ κ = ρ) (a : α) :
    ∀ᵐ x ∂(Kernel.fst ρ a), κ (a, x) = Kernel.condKernel ρ (a, x) := by
  filter_upwards [Kernel.condKernel_apply_eq_condKernel ρ a,
    Kernel.apply_eq_measure_condKernel_of_compProd_eq hκ a] with a h1 h2
  rw [h1, h2]

end Kernel

end ProbabilityTheory

