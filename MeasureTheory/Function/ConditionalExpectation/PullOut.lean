/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.Holder

/-!
# Pull-out property of the conditional expectation

Let `Ω` be endowed with a measurable space structure `mΩ`, and let `m : MeasurableSpace Ω` such that
`m ≤ mΩ`. Let `μ` be a measure over `Ω`. Let `B : F →L[ℝ] E →L[ℝ] G` a continuous bilinear map,
`f : Ω → F` and `g : Ω → E` such that `fun ω ↦ B (f ω) (g ω)` is integrable, `g` is integrable
and `f` is `AEStronglyMeasurable` with respect to `m`. The **pull-out** property of the conditional
expectation states that almost surely, `μ[B f g|m] = B f μ[g|m]`.

We specialize this statement to the cases where `B` is scalar multiplication and multiplication.

## Main statements

* `condExp_bilin_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[B f g|m] = B f μ[g|m]`.
* `condExp_smul_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[f • g|m] = f • μ[g|m]`.
* `condExp_mul_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[f * g|m] = f * μ[g|m]`.

## Tags

conditional expectation, pull-out, bilinear map
-/

public section


open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G] (B : F →L[ℝ] E →L[ℝ] G)

/-- Auxiliary lemma for `condExp_bilin_of_stronglyMeasurable_left`. -/
/-
**MeasureTheory.condExp_stronglyMeasurable_simpleFunc_bilin** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：condExp_stronglyMeasurable_simpleFunc_bilin [CompleteSpace E] (hm : m <= m
Ω) (f : @SimpleFunc Ω m F) {g : Ω -> E} (hg : Integrable g μ) : μ[fun ω => B (f 
ω) (g ω) | m] =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω)
参数：hm : m <= mΩ；f : @SimpleFunc Ω m F；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_indicator`：condExp_indicator (hf_int : Integrable 
f μ) (hs : MeasurableSet[m] s) : μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m
])
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `condExp_bilin_of_stronglyMeasurable_left`.
-/
theorem condExp_stronglyMeasurable_simpleFunc_bilin [CompleteSpace E]
    (hm : m ≤ mΩ) (f : @SimpleFunc Ω m F) {g : Ω → E} (hg : Integrable g μ) :
    μ[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ] fun ω ↦ B (f ω) (μ[g | m] ω) := by
  have : ∀ (s c) (f : Ω → E),
      (fun ω ↦ B (Set.indicator s (Function.const Ω c) ω) (f ω)) =
        s.indicator (fun ω ↦ B c (f ω)) := by
    intro s c f
    ext ω
    by_cases hω : ω ∈ s <;> simp [hω]
  apply @SimpleFunc.induction _ _ m _ (fun f ↦ _)
    (fun c s hs ↦ ?_) (fun g₁ g₂ _ h_eq₁ h_eq₂ ↦ ?_) f
  · simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    rw [this, this]
    refine (condExp_indicator ((B c).integrable_comp hg) hs).trans ?_
    filter_upwards [(B c).comp_condExp_comm hg (m := m)] with ω hω
    simp only [Function.comp_apply] at hω
    simp only [Set.indicator, hω, Function.comp_def]
  · have h_add := @SimpleFunc.coe_add _ _ m _ g₁ g₂
    calc
      μ[fun ω ↦ B (g₁ ω + g₂ ω) (g ω) | m] =ᵐ[μ]
          μ[fun ω ↦ B (g₁ ω) (g ω) | m] + μ[fun ω ↦ B (g₂ ω) (g ω) | m] := by
        simp_rw [B.map_add]
        obtain ⟨C₁, hC₁⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ g₁
        obtain ⟨C₂, hC₂⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ g₂
        exact condExp_add
          (B.integrable_of_bilin_of_bdd_left C₁ (g₁.stronglyMeasurable.mono hm).aestronglyMeasurable
            (ae_of_all _ hC₁) hg)
          (B.integrable_of_bilin_of_bdd_left C₂ (g₂.stronglyMeasurable.mono hm).aestronglyMeasurable
            (ae_of_all _ hC₂) hg) m
      _ =ᵐ[μ] fun ω ↦ B (g₁ ω) (μ[g | m] ω) + B (g₂ ω) (μ[g | m] ω) := EventuallyEq.add h_eq₁ h_eq₂
      _ =ᵐ[μ] fun ω ↦ B ((g₁ + g₂) ω) (μ[g | m] ω) := by simp
/-
**MeasureTheory.condExp_stronglyMeasurable_bilin_of_bound** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：condExp_stronglyMeasurable_bilin_of_bound [CompleteSpace E] (hm : m <= mΩ)
 [IsFiniteMeasure μ] {f : Ω -> F} {g : Ω -> E} (hf : StronglyMeasurable[m] f) (h
g : Integrable g μ) (c : Real) (hf_bound : forallᵐ ω ∂μ, ‖f ω‖ <= c) : μ[fun ω =
> B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω)
参数：hm : m <= mΩ；hf : StronglyMeasurable[m] f；hg : Integrable g μ；c : Real；hf_bou
nd : forallᵐ ω ∂μ, ‖f ω‖ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.tendsto_approxBounded_ae`：tendsto_appro
xBounded_ae {β} {f : α -> β} [NormedAddCommGroup β] [NormedSpace Real β] {m m0 :
 MeasurableSpace α} {μ : Measure α} (hf : Stron…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_neBot`：ae_neBot : (ae μ).NeBot ↔ μ != 0
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.StronglyMeasurable.norm_approxBounded_le`：norm_approxBound
ed_le {β} {f : α -> β} [SeminormedAddCommGroup β] [NormedSpace Real β] {m : Meas
urableSpace α} {c : Real} (hf : StronglyMeas…
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `MeasureTheory.StronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : 
TopologicalSpace γ] {f : α → …
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
（共 55 条，此处仅展示前 30 条）
-/
theorem condExp_stronglyMeasurable_bilin_of_bound [CompleteSpace E]
    (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f : Ω → F} {g : Ω → E} (hf : StronglyMeasurable[m] f)
    (hg : Integrable g μ) (c : ℝ) (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c) :
    μ[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ] fun ω ↦ B (f ω) (μ[g | m] ω) := by
  let fs := hf.approxBounded c
  have hfs_tendsto : ∀ᵐ ω ∂μ, Tendsto (fs · ω) atTop (𝓝 (f ω)) :=
    hf.tendsto_approxBounded_ae hf_bound
  by_cases hμ : μ = 0
  · simp only [hμ, ae_zero]; norm_cast
  have : (ae μ).NeBot := ae_neBot.2 hμ
  have hc : 0 ≤ c := by
    rcases hf_bound.exists with ⟨_, h⟩
    exact (norm_nonneg _).trans h
  have hfs_bound : ∀ n ω, ‖fs n ω‖ ≤ c := hf.norm_approxBounded_le hc
  have : μ[fun ω ↦ B (f ω) (μ[g | m] ω) | m] = fun ω ↦ B (f ω) (μ[g | m] ω) := by
    refine condExp_of_stronglyMeasurable hm ?_ ?_
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E ↦ B z.1 z.2)) (by fun_prop)
        (hf.prodMk stronglyMeasurable_condExp)
    · exact B.integrable_of_bilin_of_bdd_left c (hf.mono hm).aestronglyMeasurable hf_bound
        integrable_condExp
  rw [← this]
  refine tendsto_condExp_unique (fun n ω ↦ B (fs n ω) (g ω))
    (fun n ω ↦ B (fs n ω) (μ[g | m] ω)) (fun ω ↦ B (f ω) (g ω))
    (fun ω ↦ B (f ω) (μ[g | m] ω)) ?_ ?_ ?_ ?_ (‖B‖ * c * ‖g ·‖) ?_ (‖B‖ * c * ‖(μ[g | m]) ·‖)
    ?_ ?_ ?_ ?_
  · exact fun n ↦ B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n) hg
  · exact fun n ↦ B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x ↦ B x (g ω))).tendsto (f ω)).comp hω
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x ↦ B x (μ[g | m] ω))).tendsto (f ω)).comp hω
  · exact hg.norm.const_mul _
  · fun_prop
  · refine fun n ↦ Eventually.of_forall fun _ ↦ ?_
    grw [B.le_opNorm₂, hfs_bound]
  · refine fun n ↦ Eventually.of_forall fun _ ↦ ?_
    grw [B.le_opNorm₂, hfs_bound]
  · intro n
    refine (condExp_stronglyMeasurable_simpleFunc_bilin B hm _ hg).trans ?_
    nth_rw 2 [condExp_of_stronglyMeasurable hm]
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E ↦ B z.1 z.2)) (by fun_prop)
        ((fs n).stronglyMeasurable.prodMk stronglyMeasurable_condExp)
    exact B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp
/-
**MeasureTheory.condExp_aestronglyMeasurable_bilin_of_bound** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：condExp_aestronglyMeasurable_bilin_of_bound [CompleteSpace E] (hm : m <= m
Ω) [IsFiniteMeasure μ] {f : Ω -> F} {g : Ω -> E} (hf : AEStronglyMeasurable[m] f
 μ) (hg : Integrable g μ) (c : Real) (hf_bound : forallᵐ ω ∂μ, ‖f ω‖ <= c) : μ[f
un ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω)
参数：hm : m <= mΩ；hf : AEStronglyMeasurable[m] f μ；hg : Integrable g μ；c : Real；hf
_bound : forallᵐ ω ∂μ, ‖f ω‖ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_stronglyMeasurable_bilin_of_bound`：condExp_strongl
yMeasurable_bilin_of_bound [CompleteSpace E] (hm : m <= mΩ) [IsFiniteMeasure μ] 
{f : Ω -> F} {g : Ω -> E} (hf : StronglyMeasu…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem condExp_aestronglyMeasurable_bilin_of_bound [CompleteSpace E]
    (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f : Ω → F} {g : Ω → E} (hf : AEStronglyMeasurable[m] f μ)
    (hg : Integrable g μ) (c : ℝ) (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c) :
    μ[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ] fun ω ↦ B (f ω) (μ[g | m] ω) := calc
  μ[fun ω ↦ B (f ω) (g ω) | m]
  _ =ᵐ[μ] μ[fun ω ↦ B (hf.mk f ω) (g ω) | m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun ω ↦ B (hf.mk f ω) (μ[g | m] ω) := by
    refine condExp_stronglyMeasurable_bilin_of_bound B hm hf.stronglyMeasurable_mk
      hg c ?_
    filter_upwards [hf_bound, hf.ae_eq_mk] with ω hω1 hω2
    rwa [← hω2]
  _ =ᵐ[μ] fun ω ↦ B (f ω) (μ[g | m] ω) := by
    filter_upwards [hf.ae_eq_mk] with ω hω using by rw [hω]

/-- Pull-out property of the conditional expectation. -/
/-
**MeasureTheory.condExp_bilin_of_stronglyMeasurable_left** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：condExp_bilin_of_stronglyMeasurable_left [CompleteSpace E] {f : Ω -> F} {g
 : Ω -> E} (hf : StronglyMeasurable[m] f) (hfg : Integrable (fun ω => B (f ω) (g
 ω)) μ) (hg : Integrable g μ) : μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B (
f ω) (μ[g | m] ω)
参数：hf : StronglyMeasurable[m] f；hfg : Integrable (fun ω => B (f ω) (g ω)) μ；hg :
 Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.exists_spanning_measurableSet_norm_le`：
exists_spanning_measurableSet_norm_le [SeminormedAddCommGroup β] {m m0 : Measura
bleSpace α} (hm : m <= m0) (hf : StronglyMeasurable[m] f) (μ…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
· 使用定理 `MeasureTheory.condExp_stronglyMeasurable_bilin_of_bound`：condExp_strongl
yMeasurable_bilin_of_bound [CompleteSpace E] (hm : m <= mΩ) [IsFiniteMeasure μ] 
{f : Ω -> F} {g : Ω -> E} (hf : StronglyMeasu…
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `indicator_ae_eq_restrict`：indicator_ae_eq_restrict (hs : MeasurableSet s
) : indicator s f =ᵐ[μ.restrict s] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_restrict_ae_eq_restrict`：condExp_restrict_ae_eq_re
strict (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs_m : MeasurableSet[m] s) (hf_
int : Integrable f μ) : (μ.restrict…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Pull-out property of the conditional expectation.
-/
theorem condExp_bilin_of_stronglyMeasurable_left [CompleteSpace E] {f : Ω → F} {g : Ω → E}
    (hf : StronglyMeasurable[m] f) (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ)
    (hg : Integrable g μ) :
    μ[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ] fun ω ↦ B (f ω) (μ[g | m] ω) := by
  by_cases hm : m ≤ mΩ; swap; · exact ae_of_all _ <| by simp [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · exact ae_of_all _ <| by simp [condExp_of_not_sigmaFinite hm hμm]
  obtain ⟨sets, sets_prop, h_univ⟩ := hf.exists_spanning_measurableSet_norm_le hm μ
  simp_rw [forall_and] at sets_prop
  obtain ⟨h_meas, h_finite, h_norm⟩ := sets_prop
  suffices ∀ n, ∀ᵐ ω ∂μ, ω ∈ sets n → (μ[fun ω ↦ B (f ω) (g ω) | m]) ω = B (f ω) (μ[g | m] ω) by
    rw [← ae_all_iff] at this
    filter_upwards [this] with ω hω
    obtain ⟨i, hi⟩ : ∃ i, ω ∈ sets i := by
      have h_mem : ω ∈ ⋃ i, sets i := by rw [h_univ]; exact Set.mem_univ _
      simpa using h_mem
    exact hω i hi
  refine fun n ↦ ae_imp_of_ae_restrict ?_
  suffices (μ.restrict (sets n))[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ.restrict (sets n)]
      fun ω ↦ B (f ω) ((μ.restrict (sets n))[g | m] ω) by
    refine (condExp_restrict_ae_eq_restrict hm (h_meas n) hfg).symm.trans ?_
    filter_upwards [this, (condExp_restrict_ae_eq_restrict hm (h_meas n) hg)] with ω hω1 hω2
    rw [hω1, hω2]
  suffices (μ.restrict (sets n))[fun ω ↦ B ((sets n).indicator f ω) (g ω) | m]
      =ᵐ[μ.restrict (sets n)] fun ω ↦ B ((sets n).indicator f ω) ((μ.restrict (sets n))[g | m] ω) by
    refine EventuallyEq.trans (condExp_congr_ae ?_) (this.trans ?_)
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with ω hω
      rw [hω]
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with ω hω
      rw [hω]
  have : IsFiniteMeasure (μ.restrict (sets n)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact h_finite n
  refine condExp_stronglyMeasurable_bilin_of_bound B hm (hf.indicator (h_meas n))
    hg.integrableOn n ?_
  filter_upwards with ω
  by_cases hωs : ω ∈ sets n <;> simp [hωs, h_norm]

/-- Pull-out property of the conditional expectation. -/
/-
**MeasureTheory.condExp_bilin_of_stronglyMeasurable_right** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：condExp_bilin_of_stronglyMeasurable_right [CompleteSpace F] {f : Ω -> F} {
g : Ω -> E} (hg : StronglyMeasurable[m] g) (hfg : Integrable (fun ω => B (f ω) (
g ω)) μ) (hf : Integrable f μ) : μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B 
(μ[f | m] ω) (g ω)
参数：hg : StronglyMeasurable[m] g；hfg : Integrable (fun ω => B (f ω) (g ω)) μ；hf :
 Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_bilin_of_stronglyMeasurable_left`：condExp_bilin_of
_stronglyMeasurable_left [CompleteSpace E] {f : Ω -> F} {g : Ω -> E} (hf : Stron
glyMeasurable[m] f) (hfg : Integrable (fun ω…

--- 原说明 ---
Pull-out property of the conditional expectation.
-/
theorem condExp_bilin_of_stronglyMeasurable_right [CompleteSpace F] {f : Ω → F} {g : Ω → E}
    (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ) (hf : Integrable f μ) :
    μ[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ] fun ω ↦ B (μ[f | m] ω) (g ω) := by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_stronglyMeasurable_left B.flip hg hfg hf

/-- Pull-out property of the conditional expectation. -/
/-
**MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：condExp_bilin_of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω -> F} 
{g : Ω -> E} (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (fun ω => B (f
 ω) (g ω)) μ) (hg : Integrable g μ) : μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω 
=> B (f ω) (μ[g | m] ω)
参数：hf : AEStronglyMeasurable[m] f μ；hfg : Integrable (fun ω => B (f ω) (g ω)) μ；
hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_bilin_of_stronglyMeasurable_left`：condExp_bilin_of
_stronglyMeasurable_left [CompleteSpace E] {f : Ω -> F} {g : Ω -> E} (hf : Stron
glyMeasurable[m] f) (hfg : Integrable (fun ω…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ

--- 原说明 ---
Pull-out property of the conditional expectation.
-/
theorem condExp_bilin_of_aestronglyMeasurable_left [CompleteSpace E]
    {f : Ω → F} {g : Ω → E} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ) (hg : Integrable g μ) :
    μ[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ] fun ω ↦ B (f ω) (μ[g | m] ω) := calc
  μ[fun ω ↦ B (f ω) (g ω) | m]
  _ =ᵐ[μ] μ[fun ω ↦ B (hf.mk f ω) (g ω) | m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun ω ↦ B (hf.mk f ω) (μ[g | m] ω) := by
    refine condExp_bilin_of_stronglyMeasurable_left B hf.stronglyMeasurable_mk
      ((integrable_congr ?_).mp hfg) hg
    filter_upwards [hf.ae_eq_mk] with ω hω using by rw [hω]
  _ =ᵐ[μ] fun ω ↦ B (f ω) (μ[g | m] ω) := by
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]

/-- Pull-out property of the conditional expectation. -/
/-
**MeasureTheory.condExp_bilin_of_aestronglyMeasurable_right** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：condExp_bilin_of_aestronglyMeasurable_right [CompleteSpace F] {f : Ω -> F}
 {g : Ω -> E} (hg : AEStronglyMeasurable[m] g μ) (hfg : Integrable (fun ω => B (
f ω) (g ω)) μ) (hf : Integrable f μ) : μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω
 => B (μ[f | m] ω) (g ω)
参数：hg : AEStronglyMeasurable[m] g μ；hfg : Integrable (fun ω => B (f ω) (g ω)) μ；
hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left`：condExp_bilin_
of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω -> F} {g : Ω -> E} (hf : A
EStronglyMeasurable[m] f μ) (hfg : Integrable …

--- 原说明 ---
Pull-out property of the conditional expectation.
-/
theorem condExp_bilin_of_aestronglyMeasurable_right [CompleteSpace F] {f : Ω → F} {g : Ω → E}
    (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ) (hf : Integrable f μ) :
    μ[fun ω ↦ B (f ω) (g ω) | m] =ᵐ[μ] fun ω ↦ B (μ[f | m] ω) (g ω) := by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_aestronglyMeasurable_left B.flip hg hfg hf

/-- Pull-out property of the conditional expectation. -/
/-
**MeasureTheory.condExp_smul_of_aestronglyMeasurable_left** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：condExp_smul_of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω -> Real
} {g : Ω -> E} (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (f • g) μ) (
hg : Integrable g μ) : μ[f • g | m] =ᵐ[μ] f • μ[g | m]
参数：hf : AEStronglyMeasurable[m] f μ；hfg : Integrable (f • g) μ；hg : Integrable g
 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left`：condExp_bilin_
of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω -> F} {g : Ω -> E} (hf : A
EStronglyMeasurable[m] f μ) (hfg : Integrable …

--- 原说明 ---
Pull-out property of the conditional expectation.
-/
theorem condExp_smul_of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω → ℝ} {g : Ω → E}
    (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (f • g) μ) (hg : Integrable g μ) :
    μ[f • g | m] =ᵐ[μ] f • μ[g | m] :=
  condExp_bilin_of_aestronglyMeasurable_left (.lsmul ℝ ℝ) hf hfg hg

/-- Pull-out property of the conditional expectation. -/
/-
**MeasureTheory.condExp_smul_of_aestronglyMeasurable_right** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：condExp_smul_of_aestronglyMeasurable_right [CompleteSpace E] {f : Ω -> Rea
l} {g : Ω -> E} (hf : Integrable f μ) (hfg : Integrable (f • g) μ) (hg : AEStron
glyMeasurable[m] g μ) : μ[f • g | m] =ᵐ[μ] μ[f | m] • g
参数：hf : Integrable f μ；hfg : Integrable (f • g) μ；hg : AEStronglyMeasurable[m] g
 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left`：condExp_bilin_
of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω -> F} {g : Ω -> E} (hf : A
EStronglyMeasurable[m] f μ) (hfg : Integrable …

--- 原说明 ---
Pull-out property of the conditional expectation.
-/
theorem condExp_smul_of_aestronglyMeasurable_right [CompleteSpace E] {f : Ω → ℝ} {g : Ω → E}
    (hf : Integrable f μ) (hfg : Integrable (f • g) μ) (hg : AEStronglyMeasurable[m] g μ) :
    μ[f • g | m] =ᵐ[μ] μ[f | m] • g :=
  condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.lsmul ℝ ℝ).flip hg hfg hf

/-- Pull-out property of the conditional expectation. -/
/-
**MeasureTheory.condExp_mul_of_aestronglyMeasurable_left** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：condExp_mul_of_aestronglyMeasurable_left {f g : Ω -> Real} (hf : AEStrongl
yMeasurable[m] f μ) (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g
 | m] =ᵐ[μ] f * μ[g | m]
参数：hf : AEStronglyMeasurable[m] f μ；hfg : Integrable (f * g) μ；hg : Integrable g
 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left`：condExp_bilin_
of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω -> F} {g : Ω -> E} (hf : A
EStronglyMeasurable[m] f μ) (hfg : Integrable …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
Pull-out property of the conditional expectation.
-/
theorem condExp_mul_of_aestronglyMeasurable_left {f g : Ω → ℝ} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
  condExp_bilin_of_aestronglyMeasurable_left (.mul ℝ ℝ) hf hfg hg

/-- Pull-out property of the conditional expectation. -/
/-
**MeasureTheory.condExp_mul_of_aestronglyMeasurable_right** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：condExp_mul_of_aestronglyMeasurable_right {f g : Ω -> Real} (hg : AEStrong
lyMeasurable[m] g μ) (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * 
g | m] =ᵐ[μ] μ[f | m] * g
参数：hg : AEStronglyMeasurable[m] g μ；hfg : Integrable (f * g) μ；hf : Integrable f
 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_bilin_of_aestronglyMeasurable_right`：condExp_bilin
_of_aestronglyMeasurable_right [CompleteSpace F] {f : Ω -> F} {g : Ω -> E} (hg :
 AEStronglyMeasurable[m] g μ) (hfg : Integrable…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
Pull-out property of the conditional expectation.
-/
theorem condExp_mul_of_aestronglyMeasurable_right {f g : Ω → ℝ} (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g :=
  condExp_bilin_of_aestronglyMeasurable_right (.mul ℝ ℝ) hg hfg hf

/-- Pull-out property of the conditional expectation. -/
/-
**MeasureTheory.condExp_mul_of_stronglyMeasurable_left** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：condExp_mul_of_stronglyMeasurable_left {f g : Ω -> Real} (hf : StronglyMea
surable[m] f) (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g | m] 
=ᵐ[μ] f * μ[g | m]
参数：hf : StronglyMeasurable[m] f；hfg : Integrable (f * g) μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left`：condExp_bilin_
of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω -> F} {g : Ω -> E} (hf : A
EStronglyMeasurable[m] f μ) (hfg : Integrable …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…

--- 原说明 ---
Pull-out property of the conditional expectation.
-/
theorem condExp_mul_of_stronglyMeasurable_left {f g : Ω → ℝ} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
  condExp_bilin_of_aestronglyMeasurable_left (.mul ℝ ℝ)
    hf.aestronglyMeasurable hfg hg

/-- Pull-out property of the conditional expectation. -/
/-
**MeasureTheory.condExp_mul_of_stronglyMeasurable_right** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：condExp_mul_of_stronglyMeasurable_right {f g : Ω -> Real} (hg : StronglyMe
asurable[m] g) (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m]
 =ᵐ[μ] μ[f | m] * g
参数：hg : StronglyMeasurable[m] g；hfg : Integrable (f * g) μ；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_bilin_of_aestronglyMeasurable_right`：condExp_bilin
_of_aestronglyMeasurable_right [CompleteSpace F] {f : Ω -> F} {g : Ω -> E} (hg :
 AEStronglyMeasurable[m] g μ) (hfg : Integrable…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…

--- 原说明 ---
Pull-out property of the conditional expectation.
-/
lemma condExp_mul_of_stronglyMeasurable_right {f g : Ω → ℝ} (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g :=
  condExp_bilin_of_aestronglyMeasurable_right (.mul ℝ ℝ)
    hg.aestronglyMeasurable hfg hf
/-
**MeasureTheory.condExp_stronglyMeasurable_simpleFunc_mul** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：condExp_stronglyMeasurable_simpleFunc_mul (hm : m <= mΩ) (f : @SimpleFunc 
Ω m Real) {g : Ω -> Real} (hg : Integrable g μ) : μ[(f * g : Ω -> Real) | m] =ᵐ[
μ] f * μ[g | m]
参数：hm : m <= mΩ；f : @SimpleFunc Ω m Real；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condExp_stronglyMeasurable_simpleFunc_bilin`：condExp_stron
glyMeasurable_simpleFunc_bilin [CompleteSpace E] (hm : m <= mΩ) (f : @SimpleFunc
 Ω m F) {g : Ω -> E} (hg : Integrable g μ) : μ[…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem condExp_stronglyMeasurable_simpleFunc_mul (hm : m ≤ mΩ) (f : @SimpleFunc Ω m ℝ) {g : Ω → ℝ}
    (hg : Integrable g μ) : μ[(f * g : Ω → ℝ) | m] =ᵐ[μ] f * μ[g | m] :=
  condExp_stronglyMeasurable_simpleFunc_bilin (.mul ℝ ℝ) hm f hg
/-
**MeasureTheory.condExp_stronglyMeasurable_mul_of_bound** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：condExp_stronglyMeasurable_mul_of_bound (hm : m <= mΩ) [IsFiniteMeasure μ]
 {f g : Ω -> Real} (hf : StronglyMeasurable[m] f) (hg : Integrable g μ) (c : Rea
l) (hf_bound : forallᵐ ω ∂μ, ‖f ω‖ <= c) : μ[f * g | m] =ᵐ[μ] f * μ[g | m]
参数：hm : m <= mΩ；hf : StronglyMeasurable[m] f；hg : Integrable g μ；c : Real；hf_bou
nd : forallᵐ ω ∂μ, ‖f ω‖ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_stronglyMeasurable_bilin_of_bound`：condExp_strongl
yMeasurable_bilin_of_bound [CompleteSpace E] (hm : m <= mΩ) [IsFiniteMeasure μ] 
{f : Ω -> F} {g : Ω -> E} (hf : StronglyMeasu…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem condExp_stronglyMeasurable_mul_of_bound (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : StronglyMeasurable[m] f) (hg : Integrable g μ) (c : ℝ) (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c) :
    μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
  condExp_stronglyMeasurable_bilin_of_bound (.mul ℝ ℝ) hm hf hg c hf_bound
/-
**MeasureTheory.condExp_stronglyMeasurable_mul_of_bound** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：condExp_stronglyMeasurable_mul_of_bound (hm : m <= mΩ) [IsFiniteMeasure μ]
 {f g : Ω -> Real} (hf : StronglyMeasurable[m] f) (hg : Integrable g μ) (c : Rea
l) (hf_bound : forallᵐ ω ∂μ, ‖f ω‖ <= c) : μ[f * g | m] =ᵐ[μ] f * μ[g | m]
参数：hm : m <= mΩ；hf : StronglyMeasurable[m] f；hg : Integrable g μ；c : Real；hf_bou
nd : forallᵐ ω ∂μ, ‖f ω‖ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_stronglyMeasurable_bilin_of_bound`：condExp_strongl
yMeasurable_bilin_of_bound [CompleteSpace E] (hm : m <= mΩ) [IsFiniteMeasure μ] 
{f : Ω -> F} {g : Ω -> E} (hf : StronglyMeasu…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem condExp_stronglyMeasurable_mul_of_bound₀ (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable[m] f μ) (hg : Integrable g μ) (c : ℝ)
    (hf_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c) : μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
  condExp_aestronglyMeasurable_bilin_of_bound (.mul ℝ ℝ) hm hf hg c hf_bound

end MeasureTheory

