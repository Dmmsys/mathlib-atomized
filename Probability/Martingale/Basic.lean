/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Process.Predictable
public import Mathlib.Probability.Process.Stopping

/-!
# Martingales

A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ i] =ᵐ[μ] f i`. On the other hand, `f : ι → Ω → E` is said to be a supermartingale
with respect to the filtration `ℱ` if `f i` is integrable, `f` is strongly adapted with respect to
`ℱ` and for all `i ≤ j`, `μ[f j | ℱ i] ≤ᵐ[μ] f i`. Finally, `f : ι → Ω → E` is said to be a
submartingale with respect to the filtration `ℱ` if `f i` is integrable, `f` is strongly adapted
with respect to `ℱ` and for all `i ≤ j`, `f i ≤ᵐ[μ] μ[f j | ℱ i]`.

### Definitions

* `MeasureTheory.Martingale f ℱ μ`: `f` is a martingale with respect to filtration `ℱ` and
  measure `μ`.
* `MeasureTheory.Supermartingale f ℱ μ`: `f` is a supermartingale with respect to
  filtration `ℱ` and measure `μ`.
* `MeasureTheory.Submartingale f ℱ μ`: `f` is a submartingale with respect to filtration `ℱ` and
  measure `μ`.

### Results

* `MeasureTheory.martingale_condExp f ℱ μ`: the sequence `fun i => μ[f | ℱ i]` is a
  martingale with respect to `ℱ` and `μ`.

-/

@[expose] public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E ι : Type*} [Preorder ι] {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ι → Ω → E} {ℱ : Filtration ι m0}

/-- A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if `f`
is strongly adapted with respect to `ℱ` and for all `i ≤ j`, `μ[f j | ℱ i] =ᵐ[μ] f i`. -/
/-
**MeasureTheory.Martingale** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：Martingale (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop
参数：f : ι -> Ω -> E；ℱ : Filtration ι m0；μ : Measure Ω。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A family of functions `f : ι → Ω → E` is a martingale with respect to a filtrati
on `ℱ` if `f`
is strongly adapted with respect to `ℱ` and for all `i ≤ j`, `μ[f j | ℱ i] =ᵐ[μ]
 f i`.
-/
def Martingale (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ ∀ i j, i ≤ j → μ[f j | ℱ i] =ᵐ[μ] f i

/-- A family of integrable functions `f : ι → Ω → E` is a supermartingale with respect to a
filtration `ℱ` if `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] ≤ᵐ[μ] f i`. -/
/-
**MeasureTheory.Supermartingale** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：Supermartingale [LE E] (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measur
e Ω) : Prop
参数：f : ι -> Ω -> E；ℱ : Filtration ι m0；μ : Measure Ω。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A family of integrable functions `f : ι → Ω → E` is a supermartingale with respe
ct to a
filtration `ℱ` if `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j
`,
`μ[f j | ℱ.le i] ≤ᵐ[μ] f i`.
-/
def Supermartingale [LE E] (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ (∀ i j, i ≤ j → μ[f j | ℱ i] ≤ᵐ[μ] f i) ∧ ∀ i, Integrable (f i) μ

/-- A family of integrable functions `f : ι → Ω → E` is a submartingale with respect to a
filtration `ℱ` if `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j`,
`f i ≤ᵐ[μ] μ[f j | ℱ.le i]`. -/
/-
**MeasureTheory.Submartingale** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：Submartingale [LE E] (f : ι -> Ω -> E) (ℱ : Filtration ι m0) (μ : Measure 
Ω) : Prop
参数：f : ι -> Ω -> E；ℱ : Filtration ι m0；μ : Measure Ω。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A family of integrable functions `f : ι → Ω → E` is a submartingale with respect
 to a
filtration `ℱ` if `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j
`,
`f i ≤ᵐ[μ] μ[f j | ℱ.le i]`.
-/
def Submartingale [LE E] (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ (∀ i j, i ≤ j → f i ≤ᵐ[μ] μ[f j | ℱ i]) ∧ ∀ i, Integrable (f i) μ
/-
**MeasureTheory.martingale_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：martingale_const (ℱ : Filtration ι m0) (μ : Measure Ω) [IsFiniteMeasure μ]
 (x : E) : Martingale (fun _ _ => x) ℱ μ
参数：ℱ : Filtration ι m0；μ : Measure Ω；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.stronglyAdapted_const`：stronglyAdapted_const {β : Type*} [
TopologicalSpace β] (f : Filtration ι m) (x : β) : StronglyAdapted f fun _ _ => 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_const`：condExp_const (hm : m <= m₀) (c : E) [IsFin
iteMeasure μ] : μ[fun _ : α => c | m] = fun _ => c
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem martingale_const (ℱ : Filtration ι m0) (μ : Measure Ω) [IsFiniteMeasure μ] (x : E) :
    Martingale (fun _ _ => x) ℱ μ :=
  ⟨stronglyAdapted_const ℱ _, fun i j _ => by rw [condExp_const (ℱ.le _)]⟩
/-
**MeasureTheory.martingale_const_fun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：martingale_const_fun [OrderBot ι] (ℱ : Filtration ι m0) (μ : Measure Ω) [S
igmaFiniteFiltration μ ℱ] {f : Ω -> E} (hf : StronglyMeasurable[ℱ ⊥] f) (hfint :
 Integrable f μ) : Martingale (fun _ => f) ℱ μ
参数：ℱ : Filtration ι m0；μ : Measure Ω；hf : StronglyMeasurable[ℱ ⊥] f；hfint : Inte
grable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem martingale_const_fun [OrderBot ι] (ℱ : Filtration ι m0) (μ : Measure Ω)
    [SigmaFiniteFiltration μ ℱ]
    {f : Ω → E} (hf : StronglyMeasurable[ℱ ⊥] f) (hfint : Integrable f μ) :
    Martingale (fun _ => f) ℱ μ := by
  refine ⟨fun i => hf.mono <| ℱ.mono bot_le, fun i j _ => ?_⟩
  rw [condExp_of_stronglyMeasurable (ℱ.le _) (hf.mono <| ℱ.mono bot_le) hfint]

variable (E) in
/-
**MeasureTheory.martingale_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：martingale_zero (ℱ : Filtration ι m0) (μ : Measure Ω) : Martingale (0 : ι 
-> Ω -> E) ℱ μ
参数：ℱ : Filtration ι m0；μ : Measure Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.stronglyAdapted_zero`：stronglyAdapted_zero (β : Type*) [To
pologicalSpace β] [Zero β] (f : Filtration ι m) : StronglyAdapted f (0 : ι -> Ω 
-> β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_zero`：condExp_zero : μ[(0 : α -> E) | m] = 0
-/
theorem martingale_zero (ℱ : Filtration ι m0) (μ : Measure Ω) : Martingale (0 : ι → Ω → E) ℱ μ :=
  ⟨stronglyAdapted_zero E ℱ, fun i j _ => by simp⟩

namespace Martingale

/-
**MeasureTheory.Martingale.stronglyAdapted** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Martingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E] {f : ι → Ω → E}   {ℱ : MeasureTheory.Filtration ι m
0}, MeasureTheory.Martingale f ℱ μ → MeasureTheory.StronglyAdapted ℱ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
protected theorem stronglyAdapted (hf : Martingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1
/-
**MeasureTheory.Martingale.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Martingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E] {f : ι → Ω → E}   {ℱ : MeasureTheory.Filtration ι m
0},   MeasureTheory.Martingale f ℱ μ → ∀ (i : ι), MeasureTheory.StronglyMeasurab
le (f i)
参数：i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Martingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type u_2
} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheo
ry.Measure Ω} [inst_1 : Normed…
-/
protected theorem stronglyMeasurable (hf : Martingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i
/-
**MeasureTheory.Martingale.condExp_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Martingale`。
形式化陈述：condExp_ae_eq (hf : Martingale f ℱ μ) {i j : ι} (hij : i <= j) : μ[f j | ℱ
 i] =ᵐ[μ] f i
参数：hf : Martingale f ℱ μ；hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem condExp_ae_eq (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j) : μ[f j | ℱ i] =ᵐ[μ] f i :=
  hf.2 i j hij

variable [CompleteSpace E]
/-
**MeasureTheory.Martingale.integrable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
artingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E] {f : ι → Ω → E}   {ℱ : MeasureTheory.Filtration ι m
0} [CompleteSpace E],   MeasureTheory.Martingale f ℱ μ → ∀ (i : ι), MeasureTheor
y.Integrable (f i) μ
参数：i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.Martingale.condExp_ae_eq`：condExp_ae_eq (hf : Martingale f
 ℱ μ) {i j : ι} (hij : i <= j) : μ[f j | ℱ i] =ᵐ[μ] f i
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
protected theorem integrable (hf : Martingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  integrable_condExp.congr (hf.condExp_ae_eq (le_refl i))
/-
**MeasureTheory.Martingale.setIntegral_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Martingale`。
形式化陈述：setIntegral_eq [SigmaFiniteFiltration μ ℱ] (hf : Martingale f ℱ μ) {i j : 
ι} (hij : i <= j) {s : Set Ω} (hs : MeasurableSet[ℱ i] s) : ∫ ω in s, f i ω ∂μ =
 ∫ ω in s, f j ω ∂μ
参数：hf : Martingale f ℱ μ；hij : i <= j；hs : MeasurableSet[ℱ i] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.Martingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} {ι 
: Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Me
asure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem setIntegral_eq [SigmaFiniteFiltration μ ℱ] (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    {s : Set Ω} (hs : MeasurableSet[ℱ i] s) : ∫ ω in s, f i ω ∂μ = ∫ ω in s, f j ω ∂μ := by
  rw [← setIntegral_condExp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_congr_ae (ℱ.le i s hs) ?_
  filter_upwards [hf.2 i j hij] with _ heq _ using heq.symm
/-
**MeasureTheory.Martingale.congr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Martin
gale`。
形式化陈述：congr (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ g) (h_eq : forall t,
 f t =ᵐ[μ] g t) : Martingale g ℱ μ
参数：hf : Martingale f ℱ μ；hg : StronglyAdapted ℱ g；h_eq : forall t, f t =ᵐ[μ] g t
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma congr (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ g) (h_eq : ∀ t, f t =ᵐ[μ] g t) :
    Martingale g ℱ μ := by
  refine ⟨hg, fun i j hij ↦ ?_⟩
  calc μ[g j | ℱ i] =ᵐ[μ] μ[f j | ℱ i] := (condExp_congr_ae (h_eq j)).symm
    _ =ᵐ[μ] g i := (hf.2 i j hij).trans (h_eq i)
/-
**MeasureTheory.Martingale.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Martinga
le`。
形式化陈述：add (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f + g) ℱ
 μ
参数：hf : Martingale f ℱ μ；hg : Martingale g ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyAdapted.add`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Martingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type u_2
} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheo
ry.Measure Ω} [inst_1 : Normed…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_add`：condExp_add (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
· 使用定理 `MeasureTheory.Martingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} {ι 
: Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Me
asure Ω} [inst_1 : Normed…
· 使用定理 `Filter.EventuallyEq.add`：∀ {α : Type u} {β : Type v} [inst : Add β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f + f' =ᶠ[l] g + g'
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem add (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f + g) ℱ μ := by
  refine ⟨hf.stronglyAdapted.add hg.stronglyAdapted, fun i j hij => ?_⟩
  exact (condExp_add (hf.integrable j) (hg.integrable j) _).trans
    ((hf.2 i j hij).add (hg.2 i j hij))
/-
**MeasureTheory.Martingale.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Martinga
le`。
形式化陈述：neg (hf : Martingale f ℱ μ) : Martingale (-f) ℱ μ
参数：hf : Martingale f ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyAdapted.neg`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Martingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type u_2
} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheo
ry.Measure Ω} [inst_1 : Normed…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_neg`：condExp_neg (f : α -> E) (m : MeasurableSpace
 α) : μ[-f | m] =ᵐ[μ] -μ[f | m]
· 使用定理 `Filter.EventuallyEq.neg`：∀ {α : Type u} {β : Type v} [inst : Neg β] {f g
 : α → β} {l : Filter α}, f =ᶠ[l] g → -f =ᶠ[l] -g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem neg (hf : Martingale f ℱ μ) : Martingale (-f) ℱ μ :=
  ⟨hf.stronglyAdapted.neg, fun i j hij => (condExp_neg ..).trans (hf.2 i j hij).neg⟩
/-
**MeasureTheory.Martingale.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Martinga
le`。
形式化陈述：sub (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f - g) ℱ
 μ
参数：hf : Martingale f ℱ μ；hg : Martingale g ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.Martingale.add`：add (hf : Martingale f ℱ μ) (hg : Martinga
le g ℱ μ) : Martingale (f + g) ℱ μ
· 使用定理 `MeasureTheory.Martingale.neg`：neg (hf : Martingale f ℱ μ) : Martingale (
-f) ℱ μ
-/
theorem sub (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
/-
**MeasureTheory.Martingale.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Marting
ale`。
形式化陈述：smul (c : Real) (hf : Martingale f ℱ μ) : Martingale (c • f) ℱ μ
参数：c : Real；hf : Martingale f ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyAdapted.smul`：∀ {Ω : Type u_1} {ι : Type u_2} {m :
 MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β 
: ι → Type u_3} [inst_1 …
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Martingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type u_2
} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheo
ry.Measure Ω} [inst_1 : Normed…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_smul`：condExp_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : 
α -> E) (m : MeasurableSpace α) : μ[c • f | m] =ᵐ[μ] c • μ[f | m]
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul (c : ℝ) (hf : Martingale f ℱ μ) : Martingale (c • f) ℱ μ := by
  refine ⟨hf.stronglyAdapted.smul c, fun i j hij => ?_⟩
  refine (condExp_smul ..).trans ((hf.2 i j hij).mono fun x hx => ?_)
  simp only [Pi.smul_apply, hx]
/-
**MeasureTheory.Martingale.supermartingale** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Martingale`。
形式化陈述：supermartingale [Preorder E] (hf : Martingale f ℱ μ) : Supermartingale f ℱ
 μ
参数：hf : Martingale f ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Martingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} {ι 
: Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Me
asure Ω} [inst_1 : Normed…
-/
theorem supermartingale [Preorder E] (hf : Martingale f ℱ μ) : Supermartingale f ℱ μ :=
  ⟨hf.1, fun i j hij => (hf.2 i j hij).le, fun i => hf.integrable i⟩
/-
**MeasureTheory.Martingale.submartingale** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Martingale`。
形式化陈述：submartingale [Preorder E] (hf : Martingale f ℱ μ) : Submartingale f ℱ μ
参数：hf : Martingale f ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Martingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} {ι 
: Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Me
asure Ω} [inst_1 : Normed…
-/
theorem submartingale [Preorder E] (hf : Martingale f ℱ μ) : Submartingale f ℱ μ :=
  ⟨hf.1, fun i j hij => (hf.2 i j hij).symm.le, fun i => hf.integrable i⟩

end Martingale

/-
**MeasureTheory.martingale_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：martingale_iff [CompleteSpace E] [PartialOrder E] : Martingale f ℱ μ ↔ Sup
ermartingale f ℱ μ ∧ Submartingale f ℱ μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Martingale.supermartingale`：supermartingale [Preorder E] (
hf : Martingale f ℱ μ) : Supermartingale f ℱ μ
· 使用定理 `MeasureTheory.Martingale.submartingale`：submartingale [Preorder E] (hf :
 Martingale f ℱ μ) : Submartingale f ℱ μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem martingale_iff [CompleteSpace E] [PartialOrder E] :
    Martingale f ℱ μ ↔ Supermartingale f ℱ μ ∧ Submartingale f ℱ μ :=
  ⟨fun hf => ⟨hf.supermartingale, hf.submartingale⟩, fun ⟨hf₁, hf₂⟩ =>
    ⟨hf₁.1, fun i j hij => (hf₁.2.1 i j hij).antisymm (hf₂.2.1 i j hij)⟩⟩
/-
**MeasureTheory.martingale_condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：martingale_condExp [CompleteSpace E] (f : Ω -> E) (ℱ : Filtration ι m0) (μ
 : Measure Ω) [SigmaFiniteFiltration μ ℱ] : Martingale (fun i => μ[f | ℱ i]) ℱ μ
参数：f : Ω -> E；ℱ : Filtration ι m0；μ : Measure Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.condExp_condExp_of_le`：condExp_condExp_of_le {m₁ m₂ m₀ : M
easurableSpace α} {μ : Measure α} (hm₁₂ : m₁ <= m₂) (hm₂ : m₂ <= m₀) [SigmaFinit
e (μ.trim hm₂)] : μ[μ[f |…
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
-/
theorem martingale_condExp [CompleteSpace E] (f : Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω)
    [SigmaFiniteFiltration μ ℱ] : Martingale (fun i => μ[f | ℱ i]) ℱ μ :=
  ⟨fun _ => stronglyMeasurable_condExp, fun _ j hij => condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)⟩

namespace Supermartingale

/-
**MeasureTheory.Supermartingale.stronglyAdapted** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Supermartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E] {f : ι → Ω → E}   {ℱ : MeasureTheory.Filtration ι m
0} [inst_3 : LE E],   MeasureTheory.Supermartingale f ℱ μ → MeasureTheory.Strong
lyAdapted ℱ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
protected theorem stronglyAdapted [LE E] (hf : Supermartingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1
/-
**MeasureTheory.Supermartingale.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Supermartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E] {f : ι → Ω → E}   {ℱ : MeasureTheory.Filtration ι m
0} [inst_3 : LE E],   MeasureTheory.Supermartingale f ℱ μ → ∀ (i : ι), MeasureTh
eory.StronglyMeasurable (f i)
参数：i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Supermartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Typ
e u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : Measur
eTheory.Measure Ω} [inst_1 : Normed…
-/
protected theorem stronglyMeasurable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i
/-
**MeasureTheory.Supermartingale.integrable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Supermartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E] {f : ι → Ω → E}   {ℱ : MeasureTheory.Filtration ι m
0} [inst_3 : LE E],   MeasureTheory.Supermartingale f ℱ μ → ∀ (i : ι), MeasureTh
eory.Integrable (f i) μ
参数：i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
protected theorem integrable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i
/-
**MeasureTheory.Supermartingale.condExp_ae_le** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Supermartingale`。
形式化陈述：condExp_ae_le [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i <= j)
 : μ[f j | ℱ i] <=ᵐ[μ] f i
参数：hf : Supermartingale f ℱ μ；hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem condExp_ae_le [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    μ[f j | ℱ i] ≤ᵐ[μ] f i :=
  hf.2.1 i j hij

variable [CompleteSpace E]
/-
**MeasureTheory.Supermartingale.setIntegral_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Supermartingale`。
形式化陈述：setIntegral_le [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule Re
al E] [ClosedIciTopology E] [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω -> E} (hf : 
Supermartingale f ℱ μ) {i j : ι} (hij : i <= j) {s : Set Ω} (hs : MeasurableSet[
ℱ i] s) : ∫ ω in s, f j ω ∂μ <= ∫ ω in s, f i ω ∂μ
参数：hf : Supermartingale f ℱ μ；hij : i <= j；hs : MeasurableSet[ℱ i] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.Supermartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2
} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheo
ry.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.setIntegral_mono_ae`：setIntegral_mono_ae (h : f <=ᵐ[μ] g) 
: ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem setIntegral_le [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [ClosedIciTopology E] [SigmaFiniteFiltration μ ℱ] {f : ι → Ω → E} (hf : Supermartingale f ℱ μ)
    {i j : ι} (hij : i ≤ j) {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫ ω in s, f j ω ∂μ ≤ ∫ ω in s, f i ω ∂μ := by
  rw [← setIntegral_condExp (ℱ.le i) (hf.integrable j) hs]
  refine setIntegral_mono_ae integrable_condExp.integrableOn (hf.integrable i).integrableOn ?_
  filter_upwards [hf.2.1 i j hij] with _ heq using heq
/-
**MeasureTheory.Supermartingale.congr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.S
upermartingale`。
形式化陈述：congr [LE E] (hf : Supermartingale f ℱ μ) (hg : StronglyAdapted ℱ g) (h_eq
 : forall t, f t =ᵐ[μ] g t) : Supermartingale g ℱ μ
参数：hf : Supermartingale f ℱ μ；hg : StronglyAdapted ℱ g；h_eq : forall t, f t =ᵐ[μ
] g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `MeasureTheory.Supermartingale.condExp_ae_le`：condExp_ae_le [LE E] (hf : 
Supermartingale f ℱ μ) {i j : ι} (hij : i <= j) : μ[f j | ℱ i] <=ᵐ[μ] f i
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.Supermartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2
} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheo
ry.Measure Ω} [inst_1 : Normed…
-/
lemma congr [LE E] (hf : Supermartingale f ℱ μ) (hg : StronglyAdapted ℱ g)
    (h_eq : ∀ t, f t =ᵐ[μ] g t) :
    Supermartingale g ℱ μ := by
  refine ⟨hg, fun i j hij ↦ ?_, fun i ↦ (integrable_congr (h_eq i)).mp (hf.integrable i)⟩
  filter_upwards [condExp_ae_le hf hij, condExp_congr_ae (h_eq j), h_eq i] with ω h_le hcond h_eq
  rwa [← hcond, ← h_eq]
/-
**MeasureTheory.Supermartingale.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Sup
ermartingale`。
形式化陈述：add [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ) (hg : Superm
artingale g ℱ μ) : Supermartingale (f + g) ℱ μ
参数：hf : Supermartingale f ℱ μ；hg : Supermartingale g ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyAdapted.add`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `MeasureTheory.condExp_add`：condExp_add (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
· 使用定理 `MeasureTheory.Supermartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2
} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheo
ry.Measure Ω} [inst_1 : Normed…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
-/
theorem add [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ)
    (hg : Supermartingale g ℱ μ) : Supermartingale (f + g) ℱ μ := by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine (condExp_add (hf.integrable j) (hg.integrable j) _).le.trans ?_
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption
/-
**MeasureTheory.Supermartingale.add_martingale** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Supermartingale`。
形式化陈述：add_martingale [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ) (
hg : Martingale g ℱ μ) : Supermartingale (f + g) ℱ μ
参数：hf : Supermartingale f ℱ μ；hg : Martingale g ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Supermartingale.add`：add [Preorder E] [AddLeftMono E] (hf 
: Supermartingale f ℱ μ) (hg : Supermartingale g ℱ μ) : Supermartingale (f + g) 
ℱ μ
· 使用定理 `MeasureTheory.Martingale.supermartingale`：supermartingale [Preorder E] (
hf : Martingale f ℱ μ) : Supermartingale f ℱ μ
-/
theorem add_martingale [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f + g) ℱ μ :=
  hf.add hg.supermartingale
/-
**MeasureTheory.Supermartingale.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Sup
ermartingale`。
形式化陈述：neg [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ) : Submarting
ale (-f) ℱ μ
参数：hf : Supermartingale f ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyAdapted.neg`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_neg`：condExp_neg (f : α -> E) (m : MeasurableSpace
 α) : μ[-f | m] =ᵐ[μ] -μ[f | m]
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
-/
theorem neg [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ) :
    Submartingale (-f) ℱ μ := by
  refine ⟨hf.1.neg, fun i j hij => ?_, fun i => (hf.2.2 i).neg⟩
  refine EventuallyLE.trans ?_ (condExp_neg ..).symm.le
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

end Supermartingale

namespace Submartingale

/-
**MeasureTheory.Submartingale.stronglyAdapted** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E] {f : ι → Ω → E}   {ℱ : MeasureTheory.Filtration ι m
0} [inst_3 : LE E],   MeasureTheory.Submartingale f ℱ μ → MeasureTheory.Strongly
Adapted ℱ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
protected theorem stronglyAdapted [LE E] (hf : Submartingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1
/-
**MeasureTheory.Submartingale.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E] {f : ι → Ω → E}   {ℱ : MeasureTheory.Filtration ι m
0} [inst_3 : LE E],   MeasureTheory.Submartingale f ℱ μ → ∀ (i : ι), MeasureTheo
ry.StronglyMeasurable (f i)
参数：i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
-/
protected theorem stronglyMeasurable [LE E] (hf : Submartingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i
/-
**MeasureTheory.Submartingale.integrable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E] {f : ι → Ω → E}   {ℱ : MeasureTheory.Filtration ι m
0} [inst_3 : LE E],   MeasureTheory.Submartingale f ℱ μ → ∀ (i : ι), MeasureTheo
ry.Integrable (f i) μ
参数：i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
protected theorem integrable [LE E] (hf : Submartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i
/-
**MeasureTheory.Submartingale.ae_le_condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Submartingale`。
形式化陈述：ae_le_condExp [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i <= j) :
 f i <=ᵐ[μ] μ[f j | ℱ i]
参数：hf : Submartingale f ℱ μ；hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ae_le_condExp [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    f i ≤ᵐ[μ] μ[f j | ℱ i] :=
  hf.2.1 i j hij

variable [CompleteSpace E]
/-
**MeasureTheory.Submartingale.congr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Sub
martingale`。
形式化陈述：congr [LE E] (hf : Submartingale f ℱ μ) (hg : StronglyAdapted ℱ g) (h_eq :
 forall t, f t =ᵐ[μ] g t) : Submartingale g ℱ μ
参数：hf : Submartingale f ℱ μ；hg : StronglyAdapted ℱ g；h_eq : forall t, f t =ᵐ[μ] 
g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventuallyLE_congr`：eventuallyLE_congr {f f' g g' : α -> β} (hf :
 f =ᶠ[l] f') (hg : g =ᶠ[l] g') : f <=ᶠ[l] g ↔ f' <=ᶠ[l] g'
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `MeasureTheory.Submartingale.ae_le_condExp`：ae_le_condExp [LE E] (hf : Su
bmartingale f ℱ μ) {i j : ι} (hij : i <= j) : f i <=ᵐ[μ] μ[f j | ℱ i]
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
-/
lemma congr [LE E] (hf : Submartingale f ℱ μ) (hg : StronglyAdapted ℱ g)
    (h_eq : ∀ t, f t =ᵐ[μ] g t) :
    Submartingale g ℱ μ := by
  refine ⟨hg, fun i j hij ↦ ?_, fun i ↦ (integrable_congr (h_eq i)).mp (hf.integrable i)⟩
  exact (Filter.eventuallyLE_congr (h_eq i) (condExp_congr_ae (h_eq j))).mp (ae_le_condExp hf hij)
/-
**MeasureTheory.Submartingale.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Subma
rtingale`。
形式化陈述：add [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ) (hg : Submarti
ngale g ℱ μ) : Submartingale (f + g) ℱ μ
参数：hf : Submartingale f ℱ μ；hg : Submartingale g ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyAdapted.add`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_add`：condExp_add (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f + g | m] =ᵐ[μ] μ[f | m] + μ[g | m]
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
-/
theorem add [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Submartingale g ℱ μ) : Submartingale (f + g) ℱ μ := by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine EventuallyLE.trans ?_ (condExp_add (hf.integrable j) (hg.integrable j) _).symm.le
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine add_le_add ?_ ?_ <;> assumption
/-
**MeasureTheory.Submartingale.add_martingale** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Submartingale`。
形式化陈述：add_martingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ) (hg
 : Martingale g ℱ μ) : Submartingale (f + g) ℱ μ
参数：hf : Submartingale f ℱ μ；hg : Martingale g ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.add`：add [Preorder E] [AddLeftMono E] (hf : 
Submartingale f ℱ μ) (hg : Submartingale g ℱ μ) : Submartingale (f + g) ℱ μ
· 使用定理 `MeasureTheory.Martingale.submartingale`：submartingale [Preorder E] (hf :
 Martingale f ℱ μ) : Submartingale f ℱ μ
-/
theorem add_martingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f + g) ℱ μ :=
  hf.add hg.submartingale
/-
**MeasureTheory.Submartingale.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Subma
rtingale`。
形式化陈述：neg [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ) : Supermarting
ale (-f) ℱ μ
参数：hf : Submartingale f ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyAdapted.neg`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `MeasureTheory.condExp_neg`：condExp_neg (f : α -> E) (m : MeasurableSpace
 α) : μ[-f | m] =ᵐ[μ] -μ[f | m]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
-/
theorem neg [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ) :
    Supermartingale (-f) ℱ μ := by
  refine ⟨hf.1.neg, fun i j hij => (condExp_neg ..).le.trans ?_, fun i => (hf.2.2 i).neg⟩
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

/-- The converse of this lemma is `MeasureTheory.submartingale_of_setIntegral_le`. -/
/-
**MeasureTheory.Submartingale.setIntegral_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Submartingale`。
形式化陈述：setIntegral_le [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule Re
al E] [ClosedIciTopology E] [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω -> E} (hf : 
Submartingale f ℱ μ) {i j : ι} (hij : i <= j) {s : Set Ω} (hs : MeasurableSet[ℱ 
i] s) : ∫ ω in s, f i ω ∂μ <= ∫ ω in s, f j ω ∂μ
参数：hf : Submartingale f ℱ μ；hij : i <= j；hs : MeasurableSet[ℱ i] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `MeasureTheory.Supermartingale.setIntegral_le`：setIntegral_le [PartialOrd
er E] [IsOrderedAddMonoid E] [IsOrderedModule Real E] [ClosedIciTopology E] [Sig
maFiniteFiltration μ ℱ] {f : ι -> …
· 使用定理 `MeasureTheory.Submartingale.neg`：neg [Preorder E] [AddLeftMono E] (hf : 
Submartingale f ℱ μ) : Supermartingale (-f) ℱ μ

--- 原说明 ---
The converse of this lemma is `MeasureTheory.submartingale_of_setIntegral_le`.
-/
theorem setIntegral_le [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [ClosedIciTopology E] [SigmaFiniteFiltration μ ℱ] {f : ι → Ω → E} (hf : Submartingale f ℱ μ)
    {i j : ι} (hij : i ≤ j) {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f j ω ∂μ := by
  rw [← neg_le_neg_iff, ← integral_neg, ← integral_neg]
  exact Supermartingale.setIntegral_le hf.neg hij hs
/-
**MeasureTheory.Submartingale.sub_supermartingale** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Submartingale`。
形式化陈述：sub_supermartingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ
) (hg : Supermartingale g ℱ μ) : Submartingale (f - g) ℱ μ
参数：hf : Submartingale f ℱ μ；hg : Supermartingale g ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.Submartingale.add`：add [Preorder E] [AddLeftMono E] (hf : 
Submartingale f ℱ μ) (hg : Submartingale g ℱ μ) : Submartingale (f + g) ℱ μ
· 使用定理 `MeasureTheory.Supermartingale.neg`：neg [Preorder E] [AddLeftMono E] (hf 
: Supermartingale f ℱ μ) : Submartingale (-f) ℱ μ
-/
theorem sub_supermartingale [Preorder E] [AddLeftMono E]
    (hf : Submartingale f ℱ μ) (hg : Supermartingale g ℱ μ) : Submartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
/-
**MeasureTheory.Submartingale.sub_martingale** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Submartingale`。
形式化陈述：sub_martingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ) (hg
 : Martingale g ℱ μ) : Submartingale (f - g) ℱ μ
参数：hf : Submartingale f ℱ μ；hg : Martingale g ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.sub_supermartingale`：sub_supermartingale [Pr
eorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ) (hg : Supermartingale g ℱ μ
) : Submartingale (f - g) ℱ μ
· 使用定理 `MeasureTheory.Martingale.supermartingale`：supermartingale [Preorder E] (
hf : Martingale f ℱ μ) : Supermartingale f ℱ μ
-/
theorem sub_martingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f - g) ℱ μ :=
  hf.sub_supermartingale hg.supermartingale
/-
**MeasureTheory.Submartingale.sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Subma
rtingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E]   {ℱ : MeasureTheory.Filtration ι m0} [CompleteSpac
e E] [inst_4 : Lattice E] [ContinuousSup E] [HasSolidNorm E]   [IsOrderedAddMono
id E] [IsOrderedModule ℝ E] {f g : ι → Ω → E},   MeasureTheory.Submartingale f ℱ
 μ → MeasureTheory.Submartingale g ℱ μ → MeasureTheory.Submartingale (f ⊔ g) ℱ μ
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.sup`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace β] [inst_2 : M
ax β]   [ContinuousSup β],…
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `Filter.EventuallyLE.sup_le`：∀ {α : Type u} {β : Type v} [inst : Semilatt
iceSup β] {l : Filter α} {f g h : α → β},   f ≤ᶠ[l] h → g ≤ᶠ[l] h → f ⊔ g ≤ᶠ[l] 
h
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `MeasureTheory.condExp_mono`：condExp_mono (hf : Integrable f μ) (hg : Int
egrable g μ) (hfg : f <=ᵐ[μ] g) : μ[f | m] <=ᵐ[μ] μ[g | m]
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Integrable.sup`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {β : Type u_8} [inst : NormedAddCommGroup β]   [ins
t_1 : Lattice β] […
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
protected theorem sup [Lattice E] [ContinuousSup E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] {f g : ι → Ω → E} (hf : Submartingale f ℱ μ)
    (hg : Submartingale g ℱ μ) :
    Submartingale (f ⊔ g) ℱ μ := by
  refine ⟨fun i =>
    @StronglyMeasurable.sup _ _ _ _ (ℱ i) _ _ _ (hf.stronglyAdapted i) (hg.stronglyAdapted i),
    fun i j hij => ?_, fun i => Integrable.sup (hf.integrable _) (hg.integrable _)⟩
  refine EventuallyLE.sup_le ?_ ?_
  · exact EventuallyLE.trans (hf.2.1 i j hij)
      (condExp_mono (hf.integrable _) (Integrable.sup (hf.integrable j) (hg.integrable j))
        (Eventually.of_forall fun x => le_sup_left))
  · exact EventuallyLE.trans (hg.2.1 i j hij)
      (condExp_mono (hg.integrable _) (Integrable.sup (hf.integrable j) (hg.integrable j))
        (Eventually.of_forall fun x => le_sup_right))
/-
**MeasureTheory.Submartingale.pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Subma
rtingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E]   {ℱ : MeasureTheory.Filtration ι m0} [CompleteSpac
e E] [inst_4 : Lattice E] [ContinuousSup E] [HasSolidNorm E]   [IsOrderedAddMono
id E] [IsOrderedModule ℝ E] {f : ι → Ω → E},   MeasureTheory.Submartingale f ℱ μ
 → MeasureTheory.Submartingale f⁺ ℱ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.sup`：∀ {Ω : Type u_1} {E : Type u_2} {ι : Ty
pe u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Measur
e Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Martingale.submartingale`：submartingale [Preorder E] (hf :
 Martingale f ℱ μ) : Submartingale f ℱ μ
· 使用定理 `MeasureTheory.martingale_zero`：martingale_zero (ℱ : Filtration ι m0) (μ 
: Measure Ω) : Martingale (0 : ι -> Ω -> E) ℱ μ
-/
protected theorem pos [Lattice E] [ContinuousSup E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] {f : ι → Ω → E} (hf : Submartingale f ℱ μ) :
    Submartingale (f⁺) ℱ μ :=
  hf.sup (martingale_zero _ _ _).submartingale

end Submartingale

section Submartingale

/-
**MeasureTheory.submartingale_of_setIntegral_le** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：submartingale_of_setIntegral_le [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω ->
 Real} (hadp : StronglyAdapted ℱ f) (hint : forall i, Integrable (f i) μ) (hf : 
forall i j : ι, i <= j -> forall s : Set Ω, MeasurableSet[ℱ i] s -> ∫ ω in s, f 
i ω ∂μ <= ∫ ω in s, f j ω ∂μ) : Submartingale f ℱ μ
参数：hadp : StronglyAdapted ℱ f；hint : forall i, Integrable (f i) μ；hf : forall i 
j : ι, i <= j -> forall s : Set Ω, MeasurableSet[ℱ i] s -> ∫ ω in s, f i ω ∂μ <=
 ∫ ω in s, f j ω ∂μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg`：ae_nonneg_of_foral
l_setIntegral_nonneg (hf : Integrable f μ) (hf_zero : forall s, MeasurableSet s 
-> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ) : 0 <…
· 使用定理 `MeasureTheory.Integrable.trim`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{H : Type u_8} [inst : NormedAddCommGroup H] {m0 : MeasurableSpace α}   {μ' : Me
asureTheory.Measure…
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.StronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Sub β
]   [ContinuousSub β],   M…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_trim`：setIntegral_trim {X} {m m0 : MeasurableS
pace X} {μ : Measure X} (hm : m <= m0) {f : X -> E} (hf_meas : StronglyMeasurabl
e[m] f) {s : Set X} …
· 使用定理 `MeasureTheory.integral_sub'`：integral_sub' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.ae_le_of_ae_le_trim`：ae_le_of_ae_le_trim {E} [LE E] {hm : 
m <= m0} {f₁ f₂ : α -> E} (h12 : f₁ <=ᵐ[μ.trim hm] f₂) : f₁ <=ᵐ[μ] f₂
-/
theorem submartingale_of_setIntegral_le [SigmaFiniteFiltration μ ℱ]
    {f : ι → Ω → ℝ} (hadp : StronglyAdapted ℱ f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i j : ι,
      i ≤ j → ∀ s : Set Ω, MeasurableSet[ℱ i] s → ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f j ω ∂μ) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  suffices f i ≤ᵐ[μ.trim (ℱ.le i)] μ[f j | ℱ i] by exact ae_le_of_ae_le_trim this
  suffices 0 ≤ᵐ[μ.trim (ℱ.le i)] μ[f j | ℱ i] - f i by
    filter_upwards [this] with x hx
    rwa [← sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg
    ((integrable_condExp.sub (hint i)).trim _ (stronglyMeasurable_condExp.sub <| hadp i))
      fun s hs _ => ?_
  specialize hf i j hij s hs
  rwa [← setIntegral_trim _ (stronglyMeasurable_condExp.sub <| hadp i) hs,
    integral_sub' integrable_condExp.integrableOn (hint i).integrableOn, sub_nonneg,
    setIntegral_condExp (ℱ.le i) (hint j) hs]

variable [CompleteSpace E]
/-
**MeasureTheory.submartingale_of_condExp_sub_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：submartingale_of_condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E
] [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω -> E} (hadp : StronglyAdapted ℱ f) (hi
nt : forall i, Integrable (f i) μ) (hf : forall i j, i <= j -> 0 <=ᵐ[μ] μ[f j - 
f i | ℱ i]) : Submartingale f ℱ μ
参数：hadp : StronglyAdapted ℱ f；hint : forall i, Integrable (f i) μ；hf : forall i 
j, i <= j -> 0 <=ᵐ[μ] μ[f j - f i | ℱ i]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `Filter.eventually_sub_nonneg`：eventually_sub_nonneg [AddGroup β] [LE β] 
[AddRightMono β] {l : Filter α} {f g : α -> β} : 0 <=ᶠ[l] g - f ↔ f <=ᶠ[l] g
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `MeasureTheory.condExp_sub`：condExp_sub (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m]
-/
theorem submartingale_of_condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration μ ℱ] {f : ι → Ω → E} (hadp : StronglyAdapted ℱ f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i | ℱ i]) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  rw [← condExp_of_stronglyMeasurable (ℱ.le _) (hadp _) (hint _), ← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i j hij) (condExp_sub (hint _) (hint _) _).le
/-
**MeasureTheory.Submartingale.condExp_sub_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : M
easurableSpace Ω}   {μ : MeasureTheory.Measure Ω} [inst_1 : NormedAddCommGroup E
] [inst_2 : NormedSpace ℝ E]   {ℱ : MeasureTheory.Filtration ι m0} [CompleteSpac
e E] [inst_4 : PartialOrder E] [IsOrderedAddMonoid E]   {f : ι → Ω → E}, Measure
Theory.Submartingale f ℱ μ → ∀ {i j : ι}, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i | ↑ℱ i]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_sub_nonneg`：eventually_sub_nonneg [AddGroup β] [LE β] 
[AddRightMono β] {l : Filter α} {f g : α -> β} : 0 <=ᶠ[l] g - f ↔ f <=ᶠ[l] g
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_sub`：condExp_sub (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m]
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `Filter.EventuallyLE.refl`：∀ {α : Type u} {β : Type v} [inst : Preorder β
] (l : Filter α) (f : α → β), f ≤ᶠ[l] f
-/
theorem Submartingale.condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    {f : ι → Ω → E} (hf : Submartingale f ℱ μ) {i j : ι}
    (hij : i ≤ j) : 0 ≤ᵐ[μ] μ[f j - f i | ℱ i] := by
  by_cases h : SigmaFinite (μ.trim (ℱ.le i))
  swap; · rw [condExp_of_not_sigmaFinite (ℱ.le i) h]
  refine EventuallyLE.trans ?_ (condExp_sub (hf.integrable _) (hf.integrable _) _).symm.le
  rw [eventually_sub_nonneg,
    condExp_of_stronglyMeasurable (ℱ.le _) (hf.stronglyAdapted _) (hf.integrable _)]
  exact hf.2.1 i j hij
/-
**MeasureTheory.submartingale_iff_condExp_sub_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：submartingale_iff_condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid 
E] [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω -> E} : Submartingale f ℱ μ ↔ Strongl
yAdapted ℱ f ∧ (forall i, Integrable (f i) μ) ∧ forall i j, i <= j -> 0 <=ᵐ[μ] μ
[f j - f i | ℱ i]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Submartingale.condExp_sub_nonneg`：∀ {Ω : Type u_1} {E : Ty
pe u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : Measu
reTheory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.submartingale_of_condExp_sub_nonneg`：submartingale_of_cond
Exp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E] [SigmaFiniteFiltration μ 
ℱ] {f : ι -> Ω -> E} (hadp : StronglyAd…
-/
theorem submartingale_iff_condExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    [SigmaFiniteFiltration μ ℱ] {f : ι → Ω → E} :
    Submartingale f ℱ μ ↔
      StronglyAdapted ℱ f ∧ (∀ i, Integrable (f i) μ) ∧ ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i | ℱ i] :=
  ⟨fun h => ⟨h.stronglyAdapted, h.integrable, fun _ _ => h.condExp_sub_nonneg⟩,
   fun ⟨hadp, hint, h⟩ => submartingale_of_condExp_sub_nonneg hadp hint h⟩

end Submartingale

namespace Supermartingale

/-
**MeasureTheory.Supermartingale.sub_submartingale** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Supermartingale`。
形式化陈述：sub_submartingale [CompleteSpace E] [Preorder E] [AddLeftMono E] (hf : Sup
ermartingale f ℱ μ) (hg : Submartingale g ℱ μ) : Supermartingale (f - g) ℱ μ
参数：hf : Supermartingale f ℱ μ；hg : Submartingale g ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.Supermartingale.add`：add [Preorder E] [AddLeftMono E] (hf 
: Supermartingale f ℱ μ) (hg : Supermartingale g ℱ μ) : Supermartingale (f + g) 
ℱ μ
· 使用定理 `MeasureTheory.Submartingale.neg`：neg [Preorder E] [AddLeftMono E] (hf : 
Submartingale f ℱ μ) : Supermartingale (-f) ℱ μ
-/
theorem sub_submartingale [CompleteSpace E] [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Submartingale g ℱ μ) : Supermartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
/-
**MeasureTheory.Supermartingale.sub_martingale** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Supermartingale`。
形式化陈述：sub_martingale [CompleteSpace E] [Preorder E] [AddLeftMono E] (hf : Superm
artingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f - g) ℱ μ
参数：hf : Supermartingale f ℱ μ；hg : Martingale g ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Supermartingale.sub_submartingale`：sub_submartingale [Comp
leteSpace E] [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ) (hg : Sub
martingale g ℱ μ) : Supermartingale (…
· 使用定理 `MeasureTheory.Martingale.submartingale`：submartingale [Preorder E] (hf :
 Martingale f ℱ μ) : Submartingale f ℱ μ
-/
theorem sub_martingale [CompleteSpace E] [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f - g) ℱ μ :=
  hf.sub_submartingale hg.submartingale

section

variable {F : Type*} [NormedAddCommGroup F] [PartialOrder F] [NormedSpace ℝ F] [CompleteSpace F]
  [IsOrderedModule ℝ F]

/-
**MeasureTheory.Supermartingale.smul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Supermartingale`。
形式化陈述：smul_nonneg {f : ι -> Ω -> F} {c : Real} (hc : 0 <= c) (hf : Supermartinga
le f ℱ μ) : Supermartingale (c • f) ℱ μ
参数：hc : 0 <= c；hf : Supermartingale f ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyAdapted.smul`：∀ {Ω : Type u_1} {ι : Type u_2} {m :
 MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β 
: ι → Type u_3} [inst_1 …
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.condExp_smul`：condExp_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : 
α -> E) (m : MeasurableSpace α) : μ[c • f | m] =ᵐ[μ] c • μ[f | m]
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
-/
theorem smul_nonneg {f : ι → Ω → F} {c : ℝ} (hc : 0 ≤ c) (hf : Supermartingale f ℱ μ) :
    Supermartingale (c • f) ℱ μ := by
  refine ⟨hf.1.smul c, fun i j hij => ?_, fun i => (hf.2.2 i).smul c⟩
  filter_upwards [condExp_smul c (f j) (ℱ i), hf.2.1 i j hij] with ω hω hle
  simpa only [hω, Pi.smul_apply] using smul_le_smul_of_nonneg_left hle hc
/-
**MeasureTheory.Supermartingale.smul_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Supermartingale`。
形式化陈述：smul_nonpos [IsOrderedAddMonoid F] {f : ι -> Ω -> F} {c : Real} (hc : c <=
 0) (hf : Supermartingale f ℱ μ) : Submartingale (c • f) ℱ μ
参数：hc : c <= 0；hf : Supermartingale f ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `MeasureTheory.Supermartingale.neg`：neg [Preorder E] [AddLeftMono E] (hf 
: Supermartingale f ℱ μ) : Submartingale (-f) ℱ μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.Supermartingale.smul_nonneg`：smul_nonneg {f : ι -> Ω -> F}
 {c : Real} (hc : 0 <= c) (hf : Supermartingale f ℱ μ) : Supermartingale (c • f)
 ℱ μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
-/
theorem smul_nonpos [IsOrderedAddMonoid F] {f : ι → Ω → F} {c : ℝ}
    (hc : c ≤ 0) (hf : Supermartingale f ℱ μ) :
    Submartingale (c • f) ℱ μ := by
  rw [← neg_neg c, neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

end

end Supermartingale

namespace Submartingale

section

variable {F : Type*} [NormedAddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F]
  [NormedSpace ℝ F] [CompleteSpace F] [IsOrderedModule ℝ F]

/-
**MeasureTheory.Submartingale.smul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Submartingale`。
形式化陈述：smul_nonneg {f : ι -> Ω -> F} {c : Real} (hc : 0 <= c) (hf : Submartingale
 f ℱ μ) : Submartingale (c • f) ℱ μ
参数：hc : 0 <= c；hf : Submartingale f ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `MeasureTheory.Supermartingale.neg`：neg [Preorder E] [AddLeftMono E] (hf 
: Supermartingale f ℱ μ) : Submartingale (-f) ℱ μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.Supermartingale.smul_nonneg`：smul_nonneg {f : ι -> Ω -> F}
 {c : Real} (hc : 0 <= c) (hf : Supermartingale f ℱ μ) : Supermartingale (c • f)
 ℱ μ
· 使用定理 `MeasureTheory.Submartingale.neg`：neg [Preorder E] [AddLeftMono E] (hf : 
Submartingale f ℱ μ) : Supermartingale (-f) ℱ μ
-/
theorem smul_nonneg {f : ι → Ω → F} {c : ℝ} (hc : 0 ≤ c) (hf : Submartingale f ℱ μ) :
    Submartingale (c • f) ℱ μ := by
  rw [← neg_neg (c • f), ← smul_neg]
  exact Supermartingale.neg (hf.neg.smul_nonneg hc)
/-
**MeasureTheory.Submartingale.smul_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Submartingale`。
形式化陈述：smul_nonpos {f : ι -> Ω -> F} {c : Real} (hc : c <= 0) (hf : Submartingale
 f ℱ μ) : Supermartingale (c • f) ℱ μ
参数：hc : c <= 0；hf : Submartingale f ℱ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `MeasureTheory.Submartingale.neg`：neg [Preorder E] [AddLeftMono E] (hf : 
Submartingale f ℱ μ) : Supermartingale (-f) ℱ μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.Submartingale.smul_nonneg`：smul_nonneg {f : ι -> Ω -> F} {
c : Real} (hc : 0 <= c) (hf : Submartingale f ℱ μ) : Submartingale (c • f) ℱ μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
-/
theorem smul_nonpos {f : ι → Ω → F} {c : ℝ} (hc : c ≤ 0) (hf : Submartingale f ℱ μ) :
    Supermartingale (c • f) ℱ μ := by
  rw [← neg_neg c, neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

end

end Submartingale

section Nat

variable {𝒢 : Filtration ℕ m0}

section SubSuper

section OfSetIntegral

/-
**MeasureTheory.submartingale_of_setIntegral_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：submartingale_of_setIntegral_le_succ [IsFiniteMeasure μ] {f : Nat -> Ω -> 
Real} (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ) (hf : f
orall i, forall s : Set Ω, MeasurableSet[𝒢 i] s -> ∫ ω in s, f i ω ∂μ <= ∫ ω in 
s, f (i + 1) ω ∂μ) : Submartingale f 𝒢 μ
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ；hf : forall i,
 forall s : Set Ω, MeasurableSet[𝒢 i] s -> ∫ ω in s, f i ω ∂μ <= ∫ ω in s, f (i 
+ 1) ω ∂μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.submartingale_of_setIntegral_le`：submartingale_of_setInteg
ral_le [SigmaFiniteFiltration μ ℱ] {f : ι -> Ω -> Real} (hadp : StronglyAdapted 
ℱ f) (hint : forall i, Integrable (…
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
-/
theorem submartingale_of_setIntegral_le_succ [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, MeasurableSet[𝒢 i] s → ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f (i + 1) ω ∂μ) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  induction hij with
  | refl => rfl
  | step hk₁ hk₂ => exact hk₂.trans (hf _ s (𝒢.mono hk₁ _ hs))
/-
**MeasureTheory.supermartingale_of_setIntegral_succ_le** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：supermartingale_of_setIntegral_succ_le [IsFiniteMeasure μ] {f : Nat -> Ω -
> Real} (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ) (hf :
 forall i, forall s : Set Ω, MeasurableSet[𝒢 i] s -> ∫ ω in s, f (i + 1) ω ∂μ <=
 ∫ ω in s, f i ω ∂μ) : Supermartingale f 𝒢 μ
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ；hf : forall i,
 forall s : Set Ω, MeasurableSet[𝒢 i] s -> ∫ ω in s, f (i + 1) ω ∂μ <= ∫ ω in s,
 f i ω ∂μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MeasureTheory.Submartingale.neg`：neg [Preorder E] [AddLeftMono E] (hf : 
Submartingale f ℱ μ) : Supermartingale (-f) ℱ μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.submartingale_of_setIntegral_le_succ`：submartingale_of_set
Integral_le_succ [IsFiniteMeasure μ] {f : Nat -> Ω -> Real} (hadp : StronglyAdap
ted 𝒢 f) (hint : forall i, Integrable (f…
· 使用定理 `MeasureTheory.StronglyAdapted.neg`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem supermartingale_of_setIntegral_succ_le [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, MeasurableSet[𝒢 i] s → ∫ ω in s, f (i + 1) ω ∂μ ≤ ∫ ω in s, f i ω ∂μ) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_of_setIntegral_le_succ hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [integral_neg, Pi.neg_apply, neg_le_neg_iff]

end OfSetIntegral

section OfSucc

variable [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E] [ClosedIciTopology E]
  [IsOrderedModule ℝ E]

/-
**MeasureTheory.submartingale_nat** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：submartingale_nat [IsFiniteMeasure μ] {f : Nat -> Ω -> E} (hadp : Strongly
Adapted 𝒢 f) (hint : forall i, Integrable (f i) μ) (hf : forall i, f i <=ᵐ[μ] μ[
f (i + 1) | 𝒢 i]) : Submartingale f 𝒢 μ
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ；hf : forall i,
 f i <=ᵐ[μ] μ[f (i + 1) | 𝒢 i]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Filtration.condExp_condExp`：∀ {Ω : Type u_1} {ι : Type u_2
} {m : MeasurableSpace Ω} [inst : Preorder ι] {E : Type u_3}   [inst_1 : NormedA
ddCommGroup E] [inst_2 : Norme…
· 使用引理 `MeasureTheory.condExp_mono`：condExp_mono (hf : Integrable f μ) (hg : Int
egrable g μ) (hfg : f <=ᵐ[μ] g) : μ[f | m] <=ᵐ[μ] μ[g | m]
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
-/
theorem submartingale_nat [IsFiniteMeasure μ] {f : ℕ → Ω → E} (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, f i ≤ᵐ[μ] μ[f (i + 1) | 𝒢 i]) :
    Submartingale f 𝒢 μ := by
  refine ⟨hadp, fun i j hij ↦ ?_, hint⟩
  induction j, hij using Nat.le_induction with
  | base =>
    refine ae_of_all _ fun _ ↦ ?_
    rw [condExp_of_stronglyMeasurable (𝒢.le i) (hadp i) (hint i)]
  | succ k hik hk =>
    filter_upwards [hk, condExp_mono (hint k) integrable_condExp (hf k),
      𝒢.condExp_condExp (f (k + 1)) hik] with ω hω1 hω2 hω3
    grw [hω1, hω2, hω3]
/-
**MeasureTheory.supermartingale_nat** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：supermartingale_nat [IsFiniteMeasure μ] {f : Nat -> Ω -> E} (hadp : Strong
lyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ) (hf : forall i, μ[f (i + 1)
 | 𝒢 i] <=ᵐ[μ] f i) : Supermartingale f 𝒢 μ
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ；hf : forall i,
 μ[f (i + 1) | 𝒢 i] <=ᵐ[μ] f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MeasureTheory.Submartingale.neg`：neg [Preorder E] [AddLeftMono E] (hf : 
Submartingale f ℱ μ) : Supermartingale (-f) ℱ μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.submartingale_nat`：submartingale_nat [IsFiniteMeasure μ] {
f : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f 
i) μ) (hf : forall i,…
· 使用定理 `MeasureTheory.StronglyAdapted.neg`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_neg`：condExp_neg (f : α -> E) (m : MeasurableSpace
 α) : μ[-f | m] =ᵐ[μ] -μ[f | m]
-/
theorem supermartingale_nat [IsFiniteMeasure μ] {f : ℕ → Ω → E} (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, μ[f (i + 1) | 𝒢 i] ≤ᵐ[μ] f i) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_nat hadp.neg (fun i => (hint i).neg) fun i =>
    EventuallyLE.trans ?_ (condExp_neg ..).symm.le).neg
  filter_upwards [hf i] with x hx using neg_le_neg hx
/-
**MeasureTheory.submartingale_of_condExp_sub_nonneg_nat** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：submartingale_of_condExp_sub_nonneg_nat [IsFiniteMeasure μ] {f : Nat -> Ω 
-> E} (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ) (hf : f
orall i, 0 <=ᵐ[μ] μ[f (i + 1) - f i | 𝒢 i]) : Submartingale f 𝒢 μ
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ；hf : forall i,
 0 <=ᵐ[μ] μ[f (i + 1) - f i | 𝒢 i]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.submartingale_nat`：submartingale_nat [IsFiniteMeasure μ] {
f : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f 
i) μ) (hf : forall i,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `Filter.eventually_sub_nonneg`：eventually_sub_nonneg [AddGroup β] [LE β] 
[AddRightMono β] {l : Filter α} {f g : α -> β} : 0 <=ᶠ[l] g - f ↔ f <=ᶠ[l] g
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `MeasureTheory.condExp_sub`：condExp_sub (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m]
-/
theorem submartingale_of_condExp_sub_nonneg_nat [IsFiniteMeasure μ] {f : ℕ → Ω → E}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, 0 ≤ᵐ[μ] μ[f (i + 1) - f i | 𝒢 i]) : Submartingale f 𝒢 μ := by
  refine submartingale_nat hadp hint fun i => ?_
  rw [← condExp_of_stronglyMeasurable (𝒢.le _) (hadp _) (hint _), ← eventually_sub_nonneg]
  exact EventuallyLE.trans (hf i) (condExp_sub (hint _) (hint _) _).le
/-
**MeasureTheory.supermartingale_of_condExp_sub_nonneg_nat** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：supermartingale_of_condExp_sub_nonneg_nat [IsFiniteMeasure μ] {f : Nat -> 
Ω -> E} (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ) (hf :
 forall i, 0 <=ᵐ[μ] μ[f i - f (i + 1) | 𝒢 i]) : Supermartingale f 𝒢 μ
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ；hf : forall i,
 0 <=ᵐ[μ] μ[f i - f (i + 1) | 𝒢 i]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MeasureTheory.Submartingale.neg`：neg [Preorder E] [AddLeftMono E] (hf : 
Submartingale f ℱ μ) : Supermartingale (-f) ℱ μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.submartingale_of_condExp_sub_nonneg_nat`：submartingale_of_
condExp_sub_nonneg_nat [IsFiniteMeasure μ] {f : Nat -> Ω -> E} (hadp : StronglyA
dapted 𝒢 f) (hint : forall i, Integrable (f…
· 使用定理 `MeasureTheory.StronglyAdapted.neg`：∀ {Ω : Type u_1} {ι : Type u_2} {m : 
MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   {β :
 ι → Type u_3} [inst_1 …
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `neg_sub_neg`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α)
, -a - -b = b - a
-/
theorem supermartingale_of_condExp_sub_nonneg_nat [IsFiniteMeasure μ] {f : ℕ → Ω → E}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, 0 ≤ᵐ[μ] μ[f i - f (i + 1) | 𝒢 i]) : Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_of_condExp_sub_nonneg_nat hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [Pi.zero_apply, Pi.neg_apply, neg_sub_neg]

end OfSucc

section Preorder

variable [Preorder E]

-- Note that one cannot use `Submartingale.zero_le_of_predictable` to prove the other two
-- corresponding lemmas without imposing more restrictions to the ordering of `E`
/-- A predictable submartingale is a.e. greater than or equal to its initial state. -/
/-
**MeasureTheory.Submartingale.zero_le_of_predictable** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {𝒢 : Mea
sureTheory.Filtration ℕ m0} [inst_2 : Preorder E]   [MeasureTheory.SigmaFiniteFi
ltration μ 𝒢] {f : ℕ → Ω → E},   MeasureTheory.Submartingale f 𝒢 μ → (MeasureThe
ory.StronglyAdapted 𝒢 fun n => f (n + 1)) → ∀ (n : ℕ), f 0 ≤ᵐ[μ] f n
参数：MeasureTheory.StronglyAdapted 𝒢 fun n => f (n + 1)；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyLE.refl`：∀ {α : Type u} {β : Type v} [inst : Preorder β
] (l : Filter α) (f : α → β), f ≤ᶠ[l] f
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.EventuallyLE.trans_eq`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g =ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…

--- 原说明 ---
A predictable submartingale is a.e. greater than or equal to its initial state.
-/
theorem Submartingale.zero_le_of_predictable [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
    (hfmgle : Submartingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n => f (n + 1)) (n : ℕ) :
    f 0 ≤ᵐ[μ] f n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ih.trans ((hfmgle.2.1 k (k + 1) k.le_succ).trans_eq <| Germ.coe_eq.mp <|
    congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _) (hfadp _) <| hfmgle.integrable _)

/-- A predictable supermartingale is a.e. less than or equal to its initial state. -/
/-
**MeasureTheory.Supermartingale.le_zero_of_predictable** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Supermartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {𝒢 : Mea
sureTheory.Filtration ℕ m0} [inst_2 : Preorder E]   [MeasureTheory.SigmaFiniteFi
ltration μ 𝒢] {f : ℕ → Ω → E},   MeasureTheory.Supermartingale f 𝒢 μ → (MeasureT
heory.StronglyAdapted 𝒢 fun n => f (n + 1)) → ∀ (n : ℕ), f n ≤ᵐ[μ] f 0
参数：MeasureTheory.StronglyAdapted 𝒢 fun n => f (n + 1)；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyLE.refl`：∀ {α : Type u} {β : Type v} [inst : Preorder β
] (l : Filter α) (f : α → β), f ≤ᶠ[l] f
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.trans_le`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f =ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.Supermartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2
} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheo
ry.Measure Ω} [inst_1 : Normed…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
A predictable supermartingale is a.e. less than or equal to its initial state.
-/
theorem Supermartingale.le_zero_of_predictable [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
    (hfmgle : Supermartingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n => f (n + 1))
    (n : ℕ) : f n ≤ᵐ[μ] f 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ((Germ.coe_eq.mp <| congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _)
      (hfadp _) <| hfmgle.integrable _).symm.trans_le (hfmgle.2.1 k (k + 1) k.le_succ)).trans ih

end Preorder

end SubSuper

/-
**MeasureTheory.martingale_nat** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：martingale_nat [CompleteSpace E] [IsFiniteMeasure μ] {f : Nat -> Ω -> E} (
hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ) (hf : forall i
, f i =ᵐ[μ] μ[f (i + 1) | 𝒢 i]) : Martingale f 𝒢 μ
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ；hf : forall i,
 f i =ᵐ[μ] μ[f (i + 1) | 𝒢 i]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Filtration.condExp_condExp`：∀ {Ω : Type u_1} {ι : Type u_2
} {m : MeasurableSpace Ω} [inst : Preorder ι] {E : Type u_3}   [inst_1 : NormedA
ddCommGroup E] [inst_2 : Norme…
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem martingale_nat [CompleteSpace E] [IsFiniteMeasure μ]
    {f : ℕ → Ω → E} (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, f i =ᵐ[μ] μ[f (i + 1) | 𝒢 i]) :
    Martingale f 𝒢 μ := by
  refine ⟨hadp, fun i j hij ↦ ?_⟩
  induction j, hij using Nat.le_induction with
  | base =>
    refine ae_of_all _ fun _ ↦ ?_
    rw [condExp_of_stronglyMeasurable (𝒢.le i) (hadp i) (hint i)]
  | succ k hik hk =>
    filter_upwards [hk, condExp_congr_ae (hf k), 𝒢.condExp_condExp (f (k + 1)) hik]
      with ω hω1 hω2 hω3
    rw [← hω1, hω2, hω3]
/-
**MeasureTheory.martingale_of_setIntegral_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：martingale_of_setIntegral_eq_succ [CompleteSpace E] [IsFiniteMeasure μ] {f
 : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i
) μ) (hf : forall i, forall s : Set Ω, MeasurableSet[𝒢 i] s -> ∫ ω in s, f i ω ∂
μ = ∫ ω in s, f (i + 1) ω ∂μ) : Martingale f 𝒢 μ
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ；hf : forall i,
 forall s : Set Ω, MeasurableSet[𝒢 i] s -> ∫ ω in s, f i ω ∂μ = ∫ ω in s, f (i +
 1) ω ∂μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.martingale_nat`：martingale_nat [CompleteSpace E] [IsFinite
Measure μ] {f : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f) (hint : forall i, In
tegrable (f i) μ) …
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq`：∀ {α : Type u_1
} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : 
NormedAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `MeasureTheory.Integrable.trim`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{H : Type u_8} [inst : NormedAddCommGroup H] {m0 : MeasurableSpace α}   {μ' : Me
asureTheory.Measure…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_trim`：setIntegral_trim {X} {m m0 : MeasurableS
pace X} {μ : Measure X} (hm : m <= m0) {f : X -> E} (hf_meas : StronglyMeasurabl
e[m] f) {s : Set X} …
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
-/
theorem martingale_of_setIntegral_eq_succ [CompleteSpace E] [IsFiniteMeasure μ] {f : ℕ → Ω → E}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, MeasurableSet[𝒢 i] s → ∫ ω in s, f i ω ∂μ = ∫ ω in s, f (i + 1) ω ∂μ) :
    Martingale f 𝒢 μ := by
  refine martingale_nat hadp hint fun n ↦ ae_eq_of_ae_eq_trim <|
    ((hint n).trim (𝒢.le n) (hadp n)).ae_eq_of_forall_setIntegral_eq _ _
    (integrable_condExp.trim (𝒢.le n) stronglyMeasurable_condExp) fun s ms hs ↦ ?_
  rw [← setIntegral_trim (𝒢.le n) (hadp n) ms,
    ← setIntegral_trim (𝒢.le n) stronglyMeasurable_condExp ms,
    setIntegral_condExp (𝒢.le n) (hint (n + 1)) ms, hf n s ms]
/-
**MeasureTheory.martingale_of_condExp_sub_eq_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：martingale_of_condExp_sub_eq_zero_nat [CompleteSpace E] [IsFiniteMeasure μ
] {f : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable 
(f i) μ) (hf : forall i, μ[f (i + 1) - f i | 𝒢 i] =ᵐ[μ] 0) : Martingale f 𝒢 μ
参数：hadp : StronglyAdapted 𝒢 f；hint : forall i, Integrable (f i) μ；hf : forall i,
 μ[f (i + 1) - f i | 𝒢 i] =ᵐ[μ] 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.martingale_nat`：martingale_nat [CompleteSpace E] [IsFinite
Measure μ] {f : Nat -> Ω -> E} (hadp : StronglyAdapted 𝒢 f) (hint : forall i, In
tegrable (f i) μ) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用引理 `Filter.eventuallyEq_comm`：eventuallyEq_comm {f g : α -> β} {l : Filter α
} : f =ᶠ[l] g ↔ g =ᶠ[l] f
· 使用定理 `Filter.eventuallyEq_iff_sub`：eventuallyEq_iff_sub [AddGroup β] {f g : α 
-> β} {l : Filter α} : f =ᶠ[l] g ↔ f - g =ᶠ[l] 0
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_sub`：condExp_sub (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m]
-/
theorem martingale_of_condExp_sub_eq_zero_nat [CompleteSpace E] [IsFiniteMeasure μ] {f : ℕ → Ω → E}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, μ[f (i + 1) - f i | 𝒢 i] =ᵐ[μ] 0) : Martingale f 𝒢 μ := by
  refine martingale_nat hadp hint fun i ↦ ?_
  rw [← condExp_of_stronglyMeasurable (𝒢.le _) (hadp _) (hint _),
    eventuallyEq_comm, eventuallyEq_iff_sub]
  exact EventuallyEq.trans (condExp_sub (hint _) (hint _) _).symm (hf i)

/-- A predictable martingale is a.e. equal to its initial state. -/
/-
**MeasureTheory.Martingale.eq_zero_of_predictable** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Martingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {𝒢 : Mea
sureTheory.Filtration ℕ m0} [CompleteSpace E]   [MeasureTheory.SigmaFiniteFiltra
tion μ 𝒢] {f : ℕ → Ω → E},   MeasureTheory.Martingale f 𝒢 μ → (MeasureTheory.Str
onglyAdapted 𝒢 fun n => f (n + 1)) → ∀ (n : ℕ), f n =ᵐ[μ] f 0
参数：MeasureTheory.StronglyAdapted 𝒢 fun n => f (n + 1)；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_stronglyMeasurable`：condExp_of_stronglyMeasurab
le (hm : m <= m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α -> E} (hf : StronglyMea
surable[m] f) (hfi : Integrable f…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.Martingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} {ι 
: Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Me
asure Ω} [inst_1 : Normed…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
A predictable martingale is a.e. equal to its initial state.
-/
theorem Martingale.eq_zero_of_predictable [CompleteSpace E] [SigmaFiniteFiltration μ 𝒢]
    {f : ℕ → Ω → E}
    (hfmgle : Martingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n => f (n + 1)) (n : ℕ) :
    f n =ᵐ[μ] f 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ((Germ.coe_eq.mp (congr_arg Germ.ofFun <| condExp_of_stronglyMeasurable (𝒢.le _) (hfadp _)
      (hfmgle.integrable _))).symm.trans (hfmgle.2 k (k + 1) k.le_succ)).trans ih

section IsStronglyPredictable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A predictable submartingale is a.e. greater than or equal to its initial state. -/
/-
**MeasureTheory.Submartingale.zero_le_of_predictable'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢
 : MeasureTheory.Filtration ℕ m0}   {E : Type u_4} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] [inst_2 : Preorder E]   [MeasureTheory.SigmaFiniteFi
ltration μ 𝒢] {f : ℕ → Ω → E},   MeasureTheory.Submartingale f 𝒢 μ → MeasureTheo
ry.IsStronglyPredictable 𝒢 f → ∀ (n : ℕ), f 0 ≤ᵐ[μ] f n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.zero_le_of_predictable`：∀ {Ω : Type u_1} {E 
: Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Norme
dAddCommGroup E]   [inst_1 : NormedSpace…
· 使用引理 `MeasureTheory.IsStronglyPredictable.measurable_add_one`：measurable_add_o
ne {𝓕 : Filtration Nat m} {u : Nat -> Ω -> E} (h𝓕 : IsStronglyPredictable 𝓕 u) (
n : Nat) : StronglyMeasurable[𝓕 n] (u (n + 1…

--- 原说明 ---
A predictable submartingale is a.e. greater than or equal to its initial state.
-/
theorem Submartingale.zero_le_of_predictable' [Preorder E] [SigmaFiniteFiltration μ 𝒢]
    {f : ℕ → Ω → E} (hfmgle : Submartingale f 𝒢 μ) (hf : IsStronglyPredictable 𝒢 f) (n : ℕ) :
    f 0 ≤ᵐ[μ] f n :=
  zero_le_of_predictable hfmgle hf.measurable_add_one n

/-- A predictable supermartingale is a.e. less than or equal to its initial state. -/
/-
**MeasureTheory.Supermartingale.le_zero_of_predictable'** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Supermartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢
 : MeasureTheory.Filtration ℕ m0}   {E : Type u_4} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] [inst_2 : Preorder E]   [MeasureTheory.SigmaFiniteFi
ltration μ 𝒢] {f : ℕ → Ω → E},   MeasureTheory.Supermartingale f 𝒢 μ → MeasureTh
eory.IsStronglyPredictable 𝒢 f → ∀ (n : ℕ), f n ≤ᵐ[μ] f 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Supermartingale.le_zero_of_predictable`：∀ {Ω : Type u_1} {
E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Nor
medAddCommGroup E]   [inst_1 : NormedSpace…
· 使用引理 `MeasureTheory.IsStronglyPredictable.measurable_add_one`：measurable_add_o
ne {𝓕 : Filtration Nat m} {u : Nat -> Ω -> E} (h𝓕 : IsStronglyPredictable 𝓕 u) (
n : Nat) : StronglyMeasurable[𝓕 n] (u (n + 1…

--- 原说明 ---
A predictable supermartingale is a.e. less than or equal to its initial state.
-/
theorem Supermartingale.le_zero_of_predictable' [Preorder E] [SigmaFiniteFiltration μ 𝒢]
    {f : ℕ → Ω → E} (hfmgle : Supermartingale f 𝒢 μ) (hfadp : IsStronglyPredictable 𝒢 f)
    (n : ℕ) : f n ≤ᵐ[μ] f 0 :=
  le_zero_of_predictable hfmgle hfadp.measurable_add_one n

/-- A predictable martingale is a.e. equal to its initial state. -/
/-
**MeasureTheory.Martingale.eq_zero_of_predictable'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Martingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢
 : MeasureTheory.Filtration ℕ m0}   {E : Type u_4} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] [CompleteSpace E]   [MeasureTheory.SigmaFiniteFiltra
tion μ 𝒢] {f : ℕ → Ω → E},   MeasureTheory.Martingale f 𝒢 μ → MeasureTheory.IsSt
ronglyPredictable 𝒢 f → ∀ (n : ℕ), f n =ᵐ[μ] f 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Martingale.eq_zero_of_predictable`：∀ {Ω : Type u_1} {E : T
ype u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : NormedAd
dCommGroup E]   [inst_1 : NormedSpace…
· 使用引理 `MeasureTheory.IsStronglyPredictable.measurable_add_one`：measurable_add_o
ne {𝓕 : Filtration Nat m} {u : Nat -> Ω -> E} (h𝓕 : IsStronglyPredictable 𝓕 u) (
n : Nat) : StronglyMeasurable[𝓕 n] (u (n + 1…

--- 原说明 ---
A predictable martingale is a.e. equal to its initial state.
-/
theorem Martingale.eq_zero_of_predictable' [CompleteSpace E] [SigmaFiniteFiltration μ 𝒢]
    {f : ℕ → Ω → E}
    (hfmgle : Martingale f 𝒢 μ) (hfadp : IsStronglyPredictable 𝒢 f) (n : ℕ) : f n =ᵐ[μ] f 0 :=
  eq_zero_of_predictable hfmgle hfadp.measurable_add_one n

end IsStronglyPredictable

namespace Submartingale

/-
**MeasureTheory.Submartingale.integrable_stoppedValue** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {𝒢 : Mea
sureTheory.Filtration ℕ m0} [inst_2 : LE E] {f : ℕ → Ω → E},   MeasureTheory.Sub
martingale f 𝒢 μ →     ∀ {τ : Ω → ℕ∞},       MeasureTheory.IsStoppingTime 𝒢 τ → 
        ∀ {N : ℕ}, (∀ (ω : Ω), τ ω ≤ ↑N) → MeasureTheory.Integrable (MeasureTheo
ry.stoppedValue f τ) μ
参数：∀ (ω : Ω), τ ω ≤ ↑N；MeasureTheory.stoppedValue f τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_stoppedValue`：integrable_stoppedValue [LocallyF
initeOrderBot ι] (hτ : IsStoppingTime ℱ τ) (hu : forall n, Integrable (u n) μ) {
N : ι} (hbdd : forall ω, τ …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
-/
protected theorem integrable_stoppedValue [LE E] {f : ℕ → Ω → E} (hf : Submartingale f 𝒢 μ)
    {τ : Ω → ℕ∞} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue f τ) μ :=
  integrable_stoppedValue ℕ hτ hf.integrable hbdd

end Submartingale

section SumSMul

variable [CompleteSpace E] [PartialOrder E] [IsOrderedModule ℝ E] [ClosedIciTopology E]
  [IsOrderedAddMonoid E]

/-
**MeasureTheory.Submartingale.sum_smul_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {𝒢 : Mea
sureTheory.Filtration ℕ m0} [CompleteSpace E] [inst_3 : PartialOrder E]   [IsOrd
eredModule ℝ E] [ClosedIciTopology E] [IsOrderedAddMonoid E] [MeasureTheory.IsFi
niteMeasure μ] {R : ℝ}   {f : ℕ → Ω → E} {ξ : ℕ → Ω → ℝ},   MeasureTheory.Submar
tingale f 𝒢 μ →     MeasureTheory.StronglyAdapted 𝒢 ξ →       (∀ (n : ℕ) (ω : Ω)
, ξ n ω ≤ R) →         (∀ (n : ℕ) (ω : Ω), 0 ≤ ξ n ω) →           MeasureTheory.
Submartingale (fun n => ∑ k ∈ Finset.range n, ξ k • (f (k + 1) - f k)) 𝒢 μ
参数：∀ (n : ℕ) (ω : Ω), ξ n ω ≤ R；∀ (n : ℕ) (ω : Ω), 0 ≤ ξ n ω；fun n => ∑ k ∈ Fins
et.range n, ξ k • (f (k + 1) - f k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.integrable_finsetSum'`：integrable_finsetSum' {ι} (s : Fins
et ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (
∑ i in s, f i) μ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.bdd_smul`：∀ {α : Type u_1} {β : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]  
 {𝕜 : Type u_8} [inst_1…
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyAdapted.stronglyMeasurable`：∀ {Ω : Type u_1} {ι : 
Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtrat
ion ι m}   {β : ι → Type u_3} [inst_1 …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Finset.stronglyMeasurable_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : A
ddCommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousAdd M]   {m : Measurabl
eSpace α} {ι : Type…
· 使用定理 `MeasureTheory.StronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2} {
mα : MeasurableSpace α} [inst : TopologicalSpace β] {𝕜 : Type u_5}   [inst_1 : T
opologicalSpace 𝕜] [inst_2 …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.StronglyAdapted.stronglyMeasurable_le`：stronglyMeasurable_
le {i j : ι} (hf : StronglyAdapted f u) (hij : i <= j) : StronglyMeasurable[f j]
 (u i)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `MeasureTheory.StronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Sub β
]   [ContinuousSub β],   M…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `MeasureTheory.submartingale_of_condExp_sub_nonneg_nat`：submartingale_of_
condExp_sub_nonneg_nat [IsFiniteMeasure μ] {f : Nat -> Ω -> E} (hadp : StronglyA
dapted 𝒢 f) (hint : forall i, Integrable (f…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_Ico_eq_sub`：∀ {δ : Type u_4} [inst : AddCommGroup δ] (f : ℕ →
 δ) {m n : ℕ},   m ≤ n → ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range n, f k -
 ∑ k ∈ Fins…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
（共 44 条，此处仅展示前 30 条）
-/
theorem Submartingale.sum_smul_sub [IsFiniteMeasure μ] {R : ℝ}
    {f : ℕ → Ω → E} {ξ : ℕ → Ω → ℝ}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 ξ) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ k • (f (k + 1) - f k)) 𝒢 μ := by
  have hξbdd : ∀ i, ∃ C, ∀ ω, ‖ξ i ω‖ ≤ C := fun i =>
    ⟨R, fun ω => (abs_of_nonneg (hnonneg i ω)).trans_le (hbdd i ω)⟩
  choose C hC using hξbdd
  have hint : ∀ m, Integrable (∑ k ∈ Finset.range m, ξ k • (f (k + 1) - f k)) μ := fun m =>
      integrable_finsetSum' _ fun i _ => Integrable.bdd_smul
        ((hf.integrable _).sub (hf.integrable _)) (C i)
        hξ.stronglyMeasurable.aestronglyMeasurable (ae_of_all _ (hC i))
  have hadp : StronglyAdapted 𝒢 fun n => ∑ k ∈ Finset.range n, ξ k • (f (k + 1) - f k) := by
    intro m
    refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact (hξ.stronglyMeasurable_le hi.le).smul
      ((hf.stronglyAdapted.stronglyMeasurable_le (Nat.succ_le_of_lt hi)).sub
        (hf.stronglyAdapted.stronglyMeasurable_le hi.le))
  refine submartingale_of_condExp_sub_nonneg_nat hadp hint fun i => ?_
  simp only [← Finset.sum_Ico_eq_sub _ (Nat.le_succ _), Nat.succ_eq_add_one, Nat.Ico_succ_singleton,
    Finset.sum_singleton]
  filter_upwards [hf.condExp_sub_nonneg i.le_succ,
    condExp_smul_of_aestronglyMeasurable_left (hξ i).aestronglyMeasurable
      (((hf.integrable (i + 1)).sub (hf.integrable i)).bdd_smul
      (C i) hξ.stronglyMeasurable.aestronglyMeasurable (ae_of_all _ (hC i)))
      ((hf.integrable _).sub (hf.integrable _))] with ω hω1 hω2
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, Pi.smul_apply'] at hω1 hω2 ⊢
  grw [← smul_zero (0 : ℝ), hnonneg i ω, hω1, hω2]
  · exact hnonneg i ω
  · simp

/-- Given a discrete submartingale `f` and a predictable process `ξ` (i.e. `ξ (n + 1)` is strongly
adapted) the process defined by `fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)` is
also a submartingale. -/
/-
**MeasureTheory.Submartingale.sum_smul_sub'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {m0 : MeasurableSpace Ω} {μ : MeasureTheor
y.Measure Ω} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] {𝒢 : Mea
sureTheory.Filtration ℕ m0} [CompleteSpace E] [inst_3 : PartialOrder E]   [IsOrd
eredModule ℝ E] [ClosedIciTopology E] [IsOrderedAddMonoid E] [MeasureTheory.IsFi
niteMeasure μ] {R : ℝ}   {ξ : ℕ → Ω → ℝ} {f : ℕ → Ω → E},   MeasureTheory.Submar
tingale f 𝒢 μ →     (MeasureTheory.StronglyAdapted 𝒢 fun n => ξ (n + 1)) →      
 (∀ (n : ℕ) (ω : Ω), ξ n ω ≤ R) →         (∀ (n : ℕ) (ω : Ω), 0 ≤ ξ n ω) →      
     MeasureTheory.Submartingale (fun n => ∑ k ∈ Finset.range n, ξ (k + 1) • (f 
(k + 1) - f k)) 𝒢 μ
参数：MeasureTheory.StronglyAdapted 𝒢 fun n => ξ (n + 1)；∀ (n : ℕ) (ω : Ω), ξ n ω ≤
 R；∀ (n : ℕ) (ω : Ω), 0 ≤ ξ n ω；fun n => ∑ k ∈ Finset.range n, ξ (k + 1) • (f (k
 + 1) - f k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.sum_smul_sub`：∀ {Ω : Type u_1} {E : Type u_2
} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : NormedAddCommGr
oup E]   [inst_1 : NormedSpace…

--- 原说明 ---
Given a discrete submartingale `f` and a predictable process `ξ` (i.e. `ξ (n + 1
)` is strongly
adapted) the process defined by `fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (
k + 1) - f k)` is
also a submartingale.
-/
theorem Submartingale.sum_smul_sub' [IsFiniteMeasure μ] {R : ℝ} {ξ : ℕ → Ω → ℝ} {f : ℕ → Ω → E}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 fun n => ξ (n + 1)) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ (k + 1) • (f (k + 1) - f k)) 𝒢 μ :=
  hf.sum_smul_sub hξ (fun _ => hbdd _) fun _ => hnonneg _
/-
**MeasureTheory.Submartingale.sum_mul_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢
 : MeasureTheory.Filtration ℕ m0}   [MeasureTheory.IsFiniteMeasure μ] {R : ℝ} {ξ
 f : ℕ → Ω → ℝ},   MeasureTheory.Submartingale f 𝒢 μ →     MeasureTheory.Strongl
yAdapted 𝒢 ξ →       (∀ (n : ℕ) (ω : Ω), ξ n ω ≤ R) →         (∀ (n : ℕ) (ω : Ω)
, 0 ≤ ξ n ω) →           MeasureTheory.Submartingale (fun n => ∑ k ∈ Finset.rang
e n, ξ k * (f (k + 1) - f k)) 𝒢 μ
参数：∀ (n : ℕ) (ω : Ω), ξ n ω ≤ R；∀ (n : ℕ) (ω : Ω), 0 ≤ ξ n ω；fun n => ∑ k ∈ Fins
et.range n, ξ k * (f (k + 1) - f k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.sum_smul_sub`：∀ {Ω : Type u_1} {E : Type u_2
} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : NormedAddCommGr
oup E]   [inst_1 : NormedSpace…
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem Submartingale.sum_mul_sub [IsFiniteMeasure μ] {R : ℝ} {ξ f : ℕ → Ω → ℝ}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 ξ) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ k * (f (k + 1) - f k)) 𝒢 μ :=
  hf.sum_smul_sub hξ hbdd hnonneg

/-- Given a discrete submartingale `f` and a predictable process `ξ` (i.e. `ξ (n + 1)` is strongly
adapted) the process defined by `fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)` is
also a submartingale. -/
/-
**MeasureTheory.Submartingale.sum_mul_sub'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢
 : MeasureTheory.Filtration ℕ m0}   [MeasureTheory.IsFiniteMeasure μ] {R : ℝ} {ξ
 f : ℕ → Ω → ℝ},   MeasureTheory.Submartingale f 𝒢 μ →     (MeasureTheory.Strong
lyAdapted 𝒢 fun n => ξ (n + 1)) →       (∀ (n : ℕ) (ω : Ω), ξ n ω ≤ R) →        
 (∀ (n : ℕ) (ω : Ω), 0 ≤ ξ n ω) →           MeasureTheory.Submartingale (fun n =
> ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)) 𝒢 μ
参数：MeasureTheory.StronglyAdapted 𝒢 fun n => ξ (n + 1)；∀ (n : ℕ) (ω : Ω), ξ n ω ≤
 R；∀ (n : ℕ) (ω : Ω), 0 ≤ ξ n ω；fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k
 + 1) - f k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.sum_smul_sub'`：∀ {Ω : Type u_1} {E : Type u_
2} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : NormedAddCommG
roup E]   [inst_1 : NormedSpace…
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
Given a discrete submartingale `f` and a predictable process `ξ` (i.e. `ξ (n + 1
)` is strongly
adapted) the process defined by `fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (
k + 1) - f k)` is
also a submartingale.
-/
theorem Submartingale.sum_mul_sub' [IsFiniteMeasure μ] {R : ℝ} {ξ f : ℕ → Ω → ℝ}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 fun n => ξ (n + 1)) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)) 𝒢 μ :=
  hf.sum_smul_sub' hξ hbdd hnonneg

end SumSMul

end Nat

end MeasureTheory

