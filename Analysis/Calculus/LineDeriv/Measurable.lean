/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Measurability of the line derivative

We prove in `measurable_lineDeriv` that the line derivative of a function (with respect to a
locally compact scalar field) is measurable, provided the function is continuous.

In `measurable_lineDeriv_uncurry`, assuming additionally that the source space is second countable,
we show that `(x, v) ↦ lineDeriv 𝕜 f x v` is also measurable.

An assumption such as continuity is necessary, as otherwise one could alternate in a non-measurable
way between differentiable and non-differentiable functions along the various lines
directed by `v`.
-/

public section

open MeasureTheory

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E → F} {v : E}

/-!
Measurability of the line derivative `lineDeriv 𝕜 f x v` with respect to a fixed direction `v`.
-/

/-
**measurableSet_lineDifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_lineDifferentiableAt (hf : Continuous f) : MeasurableSet {x 
: E | LineDifferentiableAt 𝕜 f x v}
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
· 使用定理 `measurableSet_of_differentiableAt_with_param`：measurableSet_of_different
iableAt_with_param (hf : Continuous f.uncurry) : MeasurableSet {p : α × E | Diff
erentiableAt 𝕜 (f p.1) p.2}
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α

--- 原说明 ---
Measurability of the line derivative `lineDeriv 𝕜 f x v` with respect to a fixed
 direction `v`.
-/
theorem measurableSet_lineDifferentiableAt (hf : Continuous f) :
    MeasurableSet {x : E | LineDifferentiableAt 𝕜 f x v} := by
  borelize 𝕜
  let g : E → 𝕜 → F := fun x t ↦ f (x + t • v)
  have hg : Continuous g.uncurry := by fun_prop
  exact measurable_prodMk_right (measurableSet_of_differentiableAt_with_param 𝕜 hg)
/-
**measurable_lineDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_lineDeriv [MeasurableSpace F] [BorelSpace F] (hf : Continuous f
) : Measurable (fun x => lineDeriv 𝕜 f x v)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_deriv_with_param`：measurable_deriv_with_param [LocallyCompact
Space 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F] [Borel
Space F] {f : α -…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
theorem measurable_lineDeriv [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f) : Measurable (fun x ↦ lineDeriv 𝕜 f x v) := by
  borelize 𝕜
  let g : E → 𝕜 → F := fun x t ↦ f (x + t • v)
  have hg : Continuous g.uncurry := by fun_prop
  exact (measurable_deriv_with_param hg).comp measurable_prodMk_right
/-
**stronglyMeasurable_lineDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stronglyMeasurable_lineDeriv [SecondCountableTopologyEither E F] (hf : Con
tinuous f) : StronglyMeasurable (fun x => lineDeriv 𝕜 f x v)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `stronglyMeasurable_deriv_with_param`：stronglyMeasurable_deriv_with_param
 [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [h : Secon
dCountableTopologyEither …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
theorem stronglyMeasurable_lineDeriv [SecondCountableTopologyEither E F] (hf : Continuous f) :
    StronglyMeasurable (fun x ↦ lineDeriv 𝕜 f x v) := by
  borelize 𝕜
  let g : E → 𝕜 → F := fun x t ↦ f (x + t • v)
  have hg : Continuous g.uncurry := by fun_prop
  exact (stronglyMeasurable_deriv_with_param hg).comp_measurable measurable_prodMk_right
/-
**aemeasurable_lineDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_lineDeriv [MeasurableSpace F] [BorelSpace F] (hf : Continuous
 f) (μ : Measure E) : AEMeasurable (fun x => lineDeriv 𝕜 f x v) μ
参数：hf : Continuous f；μ : Measure E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_lineDeriv`：measurable_lineDeriv [MeasurableSpace F] [BorelSpa
ce F] (hf : Continuous f) : Measurable (fun x => lineDeriv 𝕜 f x v)
-/
theorem aemeasurable_lineDeriv [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f) (μ : Measure E) :
    AEMeasurable (fun x ↦ lineDeriv 𝕜 f x v) μ :=
  (measurable_lineDeriv hf).aemeasurable
/-
**aestronglyMeasurable_lineDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aestronglyMeasurable_lineDeriv [SecondCountableTopologyEither E F] (hf : C
ontinuous f) (μ : Measure E) : AEStronglyMeasurable (fun x => lineDeriv 𝕜 f x v)
 μ
参数：hf : Continuous f；μ : Measure E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `stronglyMeasurable_lineDeriv`：stronglyMeasurable_lineDeriv [SecondCounta
bleTopologyEither E F] (hf : Continuous f) : StronglyMeasurable (fun x => lineDe
riv 𝕜 f x v)
-/
theorem aestronglyMeasurable_lineDeriv [SecondCountableTopologyEither E F]
    (hf : Continuous f) (μ : Measure E) :
    AEStronglyMeasurable (fun x ↦ lineDeriv 𝕜 f x v) μ :=
  (stronglyMeasurable_lineDeriv hf).aestronglyMeasurable

/-!
Measurability of the line derivative `lineDeriv 𝕜 f x v` when varying both `x` and `v`. For this,
we need an additional second countability assumption on `E` to make sure that open sets are
measurable in `E × E`.
-/

variable [SecondCountableTopology E]

/-
**measurableSet_lineDifferentiableAt_uncurry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_lineDifferentiableAt_uncurry (hf : Continuous f) : Measurabl
eSet {p : E × E | LineDifferentiableAt 𝕜 f p.1 p.2}
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `measurableSet_of_differentiableAt_with_param`：measurableSet_of_different
iableAt_with_param (hf : Continuous f.uncurry) : MeasurableSet {p : α × E | Diff
erentiableAt 𝕜 (f p.1) p.2}
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
theorem measurableSet_lineDifferentiableAt_uncurry (hf : Continuous f) :
    MeasurableSet {p : E × E | LineDifferentiableAt 𝕜 f p.1 p.2} := by
  borelize 𝕜
  let g : (E × E) → 𝕜 → F := fun p t ↦ f (p.1 + t • p.2)
  have : Continuous g.uncurry :=
    hf.comp <| (continuous_fst.comp continuous_fst).add
    <| continuous_snd.smul (continuous_snd.comp continuous_fst)
  have M_meas : MeasurableSet {q : (E × E) × 𝕜 | DifferentiableAt 𝕜 (g q.1) q.2} :=
    measurableSet_of_differentiableAt_with_param 𝕜 this
  exact measurable_prodMk_right M_meas
/-
**measurable_lineDeriv_uncurry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_lineDeriv_uncurry [MeasurableSpace F] [BorelSpace F] (hf : Cont
inuous f) : Measurable (fun (p : E × E) => lineDeriv 𝕜 f p.1 p.2)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_deriv_with_param`：measurable_deriv_with_param [LocallyCompact
Space 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F] [Borel
Space F] {f : α -…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
theorem measurable_lineDeriv_uncurry [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f) : Measurable (fun (p : E × E) ↦ lineDeriv 𝕜 f p.1 p.2) := by
  borelize 𝕜
  let g : (E × E) → 𝕜 → F := fun p t ↦ f (p.1 + t • p.2)
  have : Continuous g.uncurry :=
    hf.comp <| (continuous_fst.comp continuous_fst).add
    <| continuous_snd.smul (continuous_snd.comp continuous_fst)
  exact (measurable_deriv_with_param this).comp measurable_prodMk_right
/-
**stronglyMeasurable_lineDeriv_uncurry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stronglyMeasurable_lineDeriv_uncurry (hf : Continuous f) : StronglyMeasura
ble (fun (p : E × E) => lineDeriv 𝕜 f p.1 p.2)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `stronglyMeasurable_deriv_with_param`：stronglyMeasurable_deriv_with_param
 [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [h : Secon
dCountableTopologyEither …
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
theorem stronglyMeasurable_lineDeriv_uncurry (hf : Continuous f) :
    StronglyMeasurable (fun (p : E × E) ↦ lineDeriv 𝕜 f p.1 p.2) := by
  borelize 𝕜
  let g : (E × E) → 𝕜 → F := fun p t ↦ f (p.1 + t • p.2)
  have : Continuous g.uncurry :=
    hf.comp <| (continuous_fst.comp continuous_fst).add
    <| continuous_snd.smul (continuous_snd.comp continuous_fst)
  exact (stronglyMeasurable_deriv_with_param this).comp_measurable measurable_prodMk_right
/-
**aemeasurable_lineDeriv_uncurry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_lineDeriv_uncurry [MeasurableSpace F] [BorelSpace F] (hf : Co
ntinuous f) (μ : Measure (E × E)) : AEMeasurable (fun (p : E × E) => lineDeriv 𝕜
 f p.1 p.2) μ
参数：hf : Continuous f；μ : Measure (E × E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_lineDeriv_uncurry`：measurable_lineDeriv_uncurry [MeasurableSp
ace F] [BorelSpace F] (hf : Continuous f) : Measurable (fun (p : E × E) => lineD
eriv 𝕜 f p.1 p.2)
-/
theorem aemeasurable_lineDeriv_uncurry [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f) (μ : Measure (E × E)) :
    AEMeasurable (fun (p : E × E) ↦ lineDeriv 𝕜 f p.1 p.2) μ :=
  (measurable_lineDeriv_uncurry hf).aemeasurable
/-
**aestronglyMeasurable_lineDeriv_uncurry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aestronglyMeasurable_lineDeriv_uncurry (hf : Continuous f) (μ : Measure (E
 × E)) : AEStronglyMeasurable (fun (p : E × E) => lineDeriv 𝕜 f p.1 p.2) μ
参数：hf : Continuous f；μ : Measure (E × E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `stronglyMeasurable_lineDeriv_uncurry`：stronglyMeasurable_lineDeriv_uncur
ry (hf : Continuous f) : StronglyMeasurable (fun (p : E × E) => lineDeriv 𝕜 f p.
1 p.2)
-/
theorem aestronglyMeasurable_lineDeriv_uncurry (hf : Continuous f) (μ : Measure (E × E)) :
    AEStronglyMeasurable (fun (p : E × E) ↦ lineDeriv 𝕜 f p.1 p.2) μ :=
  (stronglyMeasurable_lineDeriv_uncurry hf).aestronglyMeasurable
