/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of scalar products
-/

public section


variable {α : Type*} {𝕜 : Type*} {E : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

@[fun_prop]
/-
**Measurable.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.inner {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasura
bleSpace E] [SecondCountableTopology E] {f g : α -> E} (hf : Measurable f) (hg :
 Measurable g) : Measurable fun t => ⟪f t, g t⟫
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable2`：Continuous.measurable2 [SecondCountableTopologyE
ither α β] {f : δ -> α} {g : δ -> β} {c : α -> β -> γ} (h : Continuous fun p : α
 × β => c p.…
· 使用定理 `RCLike.borelSpace`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], BorelSpace 𝕜
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
-/
theorem Measurable.inner {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun t => ⟪f t, g t⟫ :=
  Continuous.measurable2 continuous_inner hf hg

@[fun_prop]
/-
**Measurable.const_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.const_inner {_ : MeasurableSpace α} [MeasurableSpace E] [OpensM
easurableSpace E] [SecondCountableTopology E] {c : E} {f : α -> E} (hf : Measura
ble f) : Measurable fun t => ⟪c, f t⟫
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.inner`：Measurable.inner {_ : MeasurableSpace α} [MeasurableSp
ace E] [OpensMeasurableSpace E] [SecondCountableTopology E] {f g : α -> E} (hf :
 Measu…
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem Measurable.const_inner {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {c : E} {f : α → E} (hf : Measurable f) :
    Measurable fun t => ⟪c, f t⟫ :=
  Measurable.inner measurable_const hf

@[fun_prop]
/-
**Measurable.inner_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.inner_const {_ : MeasurableSpace α} [MeasurableSpace E] [OpensM
easurableSpace E] [SecondCountableTopology E] {c : E} {f : α -> E} (hf : Measura
ble f) : Measurable fun t => ⟪f t, c⟫
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.inner`：Measurable.inner {_ : MeasurableSpace α} [MeasurableSp
ace E] [OpensMeasurableSpace E] [SecondCountableTopology E] {f g : α -> E} (hf :
 Measu…
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem Measurable.inner_const {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {c : E} {f : α → E} (hf : Measurable f) :
    Measurable fun t => ⟪f t, c⟫ :=
  Measurable.inner hf measurable_const

@[fun_prop]
/-
**AEMeasurable.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.inner {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasu
rableSpace E] [SecondCountableTopology E] {μ : MeasureTheory.Measure α} {f g : α
 -> E} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => 
⟪f x, g x⟫) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `Measurable.inner`：Measurable.inner {_ : MeasurableSpace α} [MeasurableSp
ace E] [OpensMeasurableSpace E] [SecondCountableTopology E] {f g : α -> E} (hf :
 Measu…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
-/
theorem AEMeasurable.inner {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {μ : MeasureTheory.Measure α} {f g : α → E}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => ⟪f x, g x⟫) μ := by
  fun_prop

@[fun_prop]
/-
**AEMeasurable.const_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.const_inner {m : MeasurableSpace α} [MeasurableSpace E] [Open
sMeasurableSpace E] [SecondCountableTopology E] {μ : MeasureTheory.Measure α} {f
 : α -> E} {c : E} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ⟪c, f x⟫) μ
参数：hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.inner`：AEMeasurable.inner {m : MeasurableSpace α} [Measurab
leSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E] {μ : MeasureTheo
ry.Measu…
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
-/
theorem AEMeasurable.const_inner {m : MeasurableSpace α} [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    {μ : MeasureTheory.Measure α} {f : α → E} {c : E} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => ⟪c, f x⟫) μ :=
  AEMeasurable.inner aemeasurable_const hf

@[fun_prop]
/-
**AEMeasurable.inner_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.inner_const {m : MeasurableSpace α} [MeasurableSpace E] [Open
sMeasurableSpace E] [SecondCountableTopology E] {μ : MeasureTheory.Measure α} {f
 : α -> E} {c : E} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ⟪f x, c⟫) μ
参数：hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.inner`：AEMeasurable.inner {m : MeasurableSpace α} [Measurab
leSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E] {μ : MeasureTheo
ry.Measu…
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
-/
theorem AEMeasurable.inner_const {m : MeasurableSpace α} [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    {μ : MeasureTheory.Measure α} {f : α → E} {c : E} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => ⟪f x, c⟫) μ :=
  AEMeasurable.inner hf aemeasurable_const
