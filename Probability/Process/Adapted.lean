/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Filtration
public import Mathlib.Topology.Instances.Discrete

/-!
# Adapted and progressively measurable processes

This file defines the related notions of a process `u` being (strongly) `Adapted` or
`Progressive` (progressively measurable) with respect to a filtration `f`, and proves some
basic facts about them.

## Main definitions

* `MeasureTheory.Adapted`: a sequence of functions `u` is said to be adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-measurable
* `MeasureTheory.IsProgressive`: a sequence of functions `u` is said to be progressive with respect
  to a filtration `f` if at each point in time `i`, `u` restricted to `Set.Iic i × Ω` is strongly
  measurable with respect to the product `MeasurableSpace` structure where the σ-algebra used for
  `Ω` is `f i`.
We also provide the following variants, which use `MeasureTheory.StronglyMeasurable` instead
of `Measurable`:
* `MeasureTheory.StronglyAdapted`
* `MeasureTheory.IsStronglyProgressive`

## Main results

* `StronglyAdapted.isStronglyProgressive_of_continuous`: a continuous strongly adapted process is
  strongly progressive.

## Tags

adapted, progressively measurable

-/

@[expose] public section

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι] {f : Filtration ι m}

section Adapted

variable {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {u v : (i : ι) → Ω → β i}

/-- A sequence of functions `u` is adapted to a filtration `f` if for all `i`,
`u i` is `f i`-measurable.

The definition known as `Adapted` before 2026-01-13 is now `StronglyAdapted`. -/
/-
**MeasureTheory.Adapted** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：Adapted (f : Filtration ι m) (u : (i : ι) -> Ω -> β i) : Prop
参数：f : Filtration ι m；u : (i : ι) -> Ω -> β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of functions `u` is adapted to a filtration `f` if for all `i`,
`u i` is `f i`-measurable.

The definition known as `Adapted` before 2026-01-13 is now `StronglyAdapted`.
-/
def Adapted (f : Filtration ι m) (u : (i : ι) → Ω → β i) : Prop :=
  ∀ i : ι, Measurable[f i] (u i)

namespace Adapted

@[to_additive]
/-
**MeasureTheory.Adapted.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Adapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → Me
asurableSpace (β i)] {u v : (i : ι) → Ω → β i} [inst_2 : (i : ι) → Mul (β i)]   
[∀ (i : ι), MeasurableMul₂ (β i)],   MeasureTheory.Adapted f u → MeasureTheory.A
dapted f v → MeasureTheory.Adapted f (u * v)
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i；u * v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
-/
protected theorem mul [∀ i, Mul (β i)] [∀ i, MeasurableMul₂ (β i)]
    (hu : Adapted f u) (hv : Adapted f v) :
    Adapted f (u * v) := fun i => (hu i).mul (hv i)

@[to_additive]
/-
**MeasureTheory.Adapted.div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Adapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → Me
asurableSpace (β i)] {u v : (i : ι) → Ω → β i} [inst_2 : (i : ι) → Div (β i)]   
[∀ (i : ι), MeasurableDiv₂ (β i)],   MeasureTheory.Adapted f u → MeasureTheory.A
dapted f v → MeasureTheory.Adapted f (u / v)
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i；u / v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.div`：Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (h
g : Measurable g) : Measurable (f / g)
-/
protected theorem div [∀ i, Div (β i)] [∀ i, MeasurableDiv₂ (β i)]
    (hu : Adapted f u) (hv : Adapted f v) :
    Adapted f (u / v) := fun i => (hu i).div (hv i)

@[to_additive]
/-
**MeasureTheory.Adapted.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Adapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → Me
asurableSpace (β i)] {u : (i : ι) → Ω → β i} [inst_2 : (i : ι) → Group (β i)]   
[∀ (i : ι), MeasurableInv (β i)], MeasureTheory.Adapted f u → MeasureTheory.Adap
ted f u⁻¹
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.inv`：Measurable.inv (hf : Measurable f) : Measurable f⁻¹
-/
protected theorem inv [∀ i, Group (β i)] [∀ i, MeasurableInv (β i)] (hu : Adapted f u) :
    Adapted f u⁻¹ := fun i => (hu i).inv
/-
**MeasureTheory.Adapted.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Adapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → Me
asurableSpace (β i)] {u : (i : ι) → Ω → β i} {𝕂 : Type u_4}   [inst_2 : Measurab
leSpace 𝕂] [inst_3 : (i : ι) → SMul 𝕂 (β i)] [∀ (i : ι), MeasurableSMul 𝕂 (β i)]
 (c : 𝕂),   MeasureTheory.Adapted f u → MeasureTheory.Adapted f (c • u)
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i；c : 𝕂；c • u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measurable.const_smul`：Measurable.const_smul (hg : Measurable g) (c : M)
 : Measurable (c • g)
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
-/
protected theorem smul {𝕂 : Type*} [MeasurableSpace 𝕂]
    [∀ i, SMul 𝕂 (β i)] [∀ i, MeasurableSMul 𝕂 (β i)] (c : 𝕂) (hu : Adapted f u) :
    Adapted f (c • u) := fun i => (hu i).const_smul c
/-
**MeasureTheory.Adapted.measurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Adap
ted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → Me
asurableSpace (β i)] {u : (i : ι) → Ω → β i} {i : ι},   MeasureTheory.Adapted f 
u → Measurable (u i)
参数：i : ι；β i；i : ι；u i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
protected theorem measurable {i : ι} (hf : Adapted f u) : Measurable[m] (u i) :=
  (hf i).mono (f.le i) (by rfl)
/-
**MeasureTheory.Adapted.measurable_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.A
dapted`。
形式化陈述：measurable_le {i j : ι} (hf : Adapted f u) (hij : i <= j) : Measurable[f j
] (u i)
参数：hf : Adapted f u；hij : i <= j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem measurable_le {i j : ι} (hf : Adapted f u) (hij : i ≤ j) : Measurable[f j] (u i) :=
  (hf i).mono (f.mono hij) (by rfl)

end Adapted

/-
**MeasureTheory.adapted_const'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：adapted_const' (f : Filtration ι m) (x : (i : ι) -> β i) : Adapted f fun i
 _ => x i
参数：f : Filtration ι m；x : (i : ι) -> β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem adapted_const' (f : Filtration ι m) (x : (i : ι) → β i) : Adapted f fun i _ ↦ x i :=
  fun _ ↦ measurable_const
/-
**MeasureTheory.adapted_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：adapted_const {β : Type*} [MeasurableSpace β] (f : Filtration ι m) (x : β)
 : Adapted f fun _ _ => x
参数：f : Filtration ι m；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.adapted_const'`：adapted_const' (f : Filtration ι m) (x : (
i : ι) -> β i) : Adapted f fun i _ => x i
-/
theorem adapted_const {β : Type*} [MeasurableSpace β] (f : Filtration ι m) (x : β) :
    Adapted f fun _ _ ↦ x := adapted_const' _ _

end Adapted

section StronglyAdapted

variable {β : ι → Type*} [∀ i, TopologicalSpace (β i)] {u v : (i : ι) → Ω → β i}

/-- A sequence of functions `u` is strongly adapted to a filtration `f` if for all `i`,
`u i` is `f i`-strongly measurable. -/
/-
**MeasureTheory.StronglyAdapted** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：StronglyAdapted (f : Filtration ι m) (u : (i : ι) -> Ω -> β i) : Prop
参数：f : Filtration ι m；u : (i : ι) -> Ω -> β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of functions `u` is strongly adapted to a filtration `f` if for all `
i`,
`u i` is `f i`-strongly measurable.
-/
def StronglyAdapted (f : Filtration ι m) (u : (i : ι) → Ω → β i) : Prop :=
  ∀ i : ι, StronglyMeasurable[f i] (u i)

namespace StronglyAdapted

@[to_additive]
/-
**MeasureTheory.StronglyAdapted.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Str
onglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → To
pologicalSpace (β i)] {u v : (i : ι) → Ω → β i}   [inst_2 : (i : ι) → Mul (β i)]
 [∀ (i : ι), ContinuousMul (β i)],   MeasureTheory.StronglyAdapted f u → Measure
Theory.StronglyAdapted f v → MeasureTheory.StronglyAdapted f (u * v)
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i；u * v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Mul β
]   [ContinuousMul β],   M…
-/
protected theorem mul [∀ i, Mul (β i)] [∀ i, ContinuousMul (β i)]
    (hu : StronglyAdapted f u) (hv : StronglyAdapted f v) :
    StronglyAdapted f (u * v) := fun i => (hu i).mul (hv i)

@[to_additive sub]
/-
**MeasureTheory.StronglyAdapted.div'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.St
ronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → To
pologicalSpace (β i)] {u v : (i : ι) → Ω → β i}   [inst_2 : (i : ι) → Div (β i)]
 [∀ (i : ι), ContinuousDiv (β i)],   MeasureTheory.StronglyAdapted f u → Measure
Theory.StronglyAdapted f v → MeasureTheory.StronglyAdapted f (u / v)
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i；u / v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.div'`：∀ {α : Type u_1} {β : Type u_2} {
f g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Div 
β]   [ContinuousDiv β],   M…
-/
protected theorem div' [∀ i, Div (β i)] [∀ i, ContinuousDiv (β i)]
    (hu : StronglyAdapted f u) (hv : StronglyAdapted f v) :
    StronglyAdapted f (u / v) := fun i => (hu i).div' (hv i)

@[to_additive]
/-
**MeasureTheory.StronglyAdapted.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Str
onglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → To
pologicalSpace (β i)] {u : (i : ι) → Ω → β i}   [inst_2 : (i : ι) → Group (β i)]
 [∀ (i : ι), ContinuousInv (β i)],   MeasureTheory.StronglyAdapted f u → Measure
Theory.StronglyAdapted f u⁻¹
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.inv`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Inv β] 
  [ContinuousInv β], Measu…
-/
protected theorem inv [∀ i, Group (β i)] [∀ i, ContinuousInv (β i)] (hu : StronglyAdapted f u) :
    StronglyAdapted f u⁻¹ := fun i => (hu i).inv
/-
**MeasureTheory.StronglyAdapted.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.St
ronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → To
pologicalSpace (β i)] {u : (i : ι) → Ω → β i}   [inst_2 : (i : ι) → SMul ℝ (β i)
] [∀ (i : ι), ContinuousConstSMul ℝ (β i)] (c : ℝ),   MeasureTheory.StronglyAdap
ted f u → MeasureTheory.StronglyAdapted f (c • u)
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i；c : ℝ；c • u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {𝕜 : Type 
u_5}   [inst_1 : SMul 𝕜 β] [Conti…
-/
protected theorem smul [∀ i, SMul ℝ (β i)] [∀ i, ContinuousConstSMul ℝ (β i)]
    (c : ℝ) (hu : StronglyAdapted f u) :
    StronglyAdapted f (c • u) := fun i => (hu i).const_smul c

/-- The norm of a strongly adapted process is strongly adapted. -/
/-
**MeasureTheory.StronglyAdapted.norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.St
ronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_4} {u : (i : ι) → Ω → β i
} [inst_1 : (i : ι) → SeminormedAddCommGroup (β i)],   MeasureTheory.StronglyAda
pted f u → MeasureTheory.StronglyAdapted f fun t ω => ‖u t ω‖
参数：i : ι；i : ι；β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.norm`：∀ {α : Type u_1} {x : MeasurableS
pace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   MeasureT
heory.StronglyMeasurable f …

--- 原说明 ---
The norm of a strongly adapted process is strongly adapted.
-/
protected lemma norm {β : ι → Type*} {u : (i : ι) → Ω → β i} [∀ i, SeminormedAddCommGroup (β i)]
    (hu : StronglyAdapted f u) :
    StronglyAdapted f (fun t ω ↦ ‖u t ω‖) := fun t ↦ (hu t).norm
/-
**MeasureTheory.StronglyAdapted.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → To
pologicalSpace (β i)] {u : (i : ι) → Ω → β i} {i : ι},   MeasureTheory.StronglyA
dapted f u → MeasureTheory.StronglyMeasurable (u i)
参数：i : ι；β i；i : ι；u i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
-/
protected theorem stronglyMeasurable {i : ι} (hf : StronglyAdapted f u) :
    StronglyMeasurable[m] (u i) := (hf i).mono (f.le i)
/-
**MeasureTheory.StronglyAdapted.stronglyMeasurable_le** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.StronglyAdapted`。
形式化陈述：stronglyMeasurable_le {i j : ι} (hf : StronglyAdapted f u) (hij : i <= j) 
: StronglyMeasurable[f j] (u i)
参数：hf : StronglyAdapted f u；hij : i <= j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
-/
theorem stronglyMeasurable_le {i j : ι} (hf : StronglyAdapted f u) (hij : i ≤ j) :
    StronglyMeasurable[f j] (u i) := (hf i).mono (f.mono hij)

end StronglyAdapted

/-
**MeasureTheory.StronglyAdapted.adapted** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → To
pologicalSpace (β i)] {u : (i : ι) → Ω → β i}   [mΒ : (i : ι) → MeasurableSpace 
(β i)] [∀ (i : ι), BorelSpace (β i)]   [∀ (i : ι), TopologicalSpace.PseudoMetriz
ableSpace (β i)],   MeasureTheory.StronglyAdapted f u → MeasureTheory.Adapted f 
u
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i；i : ι；β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
-/
theorem StronglyAdapted.adapted [mΒ : ∀ i, MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
    [∀ i, PseudoMetrizableSpace (β i)] (hf : StronglyAdapted f u) :
    Adapted f u := fun _ ↦ (hf _).measurable
/-
**MeasureTheory.Adapted.stronglyAdapted** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Adapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : ι → Type u_3} [inst_1 : (i : ι) → To
pologicalSpace (β i)] {u : (i : ι) → Ω → β i}   [mΒ : (i : ι) → MeasurableSpace 
(β i)] [∀ (i : ι), OpensMeasurableSpace (β i)]   [∀ (i : ι), TopologicalSpace.Ps
eudoMetrizableSpace (β i)] [∀ (i : ι), SecondCountableTopology (β i)],   Measure
Theory.Adapted f u → MeasureTheory.StronglyAdapted f u
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i；i : ι；β i；i : ι；β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
-/
theorem Adapted.stronglyAdapted [mΒ : ∀ i, MeasurableSpace (β i)]
    [∀ i, OpensMeasurableSpace (β i)] [∀ i, PseudoMetrizableSpace (β i)]
    [∀ i, SecondCountableTopology (β i)] (hf : Adapted f u) :
    StronglyAdapted f u := fun _ ↦ (hf _).stronglyMeasurable
/-
**MeasureTheory.stronglyAdapted_iff_adapted** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：stronglyAdapted_iff_adapted [mΒ : forall i, MeasurableSpace (β i)] [forall
 i, BorelSpace (β i)] [forall i, PseudoMetrizableSpace (β i)] [forall i, SecondC
ountableTopology (β i)] : StronglyAdapted f u ↔ Adapted f u
参数：β i；β i；β i；β i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyAdapted.adapted`：∀ {Ω : Type u_1} {ι : Type u_2} {
m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   
{β : ι → Type u_3} [inst_1 …
· 使用定理 `MeasureTheory.Adapted.stronglyAdapted`：∀ {Ω : Type u_1} {ι : Type u_2} {
m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   
{β : ι → Type u_3} [inst_1 …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem stronglyAdapted_iff_adapted [mΒ : ∀ i, MeasurableSpace (β i)]
    [∀ i, BorelSpace (β i)] [∀ i, PseudoMetrizableSpace (β i)]
    [∀ i, SecondCountableTopology (β i)] :
    StronglyAdapted f u ↔ Adapted f u := ⟨fun h ↦ h.adapted, fun h ↦ h.stronglyAdapted⟩
/-
**MeasureTheory.stronglyAdapted_const'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：stronglyAdapted_const' (f : Filtration ι m) (x : (i : ι) -> β i) : Strongl
yAdapted f fun i _ => x i
参数：f : Filtration ι m；x : (i : ι) -> β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
theorem stronglyAdapted_const' (f : Filtration ι m) (x : (i : ι) → β i) :
    StronglyAdapted f fun i _ ↦ x i :=
  fun _ ↦ stronglyMeasurable_const
/-
**MeasureTheory.stronglyAdapted_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stronglyAdapted_const {β : Type*} [TopologicalSpace β] (f : Filtration ι m
) (x : β) : StronglyAdapted f fun _ _ => x
参数：f : Filtration ι m；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyAdapted_const'`：stronglyAdapted_const' (f : Filtra
tion ι m) (x : (i : ι) -> β i) : StronglyAdapted f fun i _ => x i
-/
theorem stronglyAdapted_const {β : Type*} [TopologicalSpace β] (f : Filtration ι m) (x : β) :
    StronglyAdapted f fun _ _ ↦ x :=
  stronglyAdapted_const' _ _

variable (β) in
/-
**MeasureTheory.stronglyAdapted_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stronglyAdapted_zero' [forall i, Zero (β i)] (f : Filtration ι m) : Strong
lyAdapted f (0 : (i : ι) -> Ω -> β i)
参数：β i；f : Filtration ι m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2} {
x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Zero β],   MeasureT
heory.StronglyMeasurable 0
-/
theorem stronglyAdapted_zero' [∀ i, Zero (β i)] (f : Filtration ι m) :
    StronglyAdapted f (0 : (i : ι) → Ω → β i) :=
  fun i ↦ @stronglyMeasurable_zero Ω (β i) (f i) _ _
/-
**MeasureTheory.stronglyAdapted_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：stronglyAdapted_zero (β : Type*) [TopologicalSpace β] [Zero β] (f : Filtra
tion ι m) : StronglyAdapted f (0 : ι -> Ω -> β)
参数：β : Type*；f : Filtration ι m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2} {
x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Zero β],   MeasureT
heory.StronglyMeasurable 0
-/
theorem stronglyAdapted_zero (β : Type*) [TopologicalSpace β] [Zero β] (f : Filtration ι m) :
    StronglyAdapted f (0 : ι → Ω → β) :=
  fun i ↦ @stronglyMeasurable_zero Ω β (f i) _ _
/-
**MeasureTheory.Filtration.stronglyAdapted_natural** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Filtration`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {β : ι → Type u_3}   [inst_1 : (i : ι) → TopologicalSpace (β i)] {u : (i : ι) 
→ Ω → β i}   [inst_2 : ∀ (i : ι), TopologicalSpace.MetrizableSpace (β i)] [mβ : 
(i : ι) → MeasurableSpace (β i)]   [inst_3 : ∀ (i : ι), BorelSpace (β i)] (hum :
 ∀ (i : ι), MeasureTheory.StronglyMeasurable (u i)),   MeasureTheory.StronglyAda
pted (MeasureTheory.Filtration.natural u hum) u
参数：i : ι；β i；i : ι；i : ι；β i；i : ι；β i；i : ι；β i；hum : ∀ (i : ι), MeasureTheory.
StronglyMeasurable (u i)；MeasureTheory.Filtration.natural u hum。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `stronglyMeasurable_iff_measurable_separable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_iff_comap_le`：measurable_iff_comap_le {m₁ : MeasurableSpace α
} {m₂ : MeasurableSpace β} {f : α -> β} : Measurable f ↔ m₂.comap f <= m₁
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.StronglyMeasurable.isSeparable_range`：∀ {α : Type u_1} {β 
: Type u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β],   M
easureTheory.StronglyMeasurable f → Topo…
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem Filtration.stronglyAdapted_natural [∀ i, MetrizableSpace (β i)]
    [mβ : ∀ i, MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
    (hum : ∀ i, StronglyMeasurable[m] (u i)) :
    StronglyAdapted (Filtration.natural u hum) u := by
  intro i
  refine StronglyMeasurable.mono ?_ (le_iSup₂_of_le i (le_refl i) le_rfl)
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨measurable_iff_comap_le.2 le_rfl, (hum i).isSeparable_range⟩

end StronglyAdapted

section Progressive

variable {β : Type*} {u v : ι → Ω → β}

/-- Progressive process. A sequence of functions `u` is said to be progressive with respect
to a filtration `f` if at each point in time `i`, `u` restricted to `Set.Iic i × Ω` is measurable
with respect to the product `MeasurableSpace` structure where the σ-algebra used for `Ω` is `f i`.
The usual definition uses the interval `[0,i]`, which we replace by `Set.Iic i`. We recover the
usual definition for index types `ℝ≥0` or `ℕ`. -/
/-
**MeasureTheory.IsProgressive** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：IsProgressive [MeasurableSpace ι] [MeasurableSpace β] (f : Filtration ι m)
 (u : ι -> Ω -> β) : Prop
参数：f : Filtration ι m；u : ι -> Ω -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Progressive process. A sequence of functions `u` is said to be progressive with 
respect
to a filtration `f` if at each point in time `i`, `u` restricted to `Set.Iic i ×
 Ω` is measurable
with respect to the product `MeasurableSpace` structure where the σ-algebra used
 for `Ω` is `f i`.
The usual definition uses the interval `[0,i]`, which we replace by `Set.Iic i`.
 We recover the
usual definition for index types `ℝ≥0` or `ℕ`.
-/
def IsProgressive [MeasurableSpace ι] [MeasurableSpace β] (f : Filtration ι m)
    (u : ι → Ω → β) : Prop :=
  ∀ i, Measurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2
/-
**MeasureTheory.isProgressive_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：isProgressive_const {mi : MeasurableSpace ι} {mβ : MeasurableSpace β} (f :
 Filtration ι m) (b : β) : IsProgressive f (fun _ _ => b : ι -> Ω -> β)
参数：f : Filtration ι m；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem isProgressive_const {mi : MeasurableSpace ι} {mβ : MeasurableSpace β} (f : Filtration ι m)
    (b : β) : IsProgressive f (fun _ _ => b : ι → Ω → β) :=
  fun _ ↦ by exact measurable_const

namespace IsProgressive

variable {mi : MeasurableSpace ι} {mβ : MeasurableSpace β}

/-
**MeasureTheory.IsProgressive.adapted** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
sProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} {u : ι → Ω → β} {mi : Meas
urableSpace ι} {mβ : MeasurableSpace β},   MeasureTheory.IsProgressive f u → Mea
sureTheory.Adapted f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
protected theorem adapted (h : IsProgressive f u) : Adapted f u := by
  intro i
  have : u i = (fun p : Set.Iic i × Ω => u p.1 p.2) ∘ fun x => (⟨i, Set.mem_Iic.mpr le_rfl⟩, x) :=
    rfl
  rw [this]
  exact (h i).comp measurable_prodMk_left
/-
**MeasureTheory.IsProgressive.comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsPr
ogressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} {u : ι → Ω → β} {mi : Meas
urableSpace ι} {mβ : MeasurableSpace β} {t : ι → Ω → ι},   MeasureTheory.IsProgr
essive f u →     MeasureTheory.IsProgressive f t →       (∀ (i : ι) (ω : Ω), t i
 ω ≤ i) → MeasureTheory.IsProgressive f fun i ω => u (t i ω) ω
参数：∀ (i : ι) (ω : Ω), t i ω ≤ i；t i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
protected theorem comp {t : ι → Ω → ι} (h : IsProgressive f u) (ht : IsProgressive f t)
    (ht_le : ∀ i ω, t i ω ≤ i) :
    IsProgressive f fun i ω => u (t i ω) ω := by
  intro i
  have : (fun p : ↥(Set.Iic i) × Ω => u (t (p.fst : ι) p.snd) p.snd) =
    (fun p : ↥(Set.Iic i) × Ω => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × Ω =>
      (⟨t (p.fst : ι) p.snd, Set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) := rfl
  rw [this]
  exact (h i).comp ((ht i).subtype_mk.prodMk measurable_snd)

section Arithmetic

@[to_additive]
/-
**MeasureTheory.IsProgressive.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsPro
gressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} {u v : ι → Ω → β} {mi : Me
asurableSpace ι} {mβ : MeasurableSpace β} [inst_1 : Mul β]   [MeasurableMul₂ β],
   MeasureTheory.IsProgressive f u →     MeasureTheory.IsProgressive f v → Measu
reTheory.IsProgressive f fun i ω => u i ω * v i ω
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
-/
protected theorem mul [Mul β] [MeasurableMul₂ β] (hu : IsProgressive f u)
    (hv : IsProgressive f v) : IsProgressive f fun i ω ↦  (u i ω * v i ω) :=
  fun i ↦ Measurable.mul (hu i) (hv i)

@[to_additive]
/-
**MeasureTheory.IsProgressive.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IsProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} {mi : MeasurableSpace ι} {
mβ : MeasurableSpace β} {γ : Type u_4} [inst_1 : CommMonoid β]   [MeasurableMul₂
 β] {U : γ → ι → Ω → β} {s : Finset γ},   (∀ c ∈ s, MeasureTheory.IsProgressive 
f (U c)) → MeasureTheory.IsProgressive f fun i ω => ∏ c ∈ s, U c i ω
参数：∀ c ∈ s, MeasureTheory.IsProgressive f (U c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.measurable_prod`：Finset.measurable_prod (s : Finset ι) (hf : fora
ll i in s, Measurable (f i)) : Measurable fun a => ∏ i in s, f i a
-/
protected theorem finsetProd {γ} [CommMonoid β] [MeasurableMul₂ β] {U : γ → ι → Ω → β}
    {s : Finset γ} (h : ∀ c ∈ s, IsProgressive f (U c)) :
    IsProgressive f fun i ω ↦ ∏ c ∈ s, U c i ω :=
  fun i ↦ s.measurable_prod fun c hc ↦ h c hc i

@[to_additive]
/-
**MeasureTheory.IsProgressive.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsPro
gressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} {u : ι → Ω → β} {mi : Meas
urableSpace ι} {mβ : MeasurableSpace β} [inst_1 : Group β] [MeasurableInv β],   
MeasureTheory.IsProgressive f u → MeasureTheory.IsProgressive f fun i ω => (u i 
ω)⁻¹
参数：u i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.inv`：Measurable.inv (hf : Measurable f) : Measurable f⁻¹
-/
protected theorem inv [Group β] [MeasurableInv β] (hu : IsProgressive f u) :
    IsProgressive f fun i ω => (u i ω)⁻¹ := fun i ↦ (hu i).inv

@[to_additive]
/-
**MeasureTheory.IsProgressive.div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsPro
gressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} {u v : ι → Ω → β} {mi : Me
asurableSpace ι} {mβ : MeasurableSpace β} [inst_1 : Group β]   [MeasurableDiv₂ β
],   MeasureTheory.IsProgressive f u →     MeasureTheory.IsProgressive f v → Mea
sureTheory.IsProgressive f fun i ω => u i ω / v i ω
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.div`：Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (h
g : Measurable g) : Measurable (f / g)
-/
protected theorem div [Group β] [MeasurableDiv₂ β] (hu : IsProgressive f u)
    (hv : IsProgressive f v) : IsProgressive f fun i ω ↦ u i ω / v i ω :=
  fun i ↦ Measurable.div (hu i) (hv i)

/-- The norm of a progressive process is progressive. -/
/-
**MeasureTheory.IsProgressive.norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsPr
ogressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} {u : ι → Ω → β} {mi : Meas
urableSpace ι} {mβ : MeasurableSpace β} [inst_1 : NormedAddCommGroup β]   [Opens
MeasurableSpace β], MeasureTheory.IsProgressive f u → MeasureTheory.IsProgressiv
e f fun t ω => ‖u t ω‖
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.norm`：Measurable.norm {f : β -> α} (hf : Measurable f) : Meas
urable fun a => norm (f a)

--- 原说明 ---
The norm of a progressive process is progressive.
-/
protected lemma norm [NormedAddCommGroup β] [OpensMeasurableSpace β] (hu : IsProgressive f u) :
    IsProgressive f fun t ω ↦ ‖u t ω‖ :=
  fun i ↦ by apply @(hu i).norm; infer_instance

end Arithmetic

end IsProgressive

end Progressive

variable {β : Type*} [TopologicalSpace β] {u v : ι → Ω → β}

/-- Strongly progressive process. A sequence of functions `u` is said to be strongly
progressive with respect to a filtration `f` if at each point in time `i`, `u` restricted to
`Set.Iic i × Ω` is strongly measurable with respect to the product `MeasurableSpace` structure
where the σ-algebra used for `Ω` is `f i`.
The usual definition uses the interval `[0,i]`, which we replace by `Set.Iic i`. We recover the
usual definition for index types `ℝ≥0` or `ℕ`. -/
/-
**MeasureTheory.IsStronglyProgressive** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：IsStronglyProgressive [MeasurableSpace ι] (f : Filtration ι m) (u : ι -> Ω
 -> β) : Prop
参数：f : Filtration ι m；u : ι -> Ω -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Strongly progressive process. A sequence of functions `u` is said to be strongly
progressive with respect to a filtration `f` if at each point in time `i`, `u` r
estricted to
`Set.Iic i × Ω` is strongly measurable with respect to the product `MeasurableSp
ace` structure
where the σ-algebra used for `Ω` is `f i`.
The usual definition uses the interval `[0,i]`, which we replace by `Set.Iic i`.
 We recover the
usual definition for index types `ℝ≥0` or `ℕ`.
-/
def IsStronglyProgressive [MeasurableSpace ι] (f : Filtration ι m) (u : ι → Ω → β) : Prop :=
  ∀ i, StronglyMeasurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2
/-
**MeasureTheory.isStronglyProgressive_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：isStronglyProgressive_const [MeasurableSpace ι] (f : Filtration ι m) (b : 
β) : IsStronglyProgressive f (fun _ _ => b : ι -> Ω -> β)
参数：f : Filtration ι m；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
-/
theorem isStronglyProgressive_const [MeasurableSpace ι] (f : Filtration ι m) (b : β) :
    IsStronglyProgressive f (fun _ _ => b : ι → Ω → β) := fun i =>
  @stronglyMeasurable_const _ _ (Subtype.instMeasurableSpace.prod (f i)) _ _

namespace IsStronglyProgressive

variable [MeasurableSpace ι]

/-
**MeasureTheory.IsStronglyProgressive.stronglyAdapted** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] {u : ι → Ω → β} [inst_2 : MeasurableSpace ι],   MeasureTheory.IsStronglyProg
ressive f u → MeasureTheory.StronglyAdapted f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
protected theorem stronglyAdapted (h : IsStronglyProgressive f u) : StronglyAdapted f u := by
  intro i
  have : u i = (fun p : Set.Iic i × Ω => u p.1 p.2) ∘ fun x => (⟨i, Set.mem_Iic.mpr le_rfl⟩, x) :=
    rfl
  rw [this]
  exact (h i).comp_measurable measurable_prodMk_left
/-
**MeasureTheory.IsStronglyProgressive.comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] {u : ι → Ω → β} [inst_2 : MeasurableSpace ι] {t : ι → Ω → ι}   [inst_3 : Top
ologicalSpace ι] [BorelSpace ι] [TopologicalSpace.PseudoMetrizableSpace ι],   Me
asureTheory.IsStronglyProgressive f u →     MeasureTheory.IsStronglyProgressive 
f t →       (∀ (i : ι) (ω : Ω), t i ω ≤ i) → MeasureTheory.IsStronglyProgressive
 f fun i ω => u (t i ω) ω
参数：∀ (i : ι) (ω : Ω), t i ω ≤ i；t i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
protected theorem comp {t : ι → Ω → ι} [TopologicalSpace ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
    (h : IsStronglyProgressive f u) (ht : IsStronglyProgressive f t) (ht_le : ∀ i ω, t i ω ≤ i) :
    IsStronglyProgressive f fun i ω => u (t i ω) ω := by
  intro i
  have : (fun p : ↥(Set.Iic i) × Ω => u (t (p.fst : ι) p.snd) p.snd) =
    (fun p : ↥(Set.Iic i) × Ω => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × Ω =>
      (⟨t (p.fst : ι) p.snd, Set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) := rfl
  rw [this]
  exact (h i).comp_measurable ((ht i).measurable.subtype_mk.prodMk measurable_snd)

section Arithmetic

@[to_additive]
/-
**MeasureTheory.IsStronglyProgressive.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] {u v : ι → Ω → β} [inst_2 : MeasurableSpace ι] [inst_3 : Mul β]   [Continuou
sMul β],   MeasureTheory.IsStronglyProgressive f u →     MeasureTheory.IsStrongl
yProgressive f v → MeasureTheory.IsStronglyProgressive f fun i ω => u i ω * v i 
ω
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Mul β
]   [ContinuousMul β],   M…
-/
protected theorem mul [Mul β] [ContinuousMul β] (hu : IsStronglyProgressive f u)
    (hv : IsStronglyProgressive f v) : IsStronglyProgressive f fun i ω => u i ω * v i ω := fun i =>
  (hu i).mul (hv i)

@[to_additive]
/-
**MeasureTheory.IsStronglyProgressive.finsetProd'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] [inst_2 : MeasurableSpace ι] {γ : Type u_4} [inst_3 : CommMonoid β]   [Conti
nuousMul β] {U : γ → ι → Ω → β} {s : Finset γ},   (∀ c ∈ s, MeasureTheory.IsStro
nglyProgressive f (U c)) → MeasureTheory.IsStronglyProgressive f (∏ c ∈ s, U c)
参数：∀ c ∈ s, MeasureTheory.IsStronglyProgressive f (U c)；∏ c ∈ s, U c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `MeasureTheory.IsStronglyProgressive.mul`：∀ {Ω : Type u_1} {ι : Type u_2}
 {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m} 
  {β : Type u_3} [inst_1 : To…
· 使用定理 `MeasureTheory.isStronglyProgressive_const`：isStronglyProgressive_const [
MeasurableSpace ι] (f : Filtration ι m) (b : β) : IsStronglyProgressive f (fun _
 _ => b : ι -> Ω -> β)
-/
protected theorem finsetProd' {γ} [CommMonoid β] [ContinuousMul β] {U : γ → ι → Ω → β}
    {s : Finset γ} (h : ∀ c ∈ s, IsStronglyProgressive f (U c)) :
    IsStronglyProgressive f (∏ c ∈ s, U c) :=
  Finset.prod_induction U (IsStronglyProgressive f) (fun _ _ => .mul)
    (isStronglyProgressive_const _ 1) h

@[deprecated (since := "2026-04-08")]
protected alias finset_sum' := MeasureTheory.IsStronglyProgressive.finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod' := MeasureTheory.IsStronglyProgressive.finsetProd'

@[to_additive]
/-
**MeasureTheory.IsStronglyProgressive.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] [inst_2 : MeasurableSpace ι] {γ : Type u_4} [inst_3 : CommMonoid β]   [Conti
nuousMul β] {U : γ → ι → Ω → β} {s : Finset γ},   (∀ c ∈ s, MeasureTheory.IsStro
nglyProgressive f (U c)) →     MeasureTheory.IsStronglyProgressive f fun i a => 
∏ c ∈ s, U c i a
参数：∀ c ∈ s, MeasureTheory.IsStronglyProgressive f (U c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.IsStronglyProgressive.finsetProd'`：∀ {Ω : Type u_1} {ι : T
ype u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtrati
on ι m}   {β : Type u_3} [inst_1 : To…
-/
protected theorem finsetProd {γ} [CommMonoid β] [ContinuousMul β] {U : γ → ι → Ω → β}
    {s : Finset γ} (h : ∀ c ∈ s, IsStronglyProgressive f (U c)) :
    IsStronglyProgressive f fun i a => ∏ c ∈ s, U c i a := by
  convert! IsStronglyProgressive.finsetProd' h using 1; ext (i a); simp only [Finset.prod_apply]

@[deprecated (since := "2026-04-08")]
protected alias finset_sum := MeasureTheory.IsStronglyProgressive.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod := MeasureTheory.IsStronglyProgressive.finsetProd

@[to_additive]
/-
**MeasureTheory.IsStronglyProgressive.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] {u : ι → Ω → β} [inst_2 : MeasurableSpace ι] [inst_3 : Group β]   [Continuou
sInv β],   MeasureTheory.IsStronglyProgressive f u → MeasureTheory.IsStronglyPro
gressive f fun i ω => (u i ω)⁻¹
参数：u i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.inv`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Inv β] 
  [ContinuousInv β], Measu…
-/
protected theorem inv [Group β] [ContinuousInv β] (hu : IsStronglyProgressive f u) :
    IsStronglyProgressive f fun i ω => (u i ω)⁻¹ := fun i => (hu i).inv

@[to_additive sub]
/-
**MeasureTheory.IsStronglyProgressive.div'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] {u v : ι → Ω → β} [inst_2 : MeasurableSpace ι] [inst_3 : Group β]   [Continu
ousDiv β],   MeasureTheory.IsStronglyProgressive f u →     MeasureTheory.IsStron
glyProgressive f v → MeasureTheory.IsStronglyProgressive f fun i ω => u i ω / v 
i ω
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.div'`：∀ {α : Type u_1} {β : Type u_2} {
f g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Div 
β]   [ContinuousDiv β],   M…
-/
protected theorem div' [Group β] [ContinuousDiv β] (hu : IsStronglyProgressive f u)
    (hv : IsStronglyProgressive f v) : IsStronglyProgressive f fun i ω => u i ω / v i ω := fun i =>
  (hu i).div' (hv i)

/-- The norm of a strongly progressive process is strongly progressive. -/
/-
**MeasureTheory.IsStronglyProgressive.norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   [inst_1 : MeasurableSpace ι] {β : Type u_
4} {u : ι → Ω → β} [inst_2 : SeminormedAddCommGroup β],   MeasureTheory.IsStrong
lyProgressive f u → MeasureTheory.IsStronglyProgressive f fun t ω => ‖u t ω‖
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.norm`：∀ {α : Type u_1} {x : MeasurableS
pace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   MeasureT
heory.StronglyMeasurable f …

--- 原说明 ---
The norm of a strongly progressive process is strongly progressive.
-/
protected lemma norm {β : Type*} {u : ι → Ω → β} [SeminormedAddCommGroup β]
    (hu : IsStronglyProgressive f u) :
    IsStronglyProgressive f fun t ω ↦ ‖u t ω‖ := fun t ↦ (hu t).norm

end Arithmetic

end IsStronglyProgressive

/-
**MeasureTheory.IsProgressive.isStronglyProgressive** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.IsProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] {u : ι → Ω → β} {mi : MeasurableSpace ι} {mβ : MeasurableSpace β}   [Topolog
icalSpace.PseudoMetrizableSpace β] [SecondCountableTopology β] [OpensMeasurableS
pace β],   MeasureTheory.IsProgressive f u → MeasureTheory.IsStronglyProgressive
 f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
-/
lemma IsProgressive.isStronglyProgressive {mi : MeasurableSpace ι} {mβ : MeasurableSpace β}
    [PseudoMetrizableSpace β] [SecondCountableTopology β] [OpensMeasurableSpace β]
  (h : IsProgressive f u) : IsStronglyProgressive f u :=
  fun i ↦ (h i).stronglyMeasurable
/-
**MeasureTheory.IsStronglyProgressive.isProgressive** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.IsStronglyProgressive`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] {u : ι → Ω → β} {mi : MeasurableSpace ι} {mβ : MeasurableSpace β}   [Topolog
icalSpace.PseudoMetrizableSpace β] [BorelSpace β],   MeasureTheory.IsStronglyPro
gressive f u → MeasureTheory.IsProgressive f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
-/
lemma IsStronglyProgressive.isProgressive {mi : MeasurableSpace ι} {mβ : MeasurableSpace β}
    [PseudoMetrizableSpace β] [BorelSpace β] (h : IsStronglyProgressive f u) : IsProgressive f u :=
  fun i ↦ (h i).measurable
/-
**MeasureTheory.isStronglyProgressive_of_tendsto'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：isStronglyProgressive_of_tendsto' {γ} [MeasurableSpace ι] [PseudoMetrizabl
eSpace β] (fltr : Filter γ) [fltr.NeBot] [fltr.IsCountablyGenerated] {U : γ -> ι
 -> Ω -> β} (h : forall l, IsStronglyProgressive f (U l)) (h_tendsto : Tendsto U
 fltr (𝓝 u)) : IsStronglyProgressive f u
参数：fltr : Filter γ；h : forall l, IsStronglyProgressive f (U l)；h_tendsto : Tends
to U fltr (𝓝 u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `stronglyMeasurable_of_tendsto`：∀ {α : Type u_1} {β : Type u_2} {ι : Type
 u_5} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [TopologicalSpace.Ps
eudoMetrizableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Filter.Tendsto.apply_nhds`：Filter.Tendsto.apply_nhds {l : Filter Y} {f :
 Y -> forall i, A i} {x : forall i, A i} (h : Tendsto f l (𝓝 x)) (i : ι) : Tends
to (fun a => f …
-/
theorem isStronglyProgressive_of_tendsto' {γ} [MeasurableSpace ι] [PseudoMetrizableSpace β]
    (fltr : Filter γ) [fltr.NeBot] [fltr.IsCountablyGenerated] {U : γ → ι → Ω → β}
    (h : ∀ l, IsStronglyProgressive f (U l)) (h_tendsto : Tendsto U fltr (𝓝 u)) :
    IsStronglyProgressive f u := by
  intro i
  apply @stronglyMeasurable_of_tendsto (Set.Iic i × Ω) β γ
    (MeasurableSpace.prod _ (f i)) _ _ fltr _ _ _ _ fun l => h l i
  rw [tendsto_pi_nhds] at h_tendsto ⊢
  exact fun _ ↦ Tendsto.apply_nhds (h_tendsto _) _
/-
**MeasureTheory.isStronglyProgressive_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：isStronglyProgressive_of_tendsto [MeasurableSpace ι] [PseudoMetrizableSpac
e β] {U : Nat -> ι -> Ω -> β} (h : forall l, IsStronglyProgressive f (U l)) (h_t
endsto : Tendsto U atTop (𝓝 u)) : IsStronglyProgressive f u
参数：h : forall l, IsStronglyProgressive f (U l)；h_tendsto : Tendsto U atTop (𝓝 u)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isStronglyProgressive_of_tendsto'`：isStronglyProgressive_o
f_tendsto' {γ} [MeasurableSpace ι] [PseudoMetrizableSpace β] (fltr : Filter γ) [
fltr.NeBot] [fltr.IsCountablyGenerate…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
theorem isStronglyProgressive_of_tendsto [MeasurableSpace ι] [PseudoMetrizableSpace β]
    {U : ℕ → ι → Ω → β} (h : ∀ l, IsStronglyProgressive f (U l))
    (h_tendsto : Tendsto U atTop (𝓝 u)) : IsStronglyProgressive f u :=
  isStronglyProgressive_of_tendsto' atTop h h_tendsto

/-- A continuous and strongly adapted process is strongly progressive. -/
/-
**MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] {u : ι → Ω → β} [inst_2 : TopologicalSpace ι]   [TopologicalSpace.Metrizable
Space ι] [SecondCountableTopology ι] [inst_5 : MeasurableSpace ι] [OpensMeasurab
leSpace ι]   [TopologicalSpace.PseudoMetrizableSpace β],   MeasureTheory.Strongl
yAdapted f u → (∀ (ω : Ω), Continuous fun i => u i ω) → MeasureTheory.IsStrongly
Progressive f u
参数：∀ (ω : Ω), Continuous fun i => u i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasur
able`：stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable {α β ι : Ty
pe*} [TopologicalSpace ι] [MetrizableSpace ι] [MeasurableSpace ι] …
· 使用定理 `TopologicalSpace.MetrizableSpace.subtype`：∀ {X : Type u_2} [inst : Topol
ogicalSpace X] [TopologicalSpace.MetrizableSpace X] (s : Set X),   TopologicalSp
ace.MetrizableSpace ↑s
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
A continuous and strongly adapted process is strongly progressive.
-/
theorem StronglyAdapted.isStronglyProgressive_of_continuous [TopologicalSpace ι] [MetrizableSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    [PseudoMetrizableSpace β] (h : StronglyAdapted f u) (hu_cont : ∀ ω, Continuous fun i => u i ω) :
    IsStronglyProgressive f u := fun i =>
  @stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable _ _ (Set.Iic i) _ _ _ _ _ _ _
    (f i) _ (fun ω => (hu_cont ω).comp continuous_induced_dom) fun j => (h j).mono (f.mono j.prop)

/-- For filtrations indexed by a discrete order, `StronglyAdapted` and `IsStronglyProgressive` are
equivalent. This lemma provides `StronglyAdapted f u → IsStronglyProgressive f u`.
See `IsStronglyProgressive.stronglyAdapted` for the reverse direction, which is true more generally.
-/
/-
**MeasureTheory.StronglyAdapted.isStronglyProgressive_of_discrete** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι
] {f : MeasureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : TopologicalSpace
 β] {u : ι → Ω → β} [inst_2 : TopologicalSpace ι] [DiscreteTopology ι]   [Second
CountableTopology ι] [inst_5 : MeasurableSpace ι] [OpensMeasurableSpace ι]   [To
pologicalSpace.PseudoMetrizableSpace β],   MeasureTheory.StronglyAdapted f u → M
easureTheory.IsStronglyProgressive f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous`：∀ {Ω 
: Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : Meas
ureTheory.Filtration ι m}   {β : Type u_3} [inst_1 : To…
· 使用定理 `TopologicalSpace.DiscreteTopology.metrizableSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] [DiscreteTopology X], TopologicalSpace.MetrizableSpace X
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f

--- 原说明 ---
For filtrations indexed by a discrete order, `StronglyAdapted` and `IsStronglyPr
ogressive` are
equivalent. This lemma provides `StronglyAdapted f u → IsStronglyProgressive f u
`.
See `IsStronglyProgressive.stronglyAdapted` for the reverse direction, which is 
true more generally.
-/
theorem StronglyAdapted.isStronglyProgressive_of_discrete [TopologicalSpace ι] [DiscreteTopology ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    [PseudoMetrizableSpace β] (h : StronglyAdapted f u) : IsStronglyProgressive f u :=
  h.isStronglyProgressive_of_continuous fun _ => continuous_of_discreteTopology

@[deprecated (since := "2026-04-24")] alias ProgMeasurable := IsStronglyProgressive

@[deprecated (since := "2026-04-24")] alias progMeasurable_const := isStronglyProgressive_const

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.stronglyAdapted := IsStronglyProgressive.stronglyAdapted

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.comp := IsStronglyProgressive.comp

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.add := IsStronglyProgressive.add

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.mul := IsStronglyProgressive.mul

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_sum' := IsStronglyProgressive.finsetSum'

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_prod' := IsStronglyProgressive.finsetProd'

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_sum := IsStronglyProgressive.finsetSum

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_prod := IsStronglyProgressive.finsetProd

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.neg := IsStronglyProgressive.neg

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.inv := IsStronglyProgressive.inv

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.sub := IsStronglyProgressive.sub

@[to_additive existing ProgMeasurable.sub, deprecated (since := "2026-04-24")]
alias ProgMeasurable.div' := IsStronglyProgressive.div'

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.norm := IsStronglyProgressive.norm

@[deprecated (since := "2026-04-24")]
alias progMeasurable_of_tendsto := isStronglyProgressive_of_tendsto

@[deprecated (since := "2026-04-24")]
alias progMeasurable_of_tendsto' := isStronglyProgressive_of_tendsto'

@[deprecated (since := "2026-04-24")]
alias StronglyAdapted.progMeasurable_of_continuous :=
  StronglyAdapted.isStronglyProgressive_of_continuous

@[deprecated (since := "2026-04-24")]
alias StronglyAdapted.progMeasurable_of_discrete :=
  StronglyAdapted.isStronglyProgressive_of_discrete

end MeasureTheory

