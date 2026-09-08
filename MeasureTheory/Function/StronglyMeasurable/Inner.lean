/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Inner products of strongly measurable functions are strongly measurable.

-/

public section

variable {α 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace MeasureTheory

/-! ## Strongly measurable functions -/


local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace StronglyMeasurable

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.inner** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} {E : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {x : MeasurableSpace α
} {f g : α → E},   MeasureTheory.StronglyMeasurable f →     MeasureTheory.Strong
lyMeasurable g → MeasureTheory.StronglyMeasurable fun t => inner 𝕜 (f t) (g t)
参数：f t；g t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用定理 `MeasureTheory.StronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : 
TopologicalSpace γ] {f : α → …
-/
protected theorem inner {_ : MeasurableSpace α} {f g : α → E} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun t => ⟪f t, g t⟫ :=
  Continuous.comp_stronglyMeasurable continuous_inner (hf.prodMk hg)

end StronglyMeasurable

namespace AEStronglyMeasurable
variable {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f g : α → E} {c : E}

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.re** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {m m₀ : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {f : α → 𝕜},   MeasureTheory.AEStronglyMeasurab
le f μ → MeasureTheory.AEStronglyMeasurable (fun x => RCLike.re (f x)) μ
参数：fun x => RCLike.re (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `RCLike.continuous_re`：continuous_re : Continuous (re : K -> Real)
-/
protected theorem re {f : α → 𝕜} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x => RCLike.re (f x)) μ :=
  RCLike.continuous_re.comp_aestronglyMeasurable hf

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.im** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {m m₀ : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {f : α → 𝕜},   MeasureTheory.AEStronglyMeasurab
le f μ → MeasureTheory.AEStronglyMeasurable (fun x => RCLike.im (f x)) μ
参数：fun x => RCLike.im (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `RCLike.continuous_im`：continuous_im : Continuous (im : K -> Real)
-/
protected theorem im {f : α → 𝕜} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x => RCLike.im (f x)) μ :=
  RCLike.continuous_im.comp_aestronglyMeasurable hf

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.inner** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} {E : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] {m x : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f g : α → E},   MeasureTheory.AEStronglyMeasu
rable f μ →     MeasureTheory.AEStronglyMeasurable g μ → MeasureTheory.AEStrongl
yMeasurable (fun x => inner 𝕜 (f x) (g x)) μ
参数：fun x => inner 𝕜 (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m
 m₀ : MeasurableSpace α} {μ : M…
-/
protected theorem inner {_ : MeasurableSpace α} {μ : Measure α} {f g : α → E}
    (hf : AEStronglyMeasurable[m] f μ) (hg : AEStronglyMeasurable[m] g μ) :
    AEStronglyMeasurable[m] (fun x => ⟪f x, g x⟫) μ :=
  continuous_inner.comp_aestronglyMeasurable (hf.prodMk hg)

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.inner_const** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.AEStronglyMeasurable`。
形式化陈述：inner_const (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] (
⟪f ·, c⟫) μ
参数：hf : AEStronglyMeasurable[m] f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.inner`：∀ {α : Type u_1} {𝕜 : Type u_2
} {E : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : I
nnerProductSpace 𝕜 E] {m x : M…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
-/
lemma inner_const (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] (⟪f ·, c⟫) μ :=
  hf.inner aestronglyMeasurable_const

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.const_inner** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.AEStronglyMeasurable`。
形式化陈述：const_inner (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (
⟪c, g ·⟫) μ
参数：hg : AEStronglyMeasurable[m] g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.inner`：∀ {α : Type u_1} {𝕜 : Type u_2
} {E : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : I
nnerProductSpace 𝕜 E] {m x : M…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
-/
lemma const_inner (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (⟪c, g ·⟫) μ :=
  aestronglyMeasurable_const.inner hg

end AEStronglyMeasurable

end MeasureTheory

