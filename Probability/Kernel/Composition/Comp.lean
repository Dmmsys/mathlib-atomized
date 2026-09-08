/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Composition of kernels

We define the composition `η ∘ₖ κ` of kernels `κ : Kernel α β` and `η : Kernel β γ`, which is
a kernel from `α` to `γ`.

## Main definitions

* `comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ`: composition of 2 kernels.
  We define a notation `η ∘ₖ κ = comp η κ`.
  `∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a)`
* The monoid structure on `Kernel α α` given by kernel composition.

## Main statements

* `lintegral_comp`: Lebesgue integral of a function against a composition of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by composition.
* `pow_add_apply_eq_lintegral`: Chapman-Kolmogorov equations.

## Notation

* `η ∘ₖ κ = ProbabilityTheory.Kernel.comp η κ`

-/

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/-- Composition of two kernels. -/
/-
**ProbabilityTheory.Kernel.comp** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ker
nel`。
形式化陈述：comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ where toFun a
参数：η : Kernel β γ；κ : Kernel α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two kernels.
-/
noncomputable def comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ where
  toFun a := (κ a).bind η
  measurable' := (Measure.measurable_bind' η.measurable).comp κ.measurable

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ∘ₖ " => ProbabilityTheory.Kernel.comp
/-
**ProbabilityTheory.Kernel.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：comp_apply (η : Kernel β γ) (κ : Kernel α β) (a : α) : (η ∘ₖ κ) a = (κ a).
bind η
参数：η : Kernel β γ；κ : Kernel α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (η : Kernel β γ) (κ : Kernel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η :=
  rfl
/-
**ProbabilityTheory.Kernel.comp_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：comp_apply' (η : Kernel β γ) (κ : Kernel α β) (a : α) {s : Set γ} (hs : Me
asurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂κ a
参数：η : Kernel β γ；κ : Kernel α β；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
-/
theorem comp_apply' (η : Kernel β γ) (κ : Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂κ a := by
  rw [comp_apply, Measure.bind_apply hs (Kernel.aemeasurable _)]
/-
**ProbabilityTheory.Kernel.comp_apply_univ_le** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：comp_apply_univ_le (κ : Kernel α β) (η : Kernel β γ) (a : α) : (η ∘ₖ κ) a 
Set.univ <= κ a Set.univ * η.bound
参数：κ : Kernel α β；η : Kernel β γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem comp_apply_univ_le (κ : Kernel α β) (η : Kernel β γ) (a : α) :
    (η ∘ₖ κ) a Set.univ ≤ κ a Set.univ * η.bound := by
  rw [comp_apply' _ _ _ .univ]
  let Cη := η.bound
  calc
    ∫⁻ b, η b Set.univ ∂κ a ≤ ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η b Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _
/-
**ProbabilityTheory.Kernel.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β), ProbabilityTheory.Kernel.comp 0 κ = 0
参数：κ : ProbabilityTheory.Kernel α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.Measure.bind_zero_right`：bind_zero_right (m : Measure α) :
 bind m (0 : α -> Measure β) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma zero_comp (κ : Kernel α β) : (0 : Kernel β γ) ∘ₖ κ = 0 := by
  ext; simp [comp_apply, FunLike.coe_zero]
/-
**ProbabilityTheory.Kernel.comp_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
β γ), κ.comp 0 = 0
参数：κ : ProbabilityTheory.Kernel β γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.Measure.bind_zero_left`：bind_zero_left (f : α -> Measure β
) : bind (0 : Measure α) f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma comp_zero (κ : Kernel β γ) : κ ∘ₖ (0 : Kernel α β) = 0 := by ext; simp [comp_apply]
/-
**ProbabilityTheory.Kernel.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (κ : ProbabilityTheory.Kernel α β),   ProbabilityTheory.Kernel.id.comp κ
 = κ
参数：κ : ProbabilityTheory.Kernel α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasureTheory.lintegral_indicator_one`：lintegral_indicator_one {s : Set 
α} (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s
-/
@[simp] lemma id_comp (κ : Kernel α β) : Kernel.id ∘ₖ κ = κ := by
  ext a s hs
  simpa [comp_apply' _ _ _ hs, id_apply, Measure.dirac_apply' _ hs]
    using lintegral_indicator_one hs
/-
**ProbabilityTheory.Kernel.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
Kernel`。
形式化陈述：∀ {β : Type u_2} {γ : Type u_3} {mβ : MeasurableSpace β} {mγ : MeasurableS
pace γ} (κ : ProbabilityTheory.Kernel β γ),   κ.comp ProbabilityTheory.Kernel.id
 = κ
参数：κ : ProbabilityTheory.Kernel β γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma comp_id (κ : Kernel β γ) : κ ∘ₖ Kernel.id = κ := by
  ext a s hs
  simp [comp_apply' _ _ _ hs, id_apply,
    lintegral_dirac' a <| κ.measurable_coe hs]

section Ae

/-! ### `ae` filter of the composition -/

variable {κ : Kernel α β} {η : Kernel β γ} {a : α} {s : Set γ}

/-
**ProbabilityTheory.Kernel.ae_lt_top_of_comp_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：ae_lt_top_of_comp_ne_top (a : α) (hs : (η ∘ₖ κ) a s != ∞) : forallᵐ b ∂κ a
, η b s < ∞
参数：a : α；hs : (η ∘ₖ κ) a s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
-/
theorem ae_lt_top_of_comp_ne_top (a : α) (hs : (η ∘ₖ κ) a s ≠ ∞) : ∀ᵐ b ∂κ a, η b s < ∞ := by
  have h : ∀ᵐ b ∂κ a, η b (toMeasurable ((η ∘ₖ κ) a) s) < ∞ := by
    refine ae_lt_top (Kernel.measurable_coe η (measurableSet_toMeasurable ..)) ?_
    rwa [← Kernel.comp_apply' _ _ _ (measurableSet_toMeasurable ..), measure_toMeasurable]
  filter_upwards [h] with b hb using (measure_mono (subset_toMeasurable _ _)).trans_lt hb
/-
**ProbabilityTheory.Kernel.comp_null** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：comp_null (a : α) (hs : MeasurableSet s) : (η ∘ₖ κ) a s = 0 ↔ (fun y => η 
y s) =ᵐ[κ a] 0
参数：a : α；hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comp_null (a : α) (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = 0 ↔ (fun y ↦ η y s) =ᵐ[κ a] 0 := by
  rw [comp_apply' _ _ _ hs, lintegral_eq_zero_iff (η.measurable_coe hs)]
/-
**ProbabilityTheory.Kernel.ae_null_of_comp_null** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：ae_null_of_comp_null (h : (η ∘ₖ κ) a s = 0) : (η · s) =ᵐ[κ a] 0
参数：h : (η ∘ₖ κ) a s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyLE_antisymm_iff`：eventuallyLE_antisymm_iff [PartialOrde
r β] {l : Filter α} {f g : α -> β} : f =ᶠ[l] g ↔ f <=ᶠ[l] g ∧ g <=ᶠ[l] f
· 使用定理 `Filter.EventuallyLE.trans_eq`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g =ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `ProbabilityTheory.Kernel.comp_null`：comp_null (a : α) (hs : MeasurableSe
t s) : (η ∘ₖ κ) a s = 0 ↔ (fun y => η y s) =ᵐ[κ a] 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem ae_null_of_comp_null (h : (η ∘ₖ κ) a s = 0) : (η · s) =ᵐ[κ a] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [comp_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact ⟨Filter.EventuallyLE.trans_eq (ae_of_all _ fun _ ↦ measure_mono hst) ht,
    ae_of_all _ fun _ ↦ zero_le⟩

variable {p : γ → Prop}
/-
**ProbabilityTheory.Kernel.ae_ae_of_ae_comp** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：ae_ae_of_ae_comp (h : forallᵐ z ∂(η ∘ₖ κ) a, p z) : forallᵐ y ∂κ a, forall
ᵐ z ∂η y, p z
参数：h : forallᵐ z ∂(η ∘ₖ κ) a, p z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.ae_null_of_comp_null`：ae_null_of_comp_null (h :
 (η ∘ₖ κ) a s = 0) : (η · s) =ᵐ[κ a] 0
-/
theorem ae_ae_of_ae_comp (h : ∀ᵐ z ∂(η ∘ₖ κ) a, p z) :
    ∀ᵐ y ∂κ a, ∀ᵐ z ∂η y, p z := ae_null_of_comp_null h
/-
**ProbabilityTheory.Kernel.ae_comp_of_ae_ae** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：ae_comp_of_ae_ae (hp : MeasurableSet {z | p z}) (h : forallᵐ y ∂κ a, foral
lᵐ z ∂η y, p z) : forallᵐ z ∂(η ∘ₖ κ) a, p z
参数：hp : MeasurableSet {z | p z}；h : forallᵐ y ∂κ a, forallᵐ z ∂η y, p z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `ProbabilityTheory.Kernel.comp_null`：comp_null (a : α) (hs : MeasurableSe
t s) : (η ∘ₖ κ) a s = 0 ↔ (fun y => η y s) =ᵐ[κ a] 0
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
lemma ae_comp_of_ae_ae (hp : MeasurableSet {z | p z})
    (h : ∀ᵐ y ∂κ a, ∀ᵐ z ∂η y, p z) : ∀ᵐ z ∂(η ∘ₖ κ) a, p z := by
  rwa [ae_iff, comp_null] at *
  exact hp.compl
/-
**ProbabilityTheory.Kernel.ae_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：ae_comp_iff (hp : MeasurableSet {z | p z}) : (forallᵐ z ∂(η ∘ₖ κ) a, p z) 
↔ forallᵐ y ∂κ a, forallᵐ z ∂η y, p z
参数：hp : MeasurableSet {z | p z}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.ae_ae_of_ae_comp`：ae_ae_of_ae_comp (h : forallᵐ
 z ∂(η ∘ₖ κ) a, p z) : forallᵐ y ∂κ a, forallᵐ z ∂η y, p z
· 使用引理 `ProbabilityTheory.Kernel.ae_comp_of_ae_ae`：ae_comp_of_ae_ae (hp : Measur
ableSet {z | p z}) (h : forallᵐ y ∂κ a, forallᵐ z ∂η y, p z) : forallᵐ z ∂(η ∘ₖ 
κ) a, p z
-/
lemma ae_comp_iff (hp : MeasurableSet {z | p z}) :
    (∀ᵐ z ∂(η ∘ₖ κ) a, p z) ↔ ∀ᵐ y ∂κ a, ∀ᵐ z ∂η y, p z :=
  ⟨ae_ae_of_ae_comp, ae_comp_of_ae_ae hp⟩

end Ae

section Restrict

variable {κ : Kernel α β} {η : Kernel β γ}

/-
**ProbabilityTheory.Kernel.comp_restrict** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：comp_restrict {s : Set γ} (hs : MeasurableSet s) : η.restrict hs ∘ₖ κ = (η
 ∘ₖ κ).restrict hs
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply'`：restrict_apply' (κ : Kernel α 
β) (hs : MeasurableSet s) (a : α) (ht : MeasurableSet t) : κ.restrict hs a t = (
κ a) (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_restrict {s : Set γ} (hs : MeasurableSet s) :
    η.restrict hs ∘ₖ κ = (η ∘ₖ κ).restrict hs := by
  ext a t ht
  simp_rw [comp_apply' _ _ _ ht, restrict_apply' _ _ _ ht, comp_apply' _ _ _ (ht.inter hs)]

end Restrict

/-
**ProbabilityTheory.Kernel.lintegral_comp** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：lintegral_comp (η : Kernel β γ) (κ : Kernel α β) (a : α) {g : γ -> Real>=0
∞} (hg : Measurable g) : ∫⁻ c, g c ∂(η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂η b ∂κ a
参数：η : Kernel β γ；κ : Kernel α β；a : α；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用定理 `MeasureTheory.Measure.lintegral_bind`：lintegral_bind {m : Measure α} {μ 
: α -> Measure β} {f : β -> Real>=0∞} (hμ : AEMeasurable μ m) (hf : AEMeasurable
 f (bind m μ)) : ∫⁻ x, f x…
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem lintegral_comp (η : Kernel β γ) (κ : Kernel α β) (a : α) {g : γ → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ c, g c ∂(η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂η b ∂κ a := by
  rw [comp_apply, Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]

/-- Composition of kernels is associative. -/
/-
**ProbabilityTheory.Kernel.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：comp_assoc {δ : Type*} {mδ : MeasurableSpace δ} (ξ : Kernel γ δ) (η : Kern
el β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ (η ∘ₖ κ)
参数：ξ : Kernel γ δ；η : Kernel β γ；κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext_fun`：ext_fun (h : forall a f, Measurable f 
-> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a) : κ = η
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.lintegral_comp`：lintegral_comp (η : Kernel β γ)
 (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, g c ∂(
η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Measurable.lintegral_kernel`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kernel α β}   {f :
 β → ENNReal}, Me…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Composition of kernels is associative.
-/
theorem comp_assoc {δ : Type*} {mδ : MeasurableSpace δ} (ξ : Kernel γ δ)
    (η : Kernel β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ (η ∘ₖ κ) := by
  refine ext_fun fun a f hf => ?_
  simp_rw [lintegral_comp _ _ _ hf, lintegral_comp _ _ _ hf.lintegral_kernel]
/-
**ProbabilityTheory.Kernel.comp_discard'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：comp_discard' (κ : Kernel α β) : discard β ∘ₖ κ = { toFun a
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Measurable.smul_measure`：∀ {α : Type u_1} {β : Type u_2} {mα : Measurabl
eSpace α} {mβ : MeasurableSpace β} {f : α → ENNReal},   Measurable f → ∀ (μ : Me
asureTheory.M…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.discard_apply`：discard_apply (a : α) : discard 
α a = Measure.dirac PUnit.unit
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_discard' (κ : Kernel α β) :
    discard β ∘ₖ κ =
      { toFun a := κ a .univ • Measure.dirac PUnit.unit
        measurable' := (κ.measurable_coe .univ).smul_measure _ } := by
  ext a s hs
  simp [comp_apply' _ _ _ hs, mul_comm]

@[simp]
/-
**ProbabilityTheory.Kernel.comp_discard** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：comp_discard (κ : Kernel α β) [IsMarkovKernel κ] : discard β ∘ₖ κ = discar
d α
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Measurable.smul_measure`：∀ {α : Type u_1} {β : Type u_2} {mα : Measurabl
eSpace α} {mβ : MeasurableSpace β} {f : α → ENNReal},   Measurable f → ∀ (μ : Me
asureTheory.M…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `ProbabilityTheory.Kernel.comp_discard'`：comp_discard' (κ : Kernel α β) :
 discard β ∘ₖ κ = { toFun a
· 使用定理 `ProbabilityTheory.Kernel.mk.congr_simp`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (toFun toFun_1 : α → M
easureTheory.Measure β) (e_t…
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用引理 `ProbabilityTheory.Kernel.discard_apply`：discard_apply (a : α) : discard 
α a = Measure.dirac PUnit.unit
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_discard (κ : Kernel α β) [IsMarkovKernel κ] : discard β ∘ₖ κ = discard α := by
  ext; simp [comp_discard']

@[simp]
/-
**ProbabilityTheory.Kernel.swap_copy** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：swap_copy : (swap α α) ∘ₖ (copy α) = copy α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用引理 `ProbabilityTheory.Kernel.copy_apply`：copy_apply (a : α) : copy α a = Mea
sure.dirac (a, a)
· 使用定理 `MeasureTheory.Measure.dirac_bind`：dirac_bind {f : α -> Measure β} (hf : 
Measurable f) (a : α) : bind (dirac a) f = f a
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
· 使用引理 `ProbabilityTheory.Kernel.swap_apply'`：swap_apply' (ab : α × β) {s : Set 
(β × α)} (hs : MeasurableSet s) : swap α β ab s = s.indicator 1 ab.swap
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
-/
lemma swap_copy : (swap α α) ∘ₖ (copy α) = copy α := by
  ext a s hs
  rw [comp_apply, copy_apply, Measure.dirac_bind (Kernel.measurable _), swap_apply' _ hs,
    Measure.dirac_apply' _ hs]
  congr
/-
**ProbabilityTheory.Kernel.const_comp** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：const_comp (μ : Measure γ) (κ : Kernel α β) : const β μ ∘ₖ κ = fun a => (κ
 a) Set.univ • μ
参数：μ : Measure γ；κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma const_comp (μ : Measure γ) (κ : Kernel α β) :
    const β μ ∘ₖ κ = fun a ↦ (κ a) Set.univ • μ := by
  ext _ _ hs
  simp_rw [comp_apply' _ _ _ hs, const_apply, MeasureTheory.lintegral_const, Measure.smul_apply,
    smul_eq_mul, mul_comm]

@[simp]
/-
**ProbabilityTheory.Kernel.const_comp'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：const_comp' (μ : Measure γ) (κ : Kernel α β) [IsMarkovKernel κ] : const β 
μ ∘ₖ κ = const α μ
参数：μ : Measure γ；κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ProbabilityTheory.Kernel.const_comp`：const_comp (μ : Measure γ) (κ : Ker
nel α β) : const β μ ∘ₖ κ = fun a => (κ a) Set.univ • μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma const_comp' (μ : Measure γ) (κ : Kernel α β) [IsMarkovKernel κ] :
    const β μ ∘ₖ κ = const α μ := by
  ext; simp_rw [const_comp, measure_univ, one_smul, const_apply]
/-
**ProbabilityTheory.Kernel.comp_add_right** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：comp_add_right (μ κ : Kernel α β) (η : Kernel β γ) : η ∘ₖ (μ + κ) = η ∘ₖ μ
 + η ∘ₖ κ
参数：μ κ : Kernel α β；η : Kernel β γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_add_right (μ κ : Kernel α β) (η : Kernel β γ) :
    η ∘ₖ (μ + κ) = η ∘ₖ μ + η ∘ₖ κ := by ext _ _ hs; simp [comp_apply' _ _ _ hs]
/-
**ProbabilityTheory.Kernel.comp_add_left** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：comp_add_left (μ : Kernel α β) (κ η : Kernel β γ) : (κ + η) ∘ₖ μ = κ ∘ₖ μ 
+ η ∘ₖ μ
参数：μ : Kernel α β；κ η : Kernel β γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_add_left (μ : Kernel α β) (κ η : Kernel β γ) :
    (κ + η) ∘ₖ μ = κ ∘ₖ μ + η ∘ₖ μ := by
  ext a s hs
  simp_rw [comp_apply' _ _ _ hs, add_apply, Measure.add_apply, comp_apply' _ _ _ hs,
    lintegral_add_left (Kernel.measurable_coe κ hs)]
/-
**ProbabilityTheory.Kernel.comp_sum_right** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：comp_sum_right {ι : Type*} [Countable ι] (κ : ι -> Kernel α β) (η : Kernel
 β γ) : η ∘ₖ Kernel.sum κ = Kernel.sum fun i => η ∘ₖ (κ i)
参数：κ : ι -> Kernel α β；η : Kernel β γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_sum_right {ι : Type*} [Countable ι] (κ : ι → Kernel α β) (η : Kernel β γ) :
    η ∘ₖ Kernel.sum κ = Kernel.sum fun i ↦ η ∘ₖ (κ i) := by
  ext _ _ hs
  simp_rw [sum_apply, comp_apply' _ _ _ hs, Measure.sum_apply _ hs, sum_apply,
    lintegral_sum_measure, comp_apply' _ _ _ hs]
/-
**ProbabilityTheory.Kernel.comp_sum_left** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：comp_sum_left {ι : Type*} [Countable ι] (κ : Kernel α β) (η : ι -> Kernel 
β γ) : (Kernel.sum η) ∘ₖ κ = Kernel.sum (fun i => (η i) ∘ₖ κ)
参数：κ : Kernel α β；η : ι -> Kernel β γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `MeasureTheory.lintegral_tsum`：lintegral_tsum [Countable β] {f : β -> α -
> Real>=0∞} (hf : forall i, AEMeasurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i,
 ∫⁻ a, f i a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
-/
lemma comp_sum_left {ι : Type*} [Countable ι] (κ : Kernel α β) (η : ι → Kernel β γ) :
    (Kernel.sum η) ∘ₖ κ = Kernel.sum (fun i ↦ (η i) ∘ₖ κ) := by
  ext _ _ hs
  simp_rw [sum_apply, comp_apply' _ _ _ hs, sum_apply, Measure.sum_apply _ hs,
    comp_apply' _ _ _ hs]
  rw [lintegral_tsum]
  exact fun _ ↦ (Kernel.measurable_coe _ hs).aemeasurable
/-
**ProbabilityTheory.Kernel.copy_comp_apply_prod** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：copy_comp_apply_prod (κ : Kernel α β) (a : α) {s t : Set β} (hs : Measurab
leSet s) (ht : MeasurableSet t) : (copy β ∘ₖ κ) a (s ×ˢ t) = κ a (s inter t)
参数：κ : Kernel α β；a : α；hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.Kernel.copy_apply`：copy_apply (a : α) : copy α a = Mea
sure.dirac (a, a)
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用引理 `Set.indicator_prod_one`：indicator_prod_one {t : Set κ} {j : κ} : (s ×ˢ t
).indicator (1 : ι × κ -> M₀) (i, j) = s.indicator 1 i * t.indicator 1 j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Set.inter_indicator_one`：inter_indicator_one : (s inter t).indicator (1 
: ι -> M₀) = s.indicator 1 * t.indicator 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_indicator_one`：lintegral_indicator_one {s : Set 
α} (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
lemma copy_comp_apply_prod (κ : Kernel α β) (a : α) {s t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : (copy β ∘ₖ κ) a (s ×ˢ t) = κ a (s ∩ t) := by
  rw [comp_apply' _ _ _ <| hs.prod ht]
  simp_rw [copy_apply, Measure.dirac_apply' _ <| hs.prod ht, Set.indicator_prod_one]
  calc
  _ = ∫⁻ b, (s ∩ t).indicator 1 b ∂κ a := by
    congr with b
    simp [Set.inter_indicator_one]
  _ = κ a (s ∩ t) := lintegral_indicator_one <| hs.inter ht
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.comp** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (η : ProbabilityTheory.Kernel 
β γ) [ProbabilityTheory.IsMarkovKernel η]   (κ : ProbabilityTheory.Kernel α β) [
ProbabilityTheory.IsMarkovKernel κ], ProbabilityTheory.IsMarkovKernel (η.comp κ)
参数：η : ProbabilityTheory.Kernel β γ；κ : ProbabilityTheory.Kernel α β；η.comp κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance IsMarkovKernel.comp (η : Kernel β γ) [IsMarkovKernel η] (κ : Kernel α β)
    [IsMarkovKernel κ] : IsMarkovKernel (η ∘ₖ κ) where
  isProbabilityMeasure a := by
    rw [comp_apply]
    constructor
    rw [Measure.bind_apply .univ η.aemeasurable]
    simp
/-
**ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.comp** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IsZeroOrMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsZeroOrMarkovKernel κ]   (η : ProbabilityTheory.Kernel 
β γ) [ProbabilityTheory.IsZeroOrMarkovKernel η],   ProbabilityTheory.IsZeroOrMar
kovKernel (η.comp κ)
参数：κ : ProbabilityTheory.Kernel α β；η : ProbabilityTheory.Kernel β γ；η.comp κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.eq_zero_or_isMarkovKernel`：eq_zero_or_isMarkovKernel (
κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] : κ = 0 ∨ IsMarkovKernel κ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_zero`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.instIsZeroOrMarkovKernelOfNatKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   ProbabilityT
heory.IsZeroOrMarkovKernel 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.zero_comp`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.comp`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (η : Probability…
-/
instance IsZeroOrMarkovKernel.comp (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
    (η : Kernel β γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (η ∘ₖ κ) := by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.comp** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (η : ProbabilityTheory.Kernel 
β γ) [ProbabilityTheory.IsFiniteKernel η]   (κ : ProbabilityTheory.Kernel α β) [
ProbabilityTheory.IsFiniteKernel κ], ProbabilityTheory.IsFiniteKernel (η.comp κ)
参数：η : ProbabilityTheory.Kernel β γ；κ : ProbabilityTheory.Kernel α β；η.comp κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
· 使用定理 `ProbabilityTheory.Kernel.comp_apply_univ_le`：comp_apply_univ_le (κ : Ker
nel α β) (η : Kernel β γ) (a : α) : (η ∘ₖ κ) a Set.univ <= κ a Set.univ * η.boun
d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
instance IsFiniteKernel.comp (η : Kernel β γ) [IsFiniteKernel η] (κ : Kernel α β)
    [IsFiniteKernel κ] : IsFiniteKernel (η ∘ₖ κ) := by
  refine ⟨⟨κ.bound * η.bound, ENNReal.mul_lt_top κ.bound_lt_top η.bound_lt_top, fun a ↦ ?_⟩⟩
  calc (η ∘ₖ κ) a Set.univ
  _ ≤ κ a Set.univ * η.bound := comp_apply_univ_le κ η a
  _ ≤ κ.bound * η.bound := by gcongr; exact measure_le_bound κ a Set.univ
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.comp** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (η : ProbabilityTheory.Kernel 
β γ) [ProbabilityTheory.IsSFiniteKernel η]   (κ : ProbabilityTheory.Kernel α β) 
[ProbabilityTheory.IsSFiniteKernel κ], ProbabilityTheory.IsSFiniteKernel (η.comp
 κ)
参数：η : ProbabilityTheory.Kernel β γ；κ : ProbabilityTheory.Kernel α β；η.comp κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.kernel_sum_seq`：kernel_sum_seq (κ : Kernel α β)
 [h : IsSFiniteKernel κ] : Kernel.sum (seq κ) = κ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.comp_sum_left`：comp_sum_left {ι : Type*} [Count
able ι] (κ : Kernel α β) (η : ι -> Kernel β γ) : (Kernel.sum η) ∘ₖ κ = Kernel.su
m (fun i => (η i) ∘ₖ κ)
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.Kernel.comp_sum_right`：comp_sum_right {ι : Type*} [Cou
ntable ι] (κ : ι -> Kernel α β) (η : Kernel β γ) : η ∘ₖ Kernel.sum κ = Kernel.su
m fun i => η ∘ₖ (κ i)
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comp`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (η : Probability…
-/
instance IsSFiniteKernel.comp (η : Kernel β γ) [IsSFiniteKernel η] (κ : Kernel α β)
    [IsSFiniteKernel κ] : IsSFiniteKernel (η ∘ₖ κ) := by
  simp_rw [← kernel_sum_seq κ, ← kernel_sum_seq η, comp_sum_left, comp_sum_right]
  infer_instance

section Monoid

/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Monoid (Kernel α α) where
  mul η κ := η ∘ₖ κ
  mul_assoc ξ η κ := comp_assoc _ _ _
  one := Kernel.id
  one_mul := id_comp
  mul_one := comp_id

/-! ### Chapman-Kolmogorov Equations -/

/-- The **Chapman-Kolmogorov equation**, kernel composition version.
The `n+m`-step transition kernel is the composition of the `n`-step and `m`-step kernels.
Ref. *Meyn-Tweedie* Theorem 3.4.2, page 68 -/
/-
**ProbabilityTheory.Kernel.pow_add** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
Kernel`。
形式化陈述：pow_add (κ : Kernel α α) (m n : Nat) : κ ^ (m + n) = (κ ^ m) ∘ₖ (κ ^ n)
参数：κ : Kernel α α；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d

--- 原说明 ---
The **Chapman-Kolmogorov equation**, kernel composition version.
The `n+m`-step transition kernel is the composition of the `n`-step and `m`-step
 kernels.
Ref. *Meyn-Tweedie* Theorem 3.4.2, page 68
-/
theorem pow_add (κ : Kernel α α) (m n : ℕ) :
    κ ^ (m + n) = (κ ^ m) ∘ₖ (κ ^ n) := _root_.pow_add κ m n

/-- The **Chapman-Kolmogorov equation**, integral version. -/
/-
**ProbabilityTheory.Kernel.pow_add_apply_eq_lintegral** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：pow_add_apply_eq_lintegral (κ : Kernel α α) (m n : Nat) (a : α) {s : Set α
} (hs : MeasurableSet s) : (κ ^ (m + n)) a s = ∫⁻ b, (κ ^ n) b s ∂((κ ^ m) a)
参数：κ : Kernel α α；m n : Nat；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.pow_add`：pow_add (κ : Kernel α α) (m n : Nat) :
 κ ^ (m + n) = (κ ^ m) ∘ₖ (κ ^ n)
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The **Chapman-Kolmogorov equation**, integral version.
-/
theorem pow_add_apply_eq_lintegral (κ : Kernel α α) (m n : ℕ) (a : α) {s : Set α}
    (hs : MeasurableSet s) :
    (κ ^ (m + n)) a s = ∫⁻ b, (κ ^ n) b s ∂((κ ^ m) a) := by
  rw [add_comm]; simp [pow_add, comp_apply' _ _ _ hs]

/-- A version of the Chapman-Kolmogorov equation useful for paths. -/
/-
**ProbabilityTheory.Kernel.pow_succ_apply_eq_lintegral** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：pow_succ_apply_eq_lintegral (κ : Kernel α α) (n : Nat) (a : α) {s : Set α}
 (hs : MeasurableSet s) : (κ ^ (n + 1)) a s = ∫⁻ b, κ b s ∂((κ ^ n) a)
参数：κ : Kernel α α；n : Nat；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ProbabilityTheory.Kernel.pow_add_apply_eq_lintegral`：pow_add_apply_eq_li
ntegral (κ : Kernel α α) (m n : Nat) (a : α) {s : Set α} (hs : MeasurableSet s) 
: (κ ^ (m + n)) a s = ∫⁻ b, (κ ^ n) b s ∂…

--- 原说明 ---
A version of the Chapman-Kolmogorov equation useful for paths.
-/
theorem pow_succ_apply_eq_lintegral (κ : Kernel α α) (n : ℕ) (a : α) {s : Set α}
    (hs : MeasurableSet s) :
    (κ ^ (n + 1)) a s = ∫⁻ b, κ b s ∂((κ ^ n) a) := by
  simpa using pow_add_apply_eq_lintegral _ n 1 _ hs

end Monoid

end Kernel
end ProbabilityTheory

