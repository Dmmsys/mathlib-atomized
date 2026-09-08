/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# With Density

For an s-finite kernel `κ : Kernel α β` and a function `f : α → β → ℝ≥0∞` which is finite
everywhere, we define `withDensity κ f` as the kernel `a ↦ (κ a).withDensity (f a)`. This is
an s-finite kernel.

## Main definitions

* `ProbabilityTheory.Kernel.withDensity κ (f : α → β → ℝ≥0∞)`:
  kernel `a ↦ (κ a).withDensity (f a)`. It is defined if `κ` is s-finite. If `f` is finite
  everywhere, then this is also an s-finite kernel. The class of s-finite kernels is the smallest
  class of kernels that contains finite kernels and which is stable by `withDensity`.
  Integral: `∫⁻ b, g b ∂(withDensity κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

## Main statements

* `ProbabilityTheory.Kernel.lintegral_withDensity`:
  `∫⁻ b, g b ∂(withDensity κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

-/

@[expose] public section


open MeasureTheory ProbabilityTheory

open scoped MeasureTheory ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {κ : Kernel α β} {f : α → β → ℝ≥0∞}

/-- Kernel with image `(κ a).withDensity (f a)` if `Function.uncurry f` is measurable, and
with image 0 otherwise. If `Function.uncurry f` is measurable, it satisfies
`∫⁻ b, g b ∂(withDensity κ f hf a) = ∫⁻ b, f a b * g b ∂(κ a)`. -/
/-
**ProbabilityTheory.Kernel.withDensity** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：withDensity (κ : Kernel α β) [IsSFiniteKernel κ] (f : α -> β -> Real>=0∞) 
: Kernel α β
参数：κ : Kernel α β；f : α -> β -> Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Kernel with image `(κ a).withDensity (f a)` if `Function.uncurry f` is measurabl
e, and
with image 0 otherwise. If `Function.uncurry f` is measurable, it satisfies
`∫⁻ b, g b ∂(withDensity κ f hf a) = ∫⁻ b, f a b * g b ∂(κ a)`.
-/
noncomputable def withDensity (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → β → ℝ≥0∞) :
    Kernel α β :=
  @dite _ (Measurable (Function.uncurry f)) (Classical.dec _) (fun hf =>
    (⟨fun a => (κ a).withDensity (f a),
      by
        refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
        simp_rw [withDensity_apply _ hs]
        exact hf.setLIntegral_kernel_prod_right hs⟩ : Kernel α β)) fun _ => 0
/-
**ProbabilityTheory.Kernel.withDensity_of_not_measurable** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.Kernel`。
形式化陈述：withDensity_of_not_measurable (κ : Kernel α β) [IsSFiniteKernel κ] (hf : ¬
Measurable (Function.uncurry f)) : withDensity κ f = 0
参数：κ : Kernel α β；hf : ¬Measurable (Function.uncurry f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem withDensity_of_not_measurable (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : ¬Measurable (Function.uncurry f)) : withDensity κ f = 0 := by exact dif_neg hf
/-
**ProbabilityTheory.Kernel.withDensity_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {f : α → β → ENNReal}   (κ : ProbabilityTheory.Kernel α β) [inst : Proba
bilityTheory.IsSFiniteKernel κ],   Measurable (Function.uncurry f) → ∀ (a : α), 
(κ.withDensity f) a = (κ a).withDensity (f a)
参数：κ : ProbabilityTheory.Kernel α β；Function.uncurry f；a : α；κ.withDensity f；κ a
；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity.eq_1`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kern
el α β)   [inst : ProbabilityTh…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
protected theorem withDensity_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) :
    withDensity κ f a = (κ a).withDensity (f a) := by
  rw [withDensity, dif_pos hf]
  rfl
/-
**ProbabilityTheory.Kernel.withDensity_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {f : α → β → ENNReal}   (κ : ProbabilityTheory.Kernel α β) [inst : Proba
bilityTheory.IsSFiniteKernel κ],   Measurable (Function.uncurry f) → ∀ (a : α) (
s : Set β), ((κ.withDensity f) a) s = ∫⁻ (b : β) in s, f a b ∂κ a
参数：κ : ProbabilityTheory.Kernel α β；Function.uncurry f；a : α；s : Set β；(κ.withDe
nsity f) a；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用定理 `MeasureTheory.withDensity_apply'`：withDensity_apply' [SFinite μ] (f : α 
-> Real>=0∞) (s : Set α) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
protected theorem withDensity_apply' (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) (s : Set β) :
    withDensity κ f a s = ∫⁻ b in s, f a b ∂κ a := by
  rw [Kernel.withDensity_apply κ hf, withDensity_apply' _ s]

nonrec lemma withDensity_congr_ae (κ : Kernel α β) [IsSFiniteKernel κ] {f g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfg : ∀ a, f a =ᵐ[κ a] g a) :
    withDensity κ f = withDensity κ g := by
  ext a
  rw [Kernel.withDensity_apply _ hf, Kernel.withDensity_apply _ hg, withDensity_congr_ae (hfg a)]

nonrec lemma withDensity_absolutelyContinuous [IsSFiniteKernel κ]
    (f : α → β → ℝ≥0∞) (a : α) :
    Kernel.withDensity κ f a ≪ κ a := by
  by_cases hf : Measurable (Function.uncurry f)
  · rw [Kernel.withDensity_apply _ hf]
    exact withDensity_absolutelyContinuous _ _
  · rw [withDensity_of_not_measurable _ hf]
    simp [Measure.AbsolutelyContinuous.zero]

@[simp]
/-
**ProbabilityTheory.Kernel.withDensity_one** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：withDensity_one (κ : Kernel α β) [IsSFiniteKernel κ] : Kernel.withDensity 
κ 1 = κ
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.withDensity_one`：withDensity_one : μ.withDensity 1 = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withDensity_one (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ 1 = κ := by
  ext; rw [Kernel.withDensity_apply _ measurable_const]; simp

@[simp]
/-
**ProbabilityTheory.Kernel.withDensity_one'** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：withDensity_one' (κ : Kernel α β) [IsSFiniteKernel κ] : Kernel.withDensity
 κ (fun _ _ => 1) = κ
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.withDensity_one`：withDensity_one (κ : Kernel α 
β) [IsSFiniteKernel κ] : Kernel.withDensity κ 1 = κ
-/
lemma withDensity_one' (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ (fun _ _ ↦ 1) = κ := Kernel.withDensity_one _

@[simp]
/-
**ProbabilityTheory.Kernel.withDensity_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：withDensity_zero (κ : Kernel α β) [IsSFiniteKernel κ] : Kernel.withDensity
 κ 0 = 0
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.withDensity_zero`：withDensity_zero : μ.withDensity 0 = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withDensity_zero (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ 0 = 0 := by
  ext; rw [Kernel.withDensity_apply _ measurable_const]; simp

@[simp]
/-
**ProbabilityTheory.Kernel.withDensity_zero'** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：withDensity_zero' (κ : Kernel α β) [IsSFiniteKernel κ] : Kernel.withDensit
y κ (fun _ _ => 0) = 0
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.withDensity_zero`：withDensity_zero (κ : Kernel 
α β) [IsSFiniteKernel κ] : Kernel.withDensity κ 0 = 0
-/
lemma withDensity_zero' (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ (fun _ _ ↦ 0) = 0 := Kernel.withDensity_zero _
/-
**ProbabilityTheory.Kernel.lintegral_withDensity** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：lintegral_withDensity (κ : Kernel α β) [IsSFiniteKernel κ] (hf : Measurabl
e (Function.uncurry f)) (a : α) {g : β -> Real>=0∞} (hg : Measurable g) : ∫⁻ b, 
g b ∂withDensity κ f a = ∫⁻ b, f a b * g b ∂κ a
参数：κ : Kernel α β；hf : Measurable (Function.uncurry f)；a : α；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用定理 `MeasureTheory.lintegral_withDensity_eq_lintegral_mul`：lintegral_withDens
ity_eq_lintegral_mul (μ : Measure α) {f : α -> Real>=0∞} (h_mf : Measurable f) :
 forall {g : α -> Real>=0∞}, Measurable g …
· 使用定理 `Measurable.of_uncurry_left`：Measurable.of_uncurry_left {f : α -> β -> γ}
 (hf : Measurable (uncurry f)) {x : α} : Measurable (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_withDensity (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) {g : β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ b, g b ∂withDensity κ f a = ∫⁻ b, f a b * g b ∂κ a := by
  rw [Kernel.withDensity_apply _ hf,
    lintegral_withDensity_eq_lintegral_mul _ (Measurable.of_uncurry_left hf) hg]
  simp_rw [Pi.mul_apply]
/-
**ProbabilityTheory.Kernel.integral_withDensity** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：integral_withDensity {E : Type*} [NormedAddCommGroup E] [NormedSpace Real 
E] {f : β -> E} [IsSFiniteKernel κ] {a : α} {g : α -> β -> Real>=0} (hg : Measur
able (Function.uncurry g)) : ∫ b, f b ∂withDensity κ (fun a b => g a b) a = ∫ b,
 g a b • f b ∂κ a
参数：hg : Measurable (Function.uncurry g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `integral_withDensity_eq_integral_smul`：integral_withDensity_eq_integral_
smul {f : X -> Real>=0} (f_meas : Measurable f) (g : X -> E) : ∫ x, g x ∂μ.withD
ensity (fun x => f x) = ∫ x…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
theorem integral_withDensity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : β → E} [IsSFiniteKernel κ] {a : α} {g : α → β → ℝ≥0}
    (hg : Measurable (Function.uncurry g)) :
    ∫ b, f b ∂withDensity κ (fun a b => g a b) a = ∫ b, g a b • f b ∂κ a := by
  rw [Kernel.withDensity_apply, integral_withDensity_eq_integral_smul]
  · fun_prop
  · fun_prop
/-
**ProbabilityTheory.Kernel.withDensity_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：withDensity_add_left (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKern
el η] (f : α -> β -> Real>=0∞) : withDensity (κ + η) f = withDensity κ f + withD
ensity η f
参数：κ η : Kernel α β；f : α -> β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
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
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `MeasureTheory.withDensity_add_measure`：withDensity_add_measure {m : Meas
urableSpace α} (μ ν : Measure α) (f : α -> Real>=0∞) : (μ + ν).withDensity f = μ
.withDensity f + ν.withDens…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.withDensity_of_not_measurable`：withDensity_of_n
ot_measurable (κ : Kernel α β) [IsSFiniteKernel κ] (hf : ¬Measurable (Function.u
ncurry f)) : withDensity κ f = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem withDensity_add_left (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (f : α → β → ℝ≥0∞) : withDensity (κ + η) f = withDensity κ f + withDensity η f := by
  by_cases hf : Measurable (Function.uncurry f)
  · ext a s
    simp only [Kernel.withDensity_apply _ hf, add_apply, withDensity_add_measure]
  · simp_rw [withDensity_of_not_measurable _ hf]
    rw [zero_add]
/-
**ProbabilityTheory.Kernel.withDensity_kernel_sum** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：withDensity_kernel_sum [Countable ι] (κ : ι -> Kernel α β) (hκ : forall i,
 IsSFiniteKernel (κ i)) (f : α -> β -> Real>=0∞) : withDensity (Kernel.sum κ) f 
= Kernel.sum fun i => withDensity (κ i) f
参数：κ : ι -> Kernel α β；hκ : forall i, IsSFiniteKernel (κ i)；f : α -> β -> Real>=
0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.withDensity_sum`：withDensity_sum {ι : Type*} {m : Measurab
leSpace α} (μ : ι -> Measure α) (f : α -> Real>=0∞) : (sum μ).withDensity f = su
m fun n => (μ n).wi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.withDensity_of_not_measurable`：withDensity_of_n
ot_measurable (κ : Kernel α β) [IsSFiniteKernel κ] (hf : ¬Measurable (Function.u
ncurry f)) : withDensity κ f = 0
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.sum_zero`：sum_zero [Countable ι] : (Kernel.sum 
fun _ : ι => (0 : Kernel α β)) = 0
-/
theorem withDensity_kernel_sum [Countable ι] (κ : ι → Kernel α β) (hκ : ∀ i, IsSFiniteKernel (κ i))
    (f : α → β → ℝ≥0∞) :
    withDensity (Kernel.sum κ) f = Kernel.sum fun i => withDensity (κ i) f := by
  by_cases hf : Measurable (Function.uncurry f)
  · ext1 a
    simp_rw [sum_apply, Kernel.withDensity_apply _ hf, sum_apply,
      withDensity_sum (fun n => κ n a) (f a)]
  · simp_rw [withDensity_of_not_measurable _ hf]
    exact sum_zero.symm
/-
**ProbabilityTheory.Kernel.withDensity_add_right** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：withDensity_add_right [IsSFiniteKernel κ] {f g : α -> β -> Real>=0∞} (hf :
 Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) : withD
ensity κ (f + g) = withDensity κ f + withDensity κ g
参数：hf : Measurable (Function.uncurry f)；hg : Measurable (Function.uncurry g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `MeasureTheory.withDensity_add_right`：withDensity_add_right (f : α -> Rea
l>=0∞) {g : α -> Real>=0∞} (hg : Measurable g) : μ.withDensity (f + g) = μ.withD
ensity f + μ.withDensity …
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma withDensity_add_right [IsSFiniteKernel κ] {f g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    withDensity κ (f + g) = withDensity κ f + withDensity κ g := by
  ext a
  rw [add_apply, Kernel.withDensity_apply _ hf, Kernel.withDensity_apply _ hg,
    Kernel.withDensity_apply, Pi.add_apply, MeasureTheory.withDensity_add_right]
  · fun_prop
  · exact hf.add hg
/-
**ProbabilityTheory.Kernel.withDensity_sub_add_cancel** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：withDensity_sub_add_cancel [IsSFiniteKernel κ] {f g : α -> β -> Real>=0∞} 
(hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) (h
fg : forall a, g a <=ᵐ[κ a] f a) : withDensity κ (fun a x => f a x - g a x) + wi
thDensity κ g = withDensity κ f
参数：hf : Measurable (Function.uncurry f)；hg : Measurable (Function.uncurry g)；hfg
 : forall a, g a <=ᵐ[κ a] f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.withDensity_add_right`：withDensity_add_right [I
sSFiniteKernel κ] {f g : α -> β -> Real>=0∞} (hf : Measurable (Function.uncurry 
f)) (hg : Measurable (Function.uncur…
· 使用定理 `Measurable.sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ G], 
Meas…
· 使用定理 `ProbabilityTheory.Kernel.withDensity_congr_ae`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.
Kernel α β)   [inst : ProbabilityTh…
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `tsub_add_cancel_iff_le`：tsub_add_cancel_iff_le : b - a + a = b ↔ a <= b
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
lemma withDensity_sub_add_cancel [IsSFiniteKernel κ] {f g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfg : ∀ a, g a ≤ᵐ[κ a] f a) :
    withDensity κ (fun a x ↦ f a x - g a x) + withDensity κ g = withDensity κ f := by
  rw [← withDensity_add_right _ hg]
  swap; · exact hf.sub hg
  refine withDensity_congr_ae κ ((hf.sub hg).add hg) hf (fun a ↦ ?_)
  filter_upwards [hfg a] with x hx
  rwa [Pi.add_apply, Pi.add_apply, tsub_add_cancel_iff_le]
/-
**ProbabilityTheory.Kernel.withDensity_tsum** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：withDensity_tsum [Countable ι] (κ : Kernel α β) [IsSFiniteKernel κ] {f : ι
 -> α -> β -> Real>=0∞} (hf : forall i, Measurable (Function.uncurry (f i))) : w
ithDensity κ (∑' n, f n) = Kernel.sum fun n => withDensity κ (f n)
参数：κ : Kernel α β；hf : forall i, Measurable (Function.uncurry (f i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.summable`：∀ {α : Type u_1} {ι : Type u_4} {X : α → Type u_5} [inst : 
(x : α) → AddCommMonoid (X x)]   [inst_1 : (x : α) → TopologicalSpace (X x)] {L 
:…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.sum_apply'`：sum_apply' [Countable ι] (κ : ι -> 
Kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) : Kernel.sum κ a s = ∑' n
, κ n a s
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply'`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (
κ : ProbabilityTheory.Kernel α β)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsum_apply`：∀ {α : Type u_1} {ι : Type u_4} {X : α → Type u_5} [inst : (
x : α) → AddCommMonoid (X x)]   [inst_1 : (x : α) → TopologicalSpace (X x)] {L :
…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `Measurable.tsum'`：∀ {X : Type u_6} {E : Type u_7} {ι : Type u_8} [inst :
 MeasurableSpace X] [inst_1 : AddCommMonoid E]   [inst_2 : TopologicalSpace E] [
Topolo…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `SummationFilter.instIsCountablyGeneratedFinsetFilterUnconditionalOfCount
able`：∀ (β : Type u_2) [Countable β], (SummationFilter.unconditional β).filter.I
sCountablyGenerated
· 使用定理 `MeasureTheory.lintegral_tsum`：lintegral_tsum [Countable β] {f : β -> α -
> Real>=0∞} (hf : forall i, AEMeasurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i,
 ∫⁻ a, f i a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
theorem withDensity_tsum [Countable ι] (κ : Kernel α β) [IsSFiniteKernel κ] {f : ι → α → β → ℝ≥0∞}
    (hf : ∀ i, Measurable (Function.uncurry (f i))) :
    withDensity κ (∑' n, f n) = Kernel.sum fun n => withDensity κ (f n) := by
  have h_sum_a : ∀ a, Summable fun n => f n a := fun a => Pi.summable.mpr fun b => ENNReal.summable
  have h_sum : Summable fun n => f n := Pi.summable.mpr h_sum_a
  ext a s hs
  rw [sum_apply' _ a hs, Kernel.withDensity_apply' κ _ a s]
  swap
  · have : Function.uncurry (∑' n, f n) = ∑' n, Function.uncurry (f n) := by
      ext1 p
      simp only [Function.uncurry_def]
      rw [tsum_apply h_sum, tsum_apply (h_sum_a _), tsum_apply]
      exact Pi.summable.mpr fun p => ENNReal.summable
    rw [this]
    fun_prop
  have : ∫⁻ b in s, (∑' n, f n) a b ∂κ a = ∫⁻ b in s, ∑' n, (fun b => f n a b) b ∂κ a := by
    congr with b
    rw [tsum_apply h_sum, tsum_apply (h_sum_a a)]
  rw [this, lintegral_tsum fun n => by fun_prop]
  congr with n
  rw [Kernel.withDensity_apply' _ (hf n) a s]

/-- If a kernel `κ` is finite and a function `f : α → β → ℝ≥0∞` is bounded, then `withDensity κ f`
is finite. -/
/-
**ProbabilityTheory.Kernel.isFiniteKernel_withDensity_of_bounded** 是 Mathlib 中的一
个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isFiniteKernel_withDensity_of_bounded (κ : Kernel α β) [IsFiniteKernel κ] 
{B : Real>=0∞} (hB_top : B != ∞) (hf_B : forall a b, f a b <= B) : IsFiniteKerne
l (withDensity κ f)
参数：κ : Kernel α β；hB_top : B != ∞；hf_B : forall a b, f a b <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply'`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (
κ : ProbabilityTheory.Kernel α β)…
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
· 使用定理 `ProbabilityTheory.Kernel.withDensity_of_not_measurable`：withDensity_of_n
ot_measurable (κ : Kernel α β) [IsSFiniteKernel κ] (hf : ¬Measurable (Function.u
ncurry f)) : withDensity κ f = 0

--- 原说明 ---
If a kernel `κ` is finite and a function `f : α → β → ℝ≥0∞` is bounded, then `wi
thDensity κ f`
is finite.
-/
theorem isFiniteKernel_withDensity_of_bounded (κ : Kernel α β) [IsFiniteKernel κ] {B : ℝ≥0∞}
    (hB_top : B ≠ ∞) (hf_B : ∀ a b, f a b ≤ B) : IsFiniteKernel (withDensity κ f) := by
  by_cases hf : Measurable (Function.uncurry f)
  · exact ⟨⟨B * κ.bound, ENNReal.mul_lt_top hB_top.lt_top κ.bound_lt_top, fun a => by
        rw [Kernel.withDensity_apply' κ hf a Set.univ]
        calc
          ∫⁻ b in Set.univ, f a b ∂κ a ≤ ∫⁻ _ in Set.univ, B ∂κ a := lintegral_mono (hf_B a)
          _ = B * κ a Set.univ := by
            simp only [Measure.restrict_univ, MeasureTheory.lintegral_const]
          _ ≤ B * κ.bound := by grw [measure_le_bound]⟩⟩
  · rw [withDensity_of_not_measurable _ hf]
    infer_instance

/-- Auxiliary lemma for `IsSFiniteKernel.withDensity`.
If a kernel `κ` is finite, then `withDensity κ f` is s-finite. -/
/-
**ProbabilityTheory.Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel** 是 Mat
hlib 中的一个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isSFiniteKernel_withDensity_of_isFiniteKernel (κ : Kernel α β) [IsFiniteKe
rnel κ] (hf_ne_top : forall a b, f a b != ∞) : IsSFiniteKernel (withDensity κ f)
参数：κ : Kernel α β；hf_ne_top : forall a b, f a b != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Nat.le_of_ceil_le`：le_of_ceil_le (h : ⌈a⌉₊ <= n) : a <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_natCast`：∀ (n : ℕ), ENNReal.ofReal ↑n = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.le_ofReal_iff_toReal_le`：le_ofReal_iff_toReal_le {a : Real>=0∞} 
{b : Real} (ha : a != ∞) (hb : 0 <= b) : a <= ENNReal.ofReal b ↔ ENNReal.toReal 
a <= b
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.summable`：∀ {α : Type u_1} {ι : Type u_4} {X : α → Type u_5} [inst : 
(x : α) → AddCommMonoid (X x)]   [inst_1 : (x : α) → TopologicalSpace (X x)] {L 
:…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsum_apply`：∀ {α : Type u_1} {ι : Type u_4} {X : α → Type u_5} [inst : (
x : α) → AddCommMonoid (X x)]   [inst_1 : (x : α) → TopologicalSpace (X x)] {L :
…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
（共 67 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `IsSFiniteKernel.withDensity`.
If a kernel `κ` is finite, then `withDensity κ f` is s-finite.
-/
theorem isSFiniteKernel_withDensity_of_isFiniteKernel (κ : Kernel α β) [IsFiniteKernel κ]
    (hf_ne_top : ∀ a b, f a b ≠ ∞) : IsSFiniteKernel (withDensity κ f) := by
  -- We already have that for `f` bounded from above and a `κ` a finite kernel,
  -- `withDensity κ f` is finite. We write any function as a countable sum of bounded
  -- functions, and decompose an s-finite kernel as a sum of finite kernels. We then use that
  -- `withDensity` commutes with sums for both arguments and get a sum of finite kernels.
  by_cases hf : Measurable (Function.uncurry f)
  swap; · rw [withDensity_of_not_measurable _ hf]; infer_instance
  let fs : ℕ → α → β → ℝ≥0∞ := fun n a b => min (f a b) (n + 1) - min (f a b) n
  have h_le : ∀ a b n, ⌈(f a b).toReal⌉₊ ≤ n → f a b ≤ n := by
    intro a b n hn
    have : (f a b).toReal ≤ n := Nat.le_of_ceil_le hn
    rw [← ENNReal.le_ofReal_iff_toReal_le (hf_ne_top a b) _] at this
    · simpa
    · exact n.cast_nonneg
  have h_zero : ∀ a b n, ⌈(f a b).toReal⌉₊ ≤ n → fs n a b = 0 := by
    intro a b n hn
    suffices min (f a b) (n + 1) = f a b ∧ min (f a b) n = f a b by
      simp_rw [fs, this.1, this.2, tsub_self (f a b)]
    exact ⟨min_eq_left ((h_le a b n hn).trans (le_add_of_nonneg_right zero_le_one)),
      min_eq_left (h_le a b n hn)⟩
  have hf_eq_tsum : f = ∑' n, fs n := by
    have h_sum_a : ∀ a, Summable fun n => fs n a :=
      fun _ => Pi.summable.mpr fun _ => ENNReal.summable
    ext a b : 2
    rw [tsum_apply (Pi.summable.mpr h_sum_a), tsum_apply (h_sum_a a),
      ENNReal.tsum_eq_liminf_sum_nat]
    have h_finsetSum : ∀ n, ∑ i ∈ Finset.range n, fs i a b = min (f a b) n := fun n ↦ by
      induction n with
      | zero => simp
      | succ n hn =>
        rw [Finset.sum_range_succ, hn]
        simp [fs]
    simp_rw [h_finsetSum]
    refine (Filter.Tendsto.liminf_eq ?_).symm
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨⌈(f a b).toReal⌉₊, fun n hn => (min_eq_left (h_le a b n hn)).symm⟩
  rw [hf_eq_tsum, withDensity_tsum _ fun n : ℕ => _]
  swap; · fun_prop
  refine isSFiniteKernel_sum (hκs := fun n => ?_)
  suffices IsFiniteKernel (withDensity κ (fs n)) by infer_instance
  refine isFiniteKernel_withDensity_of_bounded _ (ENNReal.coe_ne_top : ↑n + 1 ≠ ∞) fun a b => ?_
  -- After https://github.com/leanprover/lean4/pull/2734, we need to do beta reduction before `norm_cast`
  beta_reduce
  norm_cast
  calc
    fs n a b ≤ min (f a b) (n + 1) := tsub_le_self
    _ ≤ n + 1 := min_le_right _ _
    _ = ↑(n + 1) := by norm_cast

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is everywhere finite,
`withDensity κ f` is s-finite. -/
nonrec theorem IsSFiniteKernel.withDensity (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf_ne_top : ∀ a b, f a b ≠ ∞) : IsSFiniteKernel (withDensity κ f) := by
  have h_eq_sum : withDensity κ f = Kernel.sum fun i => withDensity (seq κ i) f := by
    rw [← withDensity_kernel_sum _ _]
    congr
    exact (kernel_sum_seq κ).symm
  rw [h_eq_sum]
  exact isSFiniteKernel_sum (hκs := fun n =>
    isSFiniteKernel_withDensity_of_isFiniteKernel (seq κ n) hf_ne_top)

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0`, `withDensity κ f` is s-finite. -/
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0`, `withDensity κ f` i
s s-finite.
-/
instance (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → β → ℝ≥0) :
    IsSFiniteKernel (withDensity κ fun a b => f a b) :=
  IsSFiniteKernel.withDensity κ fun _ _ => ENNReal.coe_ne_top

nonrec lemma withDensity_mul [IsSFiniteKernel κ] {f : α → β → ℝ≥0} {g : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    withDensity κ (fun a x ↦ f a x * g a x)
      = withDensity (withDensity κ fun a x ↦ f a x) g := by
  ext a : 1
  rw [Kernel.withDensity_apply]
  swap; · fun_prop
  change (Measure.withDensity (κ a) ((fun x ↦ (f a x : ℝ≥0∞)) * (fun x ↦ (g a x : ℝ≥0∞)))) =
      (withDensity (withDensity κ fun a x ↦ f a x) g) a
  rw [withDensity_mul]
  · rw [Kernel.withDensity_apply _ hg, Kernel.withDensity_apply]
    exact measurable_coe_nnreal_ennreal.comp hf
  · fun_prop
  · fun_prop

end ProbabilityTheory.Kernel

