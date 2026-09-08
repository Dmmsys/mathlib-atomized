/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Basic

/-!
# Map of a kernel by a measurable function

We define the map and comap of a kernel along a measurable function, as well as some often useful
particular cases.

## Main definitions

Kernels built from other kernels:
* `map (κ : Kernel α β) (f : β → γ) : Kernel α γ`
  `∫⁻ c, g c ∂(map κ f a) = ∫⁻ b, g (f b) ∂(κ a)`
* `comap (κ : Kernel α β) (f : γ → α) (hf : Measurable f) : Kernel γ β`
  `∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c))`

## Main statements

* `lintegral_map`, `lintegral_comap`: Lebesgue integral of a function against the map or comap of
  a kernel.

-/

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

section MapComap

/-! ### map, comap -/


variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : β → γ} {g : γ → α}

/-- The pushforward of a kernel along a measurable function. This is an implementation detail,
use `map κ f` instead. -/
/-
**ProbabilityTheory.Kernel.mapOfMeasurable** 是 Mathlib 中的一个定义，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：mapOfMeasurable (κ : Kernel α β) (f : β -> γ) (hf : Measurable f) : Kernel
 α γ where toFun a
参数：κ : Kernel α β；f : β -> γ；hf : Measurable f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward of a kernel along a measurable function. This is an implementati
on detail,
use `map κ f` instead.
-/
noncomputable def mapOfMeasurable (κ : Kernel α β) (f : β → γ) (hf : Measurable f) :
    Kernel α γ where
  toFun a := (κ a).map f
  measurable' := by fun_prop

open scoped Classical in
/-- The pushforward of a kernel along a function.
If the function is not measurable, we use zero instead. This choice of junk
value ensures that typeclass inference can infer that the `map` of a kernel
satisfying `IsZeroOrMarkovKernel` again satisfies this property. -/
/-
**ProbabilityTheory.Kernel.map** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Kern
el`。
形式化陈述：map [MeasurableSpace γ] (κ : Kernel α β) (f : β -> γ) : Kernel α γ
参数：κ : Kernel α β；f : β -> γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward of a kernel along a function.
If the function is not measurable, we use zero instead. This choice of junk
value ensures that typeclass inference can infer that the `map` of a kernel
satisfying `IsZeroOrMarkovKernel` again satisfies this property.
-/
noncomputable def map [MeasurableSpace γ] (κ : Kernel α β) (f : β → γ) : Kernel α γ :=
  if hf : Measurable f then mapOfMeasurable κ f hf else 0
/-
**ProbabilityTheory.Kernel.map_of_not_measurable** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：map_of_not_measurable (κ : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f))
 : map κ f = 0
参数：κ : Kernel α β；hf : ¬(Measurable f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_of_not_measurable (κ : Kernel α β) {f : β → γ} (hf : ¬(Measurable f)) :
    map κ f = 0 := by
  simp [map, hf]
/-
**ProbabilityTheory.Kernel.mapOfMeasurable_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) {f : β → γ} (hf : Measurable f),   κ.mapOfMeasurable f hf = κ.map f
参数：κ : ProbabilityTheory.Kernel α β；hf : Measurable f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem mapOfMeasurable_eq_map (κ : Kernel α β) {f : β → γ} (hf : Measurable f) :
    mapOfMeasurable κ f hf = map κ f := by
  simp [map, hf]
/-
**ProbabilityTheory.Kernel.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：map_apply (κ : Kernel α β) (hf : Measurable f) (a : α) : map κ f a = (κ a)
.map f
参数：κ : Kernel α β；hf : Measurable f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_apply (κ : Kernel α β) (hf : Measurable f) (a : α) : map κ f a = (κ a).map f := by
  simp only [map, hf, ↓reduceDIte, mapOfMeasurable, coe_mk]
/-
**ProbabilityTheory.Kernel.map_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：map_apply' (κ : Kernel α β) (hf : Measurable f) (a : α) {s : Set γ} (hs : 
MeasurableSet s) : map κ f a s = κ a (f ⁻¹' s)
参数：κ : Kernel α β；hf : Measurable f；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
-/
theorem map_apply' (κ : Kernel α β) (hf : Measurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    map κ f a s = κ a (f ⁻¹' s) := by rw [map_apply _ hf, Measure.map_apply hf hs]
/-
**ProbabilityTheory.Kernel.map_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：map_comp_right (κ : Kernel α β) {f : β -> γ} (hf : Measurable f) {g : γ ->
 δ} (hg : Measurable g) : κ.map (g ∘ f) = (κ.map f).map g
参数：κ : Kernel α β；hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
-/
lemma map_comp_right (κ : Kernel α β) {f : β → γ} (hf : Measurable f) {g : γ → δ}
    (hg : Measurable g) : κ.map (g ∘ f) = (κ.map f).map g := by
  ext1 x
  rw [map_apply _ hg, map_apply _ hf, Measure.map_map hg hf, ← map_apply _ (hg.comp hf)]

@[simp]
/-
**ProbabilityTheory.Kernel.map_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：map_zero : Kernel.map (0 : Kernel α β) f = 0
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
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.map_of_not_measurable`：map_of_not_measurable (κ
 : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f)) : map κ f = 0
-/
lemma map_zero : Kernel.map (0 : Kernel α β) f = 0 := by
  ext
  by_cases hf : Measurable f
  · simp [map_apply, hf]
  · simp [map_of_not_measurable _ hf]

@[simp]
/-
**ProbabilityTheory.Kernel.map_id** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.K
ernel`。
形式化陈述：map_id (κ : Kernel α β) : map κ id = κ
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
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
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id (κ : Kernel α β) : map κ id = κ := by
  ext a
  simp [map_apply, measurable_id]

@[simp]
/-
**ProbabilityTheory.Kernel.map_id'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.
Kernel`。
形式化陈述：map_id' (κ : Kernel α β) : map κ (fun a => a) = κ
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.map_id`：map_id (κ : Kernel α β) : map κ id = κ
-/
lemma map_id' (κ : Kernel α β) : map κ (fun a ↦ a) = κ := map_id κ

nonrec theorem lintegral_map (κ : Kernel α β) (hf : Measurable f) (a : α) {g' : γ → ℝ≥0∞}
    (hg : Measurable g') : ∫⁻ b, g' b ∂map κ f a = ∫⁻ a, g' (f a) ∂κ a := by
  rw [map_apply _ hf, lintegral_map hg hf]
/-
**ProbabilityTheory.Kernel.map_apply_eq_iff_map_symm_apply_eq** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：map_apply_eq_iff_map_symm_apply_eq (κ : Kernel α β) {f : β ≃ᵐ γ} (η : Kern
el α γ) : κ.map f = η ↔ κ = η.map f.symm
参数：κ : Kernel α β；η : Kernel α γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq`：map_apply_eq_iff_map
_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ μ = ν.map e.symm
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_apply_eq_iff_map_symm_apply_eq (κ : Kernel α β) {f : β ≃ᵐ γ} (η : Kernel α γ) :
    κ.map f = η ↔ κ = η.map f.symm := by
  simp_rw [Kernel.ext_iff, map_apply _ f.measurable, map_apply _ f.symm.measurable,
    f.map_apply_eq_iff_map_symm_apply_eq]
/-
**ProbabilityTheory.Kernel.sum_map_seq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：sum_map_seq (κ : Kernel α β) [IsSFiniteKernel κ] (f : β -> γ) : (Kernel.su
m fun n => map (seq κ n) f) = map κ f
参数：κ : Kernel α β；f : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.sum_apply`：sum_apply [Countable ι] (κ : ι -> Ke
rnel α β) (a : α) : Kernel.sum κ a = Measure.sum fun n => κ n a
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.measure_sum_seq`：measure_sum_seq (κ : Kernel α 
β) [h : IsSFiniteKernel κ] (a : α) : (Measure.sum fun n => seq κ n a) = κ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `ProbabilityTheory.Kernel.map_of_not_measurable`：map_of_not_measurable (κ
 : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f)) : map κ f = 0
· 使用定理 `ProbabilityTheory.Kernel.sum_zero`：sum_zero [Countable ι] : (Kernel.sum 
fun _ : ι => (0 : Kernel α β)) = 0
-/
theorem sum_map_seq (κ : Kernel α β) [IsSFiniteKernel κ] (f : β → γ) :
    (Kernel.sum fun n => map (seq κ n) f) = map κ f := by
  by_cases hf : Measurable f
  · ext a s hs
    rw [Kernel.sum_apply, map_apply' κ hf a hs, Measure.sum_apply _ hs, ← measure_sum_seq κ,
      Measure.sum_apply _ (hf hs)]
    simp_rw [map_apply' _ hf _ hs]
  · simp [map_of_not_measurable _ hf]
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.map** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} {f : β → γ} (κ : ProbabilityTh
eory.Kernel α β) [ProbabilityTheory.IsMarkovKernel κ],   Measurable f → Probabil
ityTheory.IsMarkovKernel (κ.map f)
参数：κ : ProbabilityTheory.Kernel α β；κ.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
-/
lemma IsMarkovKernel.map (κ : Kernel α β) [IsMarkovKernel κ] (hf : Measurable f) :
    IsMarkovKernel (map κ f) :=
  ⟨fun a => ⟨by rw [map_apply' κ hf a MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩⟩
/-
**ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.map** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.IsZeroOrMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsZeroOrMarkovKernel κ] (f : β → γ),   ProbabilityTheory
.IsZeroOrMarkovKernel (κ.map f)
参数：κ : ProbabilityTheory.Kernel α β；f : β → γ；κ.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.eq_zero_or_isMarkovKernel`：eq_zero_or_isMarkovKernel (
κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] : κ = 0 ∨ IsMarkovKernel κ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.map_zero`：map_zero : Kernel.map (0 : Kernel α β
) f = 0
· 使用定理 `ProbabilityTheory.instIsZeroOrMarkovKernelOfNatKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   ProbabilityT
heory.IsZeroOrMarkovKernel 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} {f : β → γ} (κ :…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.map_of_not_measurable`：map_of_not_measurable (κ
 : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f)) : map κ f = 0
-/
instance IsZeroOrMarkovKernel.map (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (f : β → γ) :
    IsZeroOrMarkovKernel (map κ f) := by
  by_cases hf : Measurable f
  · rcases eq_zero_or_isMarkovKernel κ with rfl | h
    · simp only [map_zero]; infer_instance
    · have := IsMarkovKernel.map κ hf; infer_instance
  · simp only [map_of_not_measurable _ hf]; infer_instance
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.map** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsFiniteKernel κ] (f : β → γ),   ProbabilityTheory.IsFin
iteKernel (κ.map f)
参数：κ : ProbabilityTheory.Kernel α β；f : β → γ；κ.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.map_of_not_measurable`：map_of_not_measurable (κ
 : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f)) : map κ f = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
instance IsFiniteKernel.map (κ : Kernel α β) [IsFiniteKernel κ] (f : β → γ) :
    IsFiniteKernel (map κ f) := by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  by_cases hf : Measurable f
  · rw [map_apply' κ hf a MeasurableSet.univ]
    exact measure_le_bound κ a _
  · simp [map_of_not_measurable _ hf]
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.map** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsSFiniteKernel κ] (f : β → γ),   ProbabilityTheory.IsSF
initeKernel (κ.map f)
参数：κ : ProbabilityTheory.Kernel α β；f : β → γ；κ.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} (κ : Probability…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.sum_map_seq`：sum_map_seq (κ : Kernel α β) [IsSF
initeKernel κ] (f : β -> γ) : (Kernel.sum fun n => map (seq κ n) f) = map κ f
-/
instance IsSFiniteKernel.map (κ : Kernel α β) [IsSFiniteKernel κ] (f : β → γ) :
    IsSFiniteKernel (map κ f) :=
  ⟨⟨fun n => Kernel.map (seq κ n) f, inferInstance, (sum_map_seq κ f).symm⟩⟩

@[simp]
/-
**ProbabilityTheory.Kernel.map_const** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：map_const (μ : Measure α) {f : α -> β} (hf : Measurable f) : map (const γ 
μ) f = const γ (μ.map f)
参数：μ : Measure α；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
-/
lemma map_const (μ : Measure α) {f : α → β} (hf : Measurable f) :
    map (const γ μ) f = const γ (μ.map f) := by
  ext x s hs
  rw [map_apply' _ hf _ hs, const_apply, const_apply, Measure.map_apply hf hs]

/-- Pullback of a kernel, such that for each set s `comap κ g hg c s = κ (g c) s`.
We include measurability in the assumptions instead of using junk values
to make sure that typeclass inference can infer that the `comap` of a Markov kernel
is again a Markov kernel. -/
/-
**ProbabilityTheory.Kernel.comap** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ke
rnel`。
形式化陈述：comap (κ : Kernel α β) (g : γ -> α) (hg : Measurable g) : Kernel γ β where
 toFun a
参数：κ : Kernel α β；g : γ -> α；hg : Measurable g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback of a kernel, such that for each set s `comap κ g hg c s = κ (g c) s`.
We include measurability in the assumptions instead of using junk values
to make sure that typeclass inference can infer that the `comap` of a Markov ker
nel
is again a Markov kernel.
-/
def comap (κ : Kernel α β) (g : γ → α) (hg : Measurable g) : Kernel γ β where
  toFun a := κ (g a)
  measurable' := κ.measurable.comp hg

@[simp, norm_cast]
/-
**ProbabilityTheory.Kernel.coe_comap** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：coe_comap (κ : Kernel α β) (g : γ -> α) (hg : Measurable g) : κ.comap g hg
 = κ ∘ g
参数：κ : Kernel α β；g : γ -> α；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comap (κ : Kernel α β) (g : γ → α) (hg : Measurable g) : κ.comap g hg = κ ∘ g := rfl
/-
**ProbabilityTheory.Kernel.comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：comap_apply (κ : Kernel α β) (hg : Measurable g) (c : γ) : comap κ g hg c 
= κ (g c)
参数：κ : Kernel α β；hg : Measurable g；c : γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_apply (κ : Kernel α β) (hg : Measurable g) (c : γ) : comap κ g hg c = κ (g c) :=
  rfl
/-
**ProbabilityTheory.Kernel.comap_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：comap_apply' (κ : Kernel α β) (hg : Measurable g) (c : γ) (s : Set β) : co
map κ g hg c s = κ (g c) s
参数：κ : Kernel α β；hg : Measurable g；c : γ；s : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_apply' (κ : Kernel α β) (hg : Measurable g) (c : γ) (s : Set β) :
    comap κ g hg c s = κ (g c) s :=
  rfl

@[simp]
/-
**ProbabilityTheory.Kernel.comap_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：comap_zero (hg : Measurable g) : Kernel.comap (0 : Kernel α β) g hg = 0
参数：hg : Measurable g。
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
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comap_zero (hg : Measurable g) : Kernel.comap (0 : Kernel α β) g hg = 0 := by
  ext; simp

@[simp]
/-
**ProbabilityTheory.Kernel.comap_id** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：comap_id (κ : Kernel α β) : comap κ id measurable_id = κ
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comap_id (κ : Kernel α β) : comap κ id measurable_id = κ := by ext; simp

@[simp]
/-
**ProbabilityTheory.Kernel.comap_id'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：comap_id' (κ : Kernel α β) : comap κ (fun a => a) measurable_id = κ
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.comap_id`：comap_id (κ : Kernel α β) : comap κ i
d measurable_id = κ
-/
lemma comap_id' (κ : Kernel α β) : comap κ (fun a ↦ a) measurable_id = κ := comap_id κ
/-
**ProbabilityTheory.Kernel.lintegral_comap** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：lintegral_comap (κ : Kernel α β) (hg : Measurable g) (c : γ) (g' : β -> Re
al>=0∞) : ∫⁻ b, g' b ∂comap κ g hg c = ∫⁻ b, g' b ∂κ (g c)
参数：κ : Kernel α β；hg : Measurable g；c : γ；g' : β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lintegral_comap (κ : Kernel α β) (hg : Measurable g) (c : γ) (g' : β → ℝ≥0∞) :
    ∫⁻ b, g' b ∂comap κ g hg c = ∫⁻ b, g' b ∂κ (g c) :=
  rfl
/-
**ProbabilityTheory.Kernel.sum_comap_seq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：sum_comap_seq (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) : (
Kernel.sum fun n => comap (seq κ n) g hg) = comap κ g hg
参数：κ : Kernel α β；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.sum_apply`：sum_apply [Countable ι] (κ : ι -> Ke
rnel α β) (a : α) : Kernel.sum κ a = Measure.sum fun n => κ n a
· 使用定理 `ProbabilityTheory.Kernel.comap_apply'`：comap_apply' (κ : Kernel α β) (hg
 : Measurable g) (c : γ) (s : Set β) : comap κ g hg c s = κ (g c) s
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.measure_sum_seq`：measure_sum_seq (κ : Kernel α 
β) [h : IsSFiniteKernel κ] (a : α) : (Measure.sum fun n => seq κ n a) = κ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_comap_seq (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) :
    (Kernel.sum fun n => comap (seq κ n) g hg) = comap κ g hg := by
  ext a s hs
  rw [Kernel.sum_apply, comap_apply' κ hg a s, Measure.sum_apply _ hs, ← measure_sum_seq κ,
    Measure.sum_apply _ hs]
  simp_rw [comap_apply' _ hg _ s]
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.comap** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} {g : γ → α} (κ : ProbabilityTh
eory.Kernel α β) [ProbabilityTheory.IsMarkovKernel κ]   (hg : Measurable g), Pro
babilityTheory.IsMarkovKernel (κ.comap g hg)
参数：κ : ProbabilityTheory.Kernel α β；hg : Measurable g；κ.comap g hg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comap_apply'`：comap_apply' (κ : Kernel α β) (hg
 : Measurable g) (c : γ) (s : Set β) : comap κ g hg c s = κ (g c) s
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
-/
instance IsMarkovKernel.comap (κ : Kernel α β) [IsMarkovKernel κ] (hg : Measurable g) :
    IsMarkovKernel (comap κ g hg) :=
  ⟨fun a => ⟨by rw [comap_apply' κ hg a Set.univ, measure_univ]⟩⟩
/-
**ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.comap** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel.IsZeroOrMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} {g : γ → α} (κ : ProbabilityTh
eory.Kernel α β) [ProbabilityTheory.IsZeroOrMarkovKernel κ]   (hg : Measurable g
), ProbabilityTheory.IsZeroOrMarkovKernel (κ.comap g hg)
参数：κ : ProbabilityTheory.Kernel α β；hg : Measurable g；κ.comap g hg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.eq_zero_or_isMarkovKernel`：eq_zero_or_isMarkovKernel (
κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] : κ = 0 ∨ IsMarkovKernel κ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.comap_zero`：comap_zero (hg : Measurable g) : Ke
rnel.comap (0 : Kernel α β) g hg = 0
· 使用定理 `ProbabilityTheory.instIsZeroOrMarkovKernelOfNatKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   ProbabilityT
heory.IsZeroOrMarkovKernel 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.comap`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} {g : γ → α} (κ :…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
-/
instance IsZeroOrMarkovKernel.comap (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (hg : Measurable g) :
    IsZeroOrMarkovKernel (comap κ g hg) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [comap_zero]; infer_instance
  · have := IsMarkovKernel.comap κ hg; infer_instance
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.comap** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} {g : γ → α} (κ : ProbabilityTh
eory.Kernel α β) [ProbabilityTheory.IsFiniteKernel κ]   (hg : Measurable g), Pro
babilityTheory.IsFiniteKernel (κ.comap g hg)
参数：κ : ProbabilityTheory.Kernel α β；hg : Measurable g；κ.comap g hg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comap_apply'`：comap_apply' (κ : Kernel α β) (hg
 : Measurable g) (c : γ) (s : Set β) : comap κ g hg c s = κ (g c) s
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
-/
instance IsFiniteKernel.comap (κ : Kernel α β) [IsFiniteKernel κ] (hg : Measurable g) :
    IsFiniteKernel (comap κ g hg) := by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [comap_apply' κ hg a Set.univ]
  exact measure_le_bound κ _ _
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.comap** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} {g : γ → α} (κ : ProbabilityTh
eory.Kernel α β) [ProbabilityTheory.IsSFiniteKernel κ]   (hg : Measurable g), Pr
obabilityTheory.IsSFiniteKernel (κ.comap g hg)
参数：κ : ProbabilityTheory.Kernel α β；hg : Measurable g；κ.comap g hg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comap`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} {g : γ → α} (κ :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.sum_comap_seq`：sum_comap_seq (κ : Kernel α β) [
IsSFiniteKernel κ] (hg : Measurable g) : (Kernel.sum fun n => comap (seq κ n) g 
hg) = comap κ g hg
-/
instance IsSFiniteKernel.comap (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) :
    IsSFiniteKernel (comap κ g hg) :=
  ⟨⟨fun n => Kernel.comap (seq κ n) g hg, inferInstance, (sum_comap_seq κ hg).symm⟩⟩
/-
**ProbabilityTheory.Kernel.comap_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：comap_comp_right (κ : Kernel α β) {f : δ -> γ} (hf : Measurable f) (hg : M
easurable g) : comap κ (g ∘ f) (hg.comp hf) = (comap κ g hg).comap f hf
参数：κ : Kernel α β；hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comap_comp_right (κ : Kernel α β) {f : δ → γ} (hf : Measurable f) (hg : Measurable g) :
    comap κ (g ∘ f) (hg.comp hf) = (comap κ g hg).comap f hf := by ext; simp
/-
**ProbabilityTheory.Kernel.comap_map_comm** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：comap_map_comm (κ : Kernel β γ) {f : α -> β} {g : γ -> δ} (hf : Measurable
 f) (hg : Measurable g) : comap (map κ g) f hf = map (comap κ f hf) g
参数：κ : Kernel β γ；hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comap_apply`：comap_apply (κ : Kernel α β) (hg :
 Measurable g) (c : γ) : comap κ g hg c = κ (g c)
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
-/
lemma comap_map_comm (κ : Kernel β γ) {f : α → β} {g : γ → δ}
    (hf : Measurable f) (hg : Measurable g) :
    comap (map κ g) f hf = map (comap κ f hf) g := by
  ext x s _
  rw [comap_apply, map_apply _ hg, map_apply _ hg, comap_apply]

end MapComap

@[simp]
/-
**ProbabilityTheory.Kernel.id_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.K
ernel`。
形式化陈述：id_map {f : α -> β} (hf : Measurable f) : Kernel.id.map f = deterministic 
f hf
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
· 使用定理 `MeasureTheory.Measure.map_dirac'`：map_dirac' {f : α -> β} (hf : Measurab
le f) (a : α) : (dirac a).map f = dirac (f a)
-/
lemma id_map {f : α → β} (hf : Measurable f) : Kernel.id.map f = deterministic f hf := by
  ext
  rw [Kernel.map_apply _ hf, Kernel.deterministic_apply, Kernel.id_apply, Measure.map_dirac' hf]

@[simp]
/-
**ProbabilityTheory.Kernel.id_comap** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：id_comap {f : α -> β} (hf : Measurable f) : Kernel.id.comap f hf = determi
nistic f hf
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comap_apply`：comap_apply (κ : Kernel α β) (hg :
 Measurable g) (c : γ) : comap κ g hg c = κ (g c)
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
-/
lemma id_comap {f : α → β} (hf : Measurable f) : Kernel.id.comap f hf = deterministic f hf := by
  ext
  rw [Kernel.comap_apply _ hf, Kernel.deterministic_apply, Kernel.id_apply]
/-
**ProbabilityTheory.Kernel.deterministic_map** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：deterministic_map {f : α -> β} (hf : Measurable f) {g : β -> γ} (hg : Meas
urable g) : (deterministic f hf).map g = deterministic (g ∘ f) (hg.comp hf)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.id_map`：id_map {f : α -> β} (hf : Measurable f)
 : Kernel.id.map f = deterministic f hf
· 使用引理 `ProbabilityTheory.Kernel.map_comp_right`：map_comp_right (κ : Kernel α β)
 {f : β -> γ} (hf : Measurable f) {g : γ -> δ} (hg : Measurable g) : κ.map (g ∘ 
f) = (κ.map f).map g
-/
lemma deterministic_map {f : α → β} (hf : Measurable f) {g : β → γ} (hg : Measurable g) :
    (deterministic f hf).map g = deterministic (g ∘ f) (hg.comp hf) := by
  rw [← id_map, ← map_comp_right _ hf hg, id_map]

section FstSnd

variable {δ : Type*} {mδ : MeasurableSpace δ}

/-- Define a `Kernel (γ × α) β` from a `Kernel α β` by taking the comap of the projection. -/
/-
**ProbabilityTheory.Kernel.prodMkLeft** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) : Kernel (γ × 
α) β
参数：γ : Type*；κ : Kernel α β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)

--- 原说明 ---
Define a `Kernel (γ × α) β` from a `Kernel α β` by taking the comap of the proje
ction.
-/
def prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) : Kernel (γ × α) β :=
  comap κ Prod.snd measurable_snd

/-- Define a `Kernel (α × γ) β` from a `Kernel α β` by taking the comap of the projection. -/
/-
**ProbabilityTheory.Kernel.prodMkRight** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：prodMkRight (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) : Kernel (α ×
 γ) β
参数：γ : Type*；κ : Kernel α β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)

--- 原说明 ---
Define a `Kernel (α × γ) β` from a `Kernel α β` by taking the comap of the proje
ction.
-/
def prodMkRight (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) : Kernel (α × γ) β :=
  comap κ Prod.fst measurable_fst

@[simp]
/-
**ProbabilityTheory.Kernel.prodMkLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：prodMkLeft_apply (κ : Kernel α β) (ca : γ × α) : prodMkLeft γ κ ca = κ ca.
snd
参数：κ : Kernel α β；ca : γ × α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMkLeft_apply (κ : Kernel α β) (ca : γ × α) : prodMkLeft γ κ ca = κ ca.snd :=
  rfl

@[simp]
/-
**ProbabilityTheory.Kernel.prodMkRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：prodMkRight_apply (κ : Kernel α β) (ca : α × γ) : prodMkRight γ κ ca = κ c
a.fst
参数：κ : Kernel α β；ca : α × γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMkRight_apply (κ : Kernel α β) (ca : α × γ) : prodMkRight γ κ ca = κ ca.fst := rfl
/-
**ProbabilityTheory.Kernel.prodMkLeft_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：prodMkLeft_apply' (κ : Kernel α β) (ca : γ × α) (s : Set β) : prodMkLeft γ
 κ ca s = κ ca.snd s
参数：κ : Kernel α β；ca : γ × α；s : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMkLeft_apply' (κ : Kernel α β) (ca : γ × α) (s : Set β) :
    prodMkLeft γ κ ca s = κ ca.snd s :=
  rfl
/-
**ProbabilityTheory.Kernel.prodMkRight_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：prodMkRight_apply' (κ : Kernel α β) (ca : α × γ) (s : Set β) : prodMkRight
 γ κ ca s = κ ca.fst s
参数：κ : Kernel α β；ca : α × γ；s : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMkRight_apply' (κ : Kernel α β) (ca : α × γ) (s : Set β) :
    prodMkRight γ κ ca s = κ ca.fst s := rfl

@[simp]
/-
**ProbabilityTheory.Kernel.prodMkLeft_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：prodMkLeft_zero : Kernel.prodMkLeft α (0 : Kernel β γ) = 0
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
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodMkLeft_zero : Kernel.prodMkLeft α (0 : Kernel β γ) = 0 := by
  ext x s _; simp

@[simp]
/-
**ProbabilityTheory.Kernel.prodMkRight_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：prodMkRight_zero : Kernel.prodMkRight α (0 : Kernel β γ) = 0
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
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodMkRight_zero : Kernel.prodMkRight α (0 : Kernel β γ) = 0 := by
  ext x s _; simp

@[simp]
/-
**ProbabilityTheory.Kernel.prodMkLeft_add** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：prodMkLeft_add (κ η : Kernel α β) : prodMkLeft γ (κ + η) = prodMkLeft γ κ 
+ prodMkLeft γ η
参数：κ η : Kernel α β。
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
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodMkLeft_add (κ η : Kernel α β) :
    prodMkLeft γ (κ + η) = prodMkLeft γ κ + prodMkLeft γ η := by ext; simp

@[simp]
/-
**ProbabilityTheory.Kernel.prodMkRight_add** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：prodMkRight_add (κ η : Kernel α β) : prodMkRight γ (κ + η) = prodMkRight γ
 κ + prodMkRight γ η
参数：κ η : Kernel α β。
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
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodMkRight_add (κ η : Kernel α β) :
    prodMkRight γ (κ + η) = prodMkRight γ κ + prodMkRight γ η := by ext; simp
/-
**ProbabilityTheory.Kernel.sum_prodMkLeft** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：sum_prodMkLeft {ι : Type*} [Countable ι] {κ : ι -> Kernel α β} : Kernel.su
m (fun i => Kernel.prodMkLeft γ (κ i)) = Kernel.prodMkLeft γ (Kernel.sum κ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_prodMkLeft {ι : Type*} [Countable ι] {κ : ι → Kernel α β} :
    Kernel.sum (fun i ↦ Kernel.prodMkLeft γ (κ i)) = Kernel.prodMkLeft γ (Kernel.sum κ) := by
  ext
  simp_rw [sum_apply, prodMkLeft_apply, sum_apply]
/-
**ProbabilityTheory.Kernel.sum_prodMkRight** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：sum_prodMkRight {ι : Type*} [Countable ι] {κ : ι -> Kernel α β} : Kernel.s
um (fun i => Kernel.prodMkRight γ (κ i)) = Kernel.prodMkRight γ (Kernel.sum κ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_prodMkRight {ι : Type*} [Countable ι] {κ : ι → Kernel α β} :
    Kernel.sum (fun i ↦ Kernel.prodMkRight γ (κ i)) = Kernel.prodMkRight γ (Kernel.sum κ) := by
  ext
  simp_rw [sum_apply, prodMkRight_apply, sum_apply]
/-
**ProbabilityTheory.Kernel.lintegral_prodMkLeft** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：lintegral_prodMkLeft (κ : Kernel α β) (ca : γ × α) (g : β -> Real>=0∞) : ∫
⁻ b, g b ∂prodMkLeft γ κ ca = ∫⁻ b, g b ∂κ ca.snd
参数：κ : Kernel α β；ca : γ × α；g : β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lintegral_prodMkLeft (κ : Kernel α β) (ca : γ × α) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂prodMkLeft γ κ ca = ∫⁻ b, g b ∂κ ca.snd := rfl
/-
**ProbabilityTheory.Kernel.lintegral_prodMkRight** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：lintegral_prodMkRight (κ : Kernel α β) (ca : α × γ) (g : β -> Real>=0∞) : 
∫⁻ b, g b ∂prodMkRight γ κ ca = ∫⁻ b, g b ∂κ ca.fst
参数：κ : Kernel α β；ca : α × γ；g : β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lintegral_prodMkRight (κ : Kernel α β) (ca : α × γ) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂prodMkRight γ κ ca = ∫⁻ b, g b ∂κ ca.fst := rfl
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.prodMkLeft** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsMarkovKernel κ],   ProbabilityTheory.IsMarkovKernel (P
robabilityTheory.Kernel.prodMkLeft γ κ)
参数：κ : ProbabilityTheory.Kernel α β；ProbabilityTheory.Kernel.prodMkLeft γ κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prodMkLeft.eq_1`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (γ : Type u_5)   [inst : Mea
surableSpace γ] (κ : Probabili…
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.comap`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsMarkovKernel.prodMkLeft (κ : Kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.prodMkRight** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsMarkovKernel κ],   ProbabilityTheory.IsMarkovKernel (P
robabilityTheory.Kernel.prodMkRight γ κ)
参数：κ : ProbabilityTheory.Kernel α β；ProbabilityTheory.Kernel.prodMkRight γ κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prodMkRight.eq_1`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (γ : Type u_5)   [inst : Me
asurableSpace γ] (κ : Probabili…
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.comap`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsMarkovKernel.prodMkRight (κ : Kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance
/-
**ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.prodMkLeft** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsZeroOrMarkovKernel κ],   ProbabilityTheory.IsZeroOrMar
kovKernel (ProbabilityTheory.Kernel.prodMkLeft γ κ)
参数：κ : ProbabilityTheory.Kernel α β；ProbabilityTheory.Kernel.prodMkLeft γ κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prodMkLeft.eq_1`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (γ : Type u_5)   [inst : Mea
surableSpace γ] (κ : Probabili…
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.comap`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   
{mγ : MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsZeroOrMarkovKernel.prodMkLeft (κ : Kernel α β) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance
/-
**ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.prodMkRight** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsZeroOrMarkovKernel κ],   ProbabilityTheory.IsZeroOrMar
kovKernel (ProbabilityTheory.Kernel.prodMkRight γ κ)
参数：κ : ProbabilityTheory.Kernel α β；ProbabilityTheory.Kernel.prodMkRight γ κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prodMkRight.eq_1`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (γ : Type u_5)   [inst : Me
asurableSpace γ] (κ : Probabili…
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.comap`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   
{mγ : MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsZeroOrMarkovKernel.prodMkRight (κ : Kernel α β) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.prodMkLeft** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsFiniteKernel κ],   ProbabilityTheory.IsFiniteKernel (P
robabilityTheory.Kernel.prodMkLeft γ κ)
参数：κ : ProbabilityTheory.Kernel α β；ProbabilityTheory.Kernel.prodMkLeft γ κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prodMkLeft.eq_1`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (γ : Type u_5)   [inst : Mea
surableSpace γ] (κ : Probabili…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comap`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsFiniteKernel.prodMkLeft (κ : Kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.prodMkRight** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsFiniteKernel κ],   ProbabilityTheory.IsFiniteKernel (P
robabilityTheory.Kernel.prodMkRight γ κ)
参数：κ : ProbabilityTheory.Kernel α β；ProbabilityTheory.Kernel.prodMkRight γ κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prodMkRight.eq_1`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (γ : Type u_5)   [inst : Me
asurableSpace γ] (κ : Probabili…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comap`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsFiniteKernel.prodMkRight (κ : Kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsSFiniteKernel κ],   ProbabilityTheory.IsSFiniteKernel 
(ProbabilityTheory.Kernel.prodMkLeft γ κ)
参数：κ : ProbabilityTheory.Kernel α β；ProbabilityTheory.Kernel.prodMkLeft γ κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prodMkLeft.eq_1`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (γ : Type u_5)   [inst : Mea
surableSpace γ] (κ : Probabili…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsSFiniteKernel.prodMkLeft (κ : Kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkRight** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsSFiniteKernel κ],   ProbabilityTheory.IsSFiniteKernel 
(ProbabilityTheory.Kernel.prodMkRight γ κ)
参数：κ : ProbabilityTheory.Kernel α β；ProbabilityTheory.Kernel.prodMkRight γ κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prodMkRight.eq_1`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (γ : Type u_5)   [inst : Me
asurableSpace γ] (κ : Probabili…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsSFiniteKernel.prodMkRight (κ : Kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance
/-
**ProbabilityTheory.Kernel.isSFiniteKernel_prodMkLeft_unit** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isSFiniteKernel_prodMkLeft_unit {κ : Kernel α β} : IsSFiniteKernel (prodMk
Left Unit κ) ↔ IsSFiniteKernel κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
-/
lemma isSFiniteKernel_prodMkLeft_unit {κ : Kernel α β} :
    IsSFiniteKernel (prodMkLeft Unit κ) ↔ IsSFiniteKernel κ := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  change IsSFiniteKernel ((prodMkLeft Unit κ).comap (fun a ↦ ((), a)) (by fun_prop))
  infer_instance
/-
**ProbabilityTheory.Kernel.isSFiniteKernel_prodMkRight_unit** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isSFiniteKernel_prodMkRight_unit {κ : Kernel α β} : IsSFiniteKernel (prodM
kRight Unit κ) ↔ IsSFiniteKernel κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkRight`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mγ : MeasurableSpace γ} (κ : Probability…
-/
lemma isSFiniteKernel_prodMkRight_unit {κ : Kernel α β} :
    IsSFiniteKernel (prodMkRight Unit κ) ↔ IsSFiniteKernel κ := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  change IsSFiniteKernel ((prodMkRight Unit κ).comap (fun a ↦ (a, ())) (by fun_prop))
  infer_instance
/-
**ProbabilityTheory.Kernel.map_prodMkLeft** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：map_prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) (f : β -> 
δ) : map (prodMkLeft γ κ) f = prodMkLeft γ (map κ f)
参数：γ : Type*；κ : Kernel α β；f : β -> δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.map_of_not_measurable`：map_of_not_measurable (κ
 : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f)) : map κ f = 0
· 使用引理 `ProbabilityTheory.Kernel.prodMkLeft_zero`：prodMkLeft_zero : Kernel.prodM
kLeft α (0 : Kernel β γ) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) (f : β → δ) :
    map (prodMkLeft γ κ) f = prodMkLeft γ (map κ f) := by
  by_cases hf : Measurable f
  · simp only [map, hf, ↓reduceDIte]
    rfl
  · simp [map_of_not_measurable _ hf]
/-
**ProbabilityTheory.Kernel.map_prodMkRight** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：map_prodMkRight (κ : Kernel α β) (γ : Type*) {mγ : MeasurableSpace γ} (f :
 β -> δ) : map (prodMkRight γ κ) f = prodMkRight γ (map κ f)
参数：κ : Kernel α β；γ : Type*；f : β -> δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.map_of_not_measurable`：map_of_not_measurable (κ
 : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f)) : map κ f = 0
· 使用引理 `ProbabilityTheory.Kernel.prodMkRight_zero`：prodMkRight_zero : Kernel.pro
dMkRight α (0 : Kernel β γ) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_prodMkRight (κ : Kernel α β) (γ : Type*) {mγ : MeasurableSpace γ} (f : β → δ) :
    map (prodMkRight γ κ) f = prodMkRight γ (map κ f) := by
  by_cases hf : Measurable f
  · simp only [map, hf, ↓reduceDIte]
    rfl
  · simp [map_of_not_measurable _ hf]

/-- Define a `Kernel (β × α) γ` from a `Kernel (α × β) γ` by taking the comap of `Prod.swap`. -/
/-
**ProbabilityTheory.Kernel.swapLeft** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：swapLeft (κ : Kernel (α × β) γ) : Kernel (β × α) γ
参数：κ : Kernel (α × β) γ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)

--- 原说明 ---
Define a `Kernel (β × α) γ` from a `Kernel (α × β) γ` by taking the comap of `Pr
od.swap`.
-/
def swapLeft (κ : Kernel (α × β) γ) : Kernel (β × α) γ :=
  comap κ Prod.swap measurable_swap

@[simp]
/-
**ProbabilityTheory.Kernel.swapLeft_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：swapLeft_zero : swapLeft (0 : Kernel (α × β) γ) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.comap_zero`：comap_zero (hg : Measurable g) : Ke
rnel.comap (0 : Kernel α β) g hg = 0
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma swapLeft_zero : swapLeft (0 : Kernel (α × β) γ) = 0 := by simp [swapLeft]

@[simp]
/-
**ProbabilityTheory.Kernel.swapLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：swapLeft_apply (κ : Kernel (α × β) γ) (a : β × α) : swapLeft κ a = κ a.swa
p
参数：κ : Kernel (α × β) γ；a : β × α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swapLeft_apply (κ : Kernel (α × β) γ) (a : β × α) : swapLeft κ a = κ a.swap := rfl
/-
**ProbabilityTheory.Kernel.swapLeft_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：swapLeft_apply' (κ : Kernel (α × β) γ) (a : β × α) (s : Set γ) : swapLeft 
κ a s = κ a.swap s
参数：κ : Kernel (α × β) γ；a : β × α；s : Set γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swapLeft_apply' (κ : Kernel (α × β) γ) (a : β × α) (s : Set γ) :
    swapLeft κ a s = κ a.swap s := rfl
/-
**ProbabilityTheory.Kernel.lintegral_swapLeft** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：lintegral_swapLeft (κ : Kernel (α × β) γ) (a : β × α) (g : γ -> Real>=0∞) 
: ∫⁻ c, g c ∂swapLeft κ a = ∫⁻ c, g c ∂κ a.swap
参数：κ : Kernel (α × β) γ；a : β × α；g : γ -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.swapLeft_apply`：swapLeft_apply (κ : Kernel (α ×
 β) γ) (a : β × α) : swapLeft κ a = κ a.swap
-/
theorem lintegral_swapLeft (κ : Kernel (α × β) γ) (a : β × α) (g : γ → ℝ≥0∞) :
    ∫⁻ c, g c ∂swapLeft κ a = ∫⁻ c, g c ∂κ a.swap := by
  rw [swapLeft_apply]
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.swapLeft** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
(α × β) γ) [ProbabilityTheory.IsMarkovKernel κ],   ProbabilityTheory.IsMarkovKer
nel κ.swapLeft
参数：κ : ProbabilityTheory.Kernel (α × β) γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.swapLeft.eq_1`：∀ {α : Type u_1} {β : Type u_2} 
{γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measura
bleSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.comap`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsMarkovKernel.swapLeft (κ : Kernel (α × β) γ) [IsMarkovKernel κ] :
    IsMarkovKernel (swapLeft κ) := by rw [Kernel.swapLeft]; infer_instance
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.swapLeft** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
(α × β) γ) [ProbabilityTheory.IsFiniteKernel κ],   ProbabilityTheory.IsFiniteKer
nel κ.swapLeft
参数：κ : ProbabilityTheory.Kernel (α × β) γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.swapLeft.eq_1`：∀ {α : Type u_1} {β : Type u_2} 
{γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measura
bleSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comap`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsFiniteKernel.swapLeft (κ : Kernel (α × β) γ) [IsFiniteKernel κ] :
    IsFiniteKernel (swapLeft κ) := by rw [Kernel.swapLeft]; infer_instance
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.swapLeft** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
(α × β) γ) [ProbabilityTheory.IsSFiniteKernel κ],   ProbabilityTheory.IsSFiniteK
ernel κ.swapLeft
参数：κ : ProbabilityTheory.Kernel (α × β) γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.swapLeft.eq_1`：∀ {α : Type u_1} {β : Type u_2} 
{γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measura
bleSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
-/
instance IsSFiniteKernel.swapLeft (κ : Kernel (α × β) γ) [IsSFiniteKernel κ] :
    IsSFiniteKernel (swapLeft κ) := by rw [Kernel.swapLeft]; infer_instance
/-
**ProbabilityTheory.Kernel.swapLeft_prodMkLeft** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (κ : ProbabilityTheory.Kernel α β)   (γ : Type u_5) {x : MeasurableSpace
 γ},   (ProbabilityTheory.Kernel.prodMkLeft γ κ).swapLeft = ProbabilityTheory.Ke
rnel.prodMkRight γ κ
参数：κ : ProbabilityTheory.Kernel α β；γ : Type u_5；ProbabilityTheory.Kernel.prodMk
Left γ κ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma swapLeft_prodMkLeft (κ : Kernel α β) (γ : Type*) {_ : MeasurableSpace γ} :
    swapLeft (prodMkLeft γ κ) = prodMkRight γ κ := rfl
/-
**ProbabilityTheory.Kernel.swapLeft_prodMkRight** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (κ : ProbabilityTheory.Kernel α β)   (γ : Type u_5) {x : MeasurableSpace
 γ},   (ProbabilityTheory.Kernel.prodMkRight γ κ).swapLeft = ProbabilityTheory.K
ernel.prodMkLeft γ κ
参数：κ : ProbabilityTheory.Kernel α β；γ : Type u_5；ProbabilityTheory.Kernel.prodMk
Right γ κ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma swapLeft_prodMkRight (κ : Kernel α β) (γ : Type*) {_ : MeasurableSpace γ} :
    swapLeft (prodMkRight γ κ) = prodMkLeft γ κ := rfl

/-- Define a `Kernel α (γ × β)` from a `Kernel α (β × γ)` by taking the map of `Prod.swap`.
We use `mapOfMeasurable` in the definition for better defeqs. -/
/-
**ProbabilityTheory.Kernel.swapRight** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：swapRight (κ : Kernel α (β × γ)) : Kernel α (γ × β)
参数：κ : Kernel α (β × γ)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)

--- 原说明 ---
Define a `Kernel α (γ × β)` from a `Kernel α (β × γ)` by taking the map of `Prod
.swap`.
We use `mapOfMeasurable` in the definition for better defeqs.
-/
noncomputable def swapRight (κ : Kernel α (β × γ)) : Kernel α (γ × β) :=
  mapOfMeasurable κ Prod.swap measurable_swap
/-
**ProbabilityTheory.Kernel.swapRight_eq** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：swapRight_eq (κ : Kernel α (β × γ)) : swapRight κ = map κ Prod.swap
参数：κ : Kernel α (β × γ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.mapOfMeasurable_eq_map`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ 
: MeasurableSpace γ} (κ : Probability…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma swapRight_eq (κ : Kernel α (β × γ)) : swapRight κ = map κ Prod.swap := by
  simp [swapRight]

@[simp]
/-
**ProbabilityTheory.Kernel.swapRight_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：swapRight_zero : swapRight (0 : Kernel α (β × γ)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `ProbabilityTheory.Kernel.mapOfMeasurable_eq_map`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ 
: MeasurableSpace γ} (κ : Probability…
· 使用引理 `ProbabilityTheory.Kernel.map_zero`：map_zero : Kernel.map (0 : Kernel α β
) f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma swapRight_zero : swapRight (0 : Kernel α (β × γ)) = 0 := by simp [swapRight]
/-
**ProbabilityTheory.Kernel.swapRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：swapRight_apply (κ : Kernel α (β × γ)) (a : α) : swapRight κ a = (κ a).map
 Prod.swap
参数：κ : Kernel α (β × γ)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swapRight_apply (κ : Kernel α (β × γ)) (a : α) : swapRight κ a = (κ a).map Prod.swap :=
  rfl
/-
**ProbabilityTheory.Kernel.swapRight_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：swapRight_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set (γ × β)} (hs : Me
asurableSet s) : swapRight κ a s = κ a {p | p.swap in s}
参数：κ : Kernel α (β × γ)；a : α；γ × β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.swapRight_apply`：swapRight_apply (κ : Kernel α 
(β × γ)) (a : α) : swapRight κ a = (κ a).map Prod.swap
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
theorem swapRight_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set (γ × β)} (hs : MeasurableSet s) :
    swapRight κ a s = κ a {p | p.swap ∈ s} := by
  rw [swapRight_apply, Measure.map_apply measurable_swap hs]; rfl
/-
**ProbabilityTheory.Kernel.lintegral_swapRight** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：lintegral_swapRight (κ : Kernel α (β × γ)) (a : α) {g : γ × β -> Real>=0∞}
 (hg : Measurable g) : ∫⁻ c, g c ∂swapRight κ a = ∫⁻ bc : β × γ, g bc.swap ∂κ a
参数：κ : Kernel α (β × γ)；a : α；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.swapRight_eq`：swapRight_eq (κ : Kernel α (β × γ
)) : swapRight κ = map κ Prod.swap
· 使用定理 `ProbabilityTheory.Kernel.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} 
{mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Measura
bleSpace γ} {f : β → γ} (κ :…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
theorem lintegral_swapRight (κ : Kernel α (β × γ)) (a : α) {g : γ × β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂swapRight κ a = ∫⁻ bc : β × γ, g bc.swap ∂κ a := by
  rw [swapRight_eq, lintegral_map _ measurable_swap a hg]
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.swapRight** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsMarkovKernel κ],   ProbabilityTheory.IsMarkovKer
nel κ.swapRight
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.swapRight_eq`：swapRight_eq (κ : Kernel α (β × γ
)) : swapRight κ = map κ Prod.swap
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} {f : β → γ} (κ :…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
instance IsMarkovKernel.swapRight (κ : Kernel α (β × γ)) [IsMarkovKernel κ] :
    IsMarkovKernel (swapRight κ) := by
  rw [Kernel.swapRight_eq]; exact IsMarkovKernel.map _ measurable_swap
/-
**ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.swapRight** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsZeroOrMarkovKernel κ],   ProbabilityTheory.IsZer
oOrMarkovKernel κ.swapRight
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.swapRight_eq`：swapRight_eq (κ : Kernel α (β × γ
)) : swapRight κ = map κ Prod.swap
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.map`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {m
γ : MeasurableSpace γ} (κ : Probability…
-/
instance IsZeroOrMarkovKernel.swapRight (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (swapRight κ) := by rw [Kernel.swapRight_eq]; infer_instance
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.swapRight** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsFiniteKernel κ],   ProbabilityTheory.IsFiniteKer
nel κ.swapRight
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.swapRight_eq`：swapRight_eq (κ : Kernel α (β × γ
)) : swapRight κ = map κ Prod.swap
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} (κ : Probability…
-/
instance IsFiniteKernel.swapRight (κ : Kernel α (β × γ)) [IsFiniteKernel κ] :
    IsFiniteKernel (swapRight κ) := by rw [Kernel.swapRight_eq]; infer_instance
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.swapRight** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsSFiniteKernel κ],   ProbabilityTheory.IsSFiniteK
ernel κ.swapRight
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.swapRight_eq`：swapRight_eq (κ : Kernel α (β × γ
)) : swapRight κ = map κ Prod.swap
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
-/
instance IsSFiniteKernel.swapRight (κ : Kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (swapRight κ) := by rw [Kernel.swapRight_eq]; infer_instance

/-- Define a `Kernel α β` from a `Kernel α (β × γ)` by taking the map of the first projection.
We use `mapOfMeasurable` for better defeqs. -/
/-
**ProbabilityTheory.Kernel.fst** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Kern
el`。
形式化陈述：fst (κ : Kernel α (β × γ)) : Kernel α β
参数：κ : Kernel α (β × γ)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)

--- 原说明 ---
Define a `Kernel α β` from a `Kernel α (β × γ)` by taking the map of the first p
rojection.
We use `mapOfMeasurable` for better defeqs.
-/
noncomputable def fst (κ : Kernel α (β × γ)) : Kernel α β :=
  mapOfMeasurable κ Prod.fst measurable_fst
/-
**ProbabilityTheory.Kernel.fst_eq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.K
ernel`。
形式化陈述：fst_eq (κ : Kernel α (β × γ)) : fst κ = map κ Prod.fst
参数：κ : Kernel α (β × γ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.mapOfMeasurable_eq_map`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ 
: MeasurableSpace γ} (κ : Probability…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fst_eq (κ : Kernel α (β × γ)) : fst κ = map κ Prod.fst := by simp [fst]
/-
**ProbabilityTheory.Kernel.fst_apply** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：fst_apply (κ : Kernel α (β × γ)) (a : α) : fst κ a = (κ a).map Prod.fst
参数：κ : Kernel α (β × γ)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_apply (κ : Kernel α (β × γ)) (a : α) : fst κ a = (κ a).map Prod.fst :=
  rfl
/-
**ProbabilityTheory.Kernel.fst_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：fst_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet 
s) : fst κ a s = κ a {p | p.1 in s}
参数：κ : Kernel α (β × γ)；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_apply`：fst_apply (κ : Kernel α (β × γ)) (a 
: α) : fst κ a = (κ a).map Prod.fst
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
theorem fst_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s) :
    fst κ a s = κ a {p | p.1 ∈ s} := by rw [fst_apply, Measure.map_apply measurable_fst hs]; rfl
/-
**ProbabilityTheory.Kernel.fst_real_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：fst_real_apply (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : Measurable
Set s) : (fst κ a).real s = (κ a).real {p | p.1 in s}
参数：κ : Kernel α (β × γ)；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_apply'`：fst_apply' (κ : Kernel α (β × γ)) (
a : α) {s : Set β} (hs : MeasurableSet s) : fst κ a s = κ a {p | p.1 in s}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fst_real_apply (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s) :
    (fst κ a).real s = (κ a).real {p | p.1 ∈ s} := by
  simp [fst_apply', hs, measureReal_def]

@[simp]
/-
**ProbabilityTheory.Kernel.fst_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：fst_zero : fst (0 : Kernel α (β × γ)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `ProbabilityTheory.Kernel.mapOfMeasurable_eq_map`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ 
: MeasurableSpace γ} (κ : Probability…
· 使用引理 `ProbabilityTheory.Kernel.map_zero`：map_zero : Kernel.map (0 : Kernel α β
) f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fst_zero : fst (0 : Kernel α (β × γ)) = 0 := by simp [fst]
/-
**ProbabilityTheory.Kernel.lintegral_fst** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：lintegral_fst (κ : Kernel α (β × γ)) (a : α) {g : β -> Real>=0∞} (hg : Mea
surable g) : ∫⁻ c, g c ∂fst κ a = ∫⁻ bc : β × γ, g bc.fst ∂κ a
参数：κ : Kernel α (β × γ)；a : α；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_eq`：fst_eq (κ : Kernel α (β × γ)) : fst κ =
 map κ Prod.fst
· 使用定理 `ProbabilityTheory.Kernel.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} 
{mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Measura
bleSpace γ} {f : β → γ} (κ :…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
theorem lintegral_fst (κ : Kernel α (β × γ)) (a : α) {g : β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂fst κ a = ∫⁻ bc : β × γ, g bc.fst ∂κ a := by
  rw [fst_eq, lintegral_map _ measurable_fst a hg]
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.fst** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsMarkovKernel κ],   ProbabilityTheory.IsMarkovKer
nel κ.fst
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_eq`：fst_eq (κ : Kernel α (β × γ)) : fst κ =
 map κ Prod.fst
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} {f : β → γ} (κ :…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
instance IsMarkovKernel.fst (κ : Kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (fst κ) := by
  rw [Kernel.fst_eq]; exact IsMarkovKernel.map _ measurable_fst
/-
**ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.fst** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.IsZeroOrMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsZeroOrMarkovKernel κ],   ProbabilityTheory.IsZer
oOrMarkovKernel κ.fst
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_eq`：fst_eq (κ : Kernel α (β × γ)) : fst κ =
 map κ Prod.fst
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.map`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {m
γ : MeasurableSpace γ} (κ : Probability…
-/
instance IsZeroOrMarkovKernel.fst (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (fst κ) := by
  rw [Kernel.fst_eq]; infer_instance
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.fst** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsFiniteKernel κ],   ProbabilityTheory.IsFiniteKer
nel κ.fst
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_eq`：fst_eq (κ : Kernel α (β × γ)) : fst κ =
 map κ Prod.fst
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} (κ : Probability…
-/
instance IsFiniteKernel.fst (κ : Kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (fst κ) := by
  rw [Kernel.fst_eq]; infer_instance
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.fst** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsSFiniteKernel κ],   ProbabilityTheory.IsSFiniteK
ernel κ.fst
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_eq`：fst_eq (κ : Kernel α (β × γ)) : fst κ =
 map κ Prod.fst
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
-/
instance IsSFiniteKernel.fst (κ : Kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (fst κ) := by rw [Kernel.fst_eq]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isFiniteKernel_of_isFiniteKernel_fst {κ : Kernel α (β × γ)}
    [h : IsFiniteKernel (fst κ)] :
    IsFiniteKernel κ := by
  refine ⟨(fst κ).bound, (fst κ).bound_lt_top,
    fun a ↦ le_trans ?_ (measure_le_bound (fst κ) a Set.univ)⟩
  rw [fst_apply' _ _ MeasurableSet.univ]
  simp
/-
**ProbabilityTheory.Kernel.fst_map_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：fst_map_prod (κ : Kernel α β) {f : β -> γ} {g : β -> δ} (hg : Measurable g
) : fst (map κ (fun x => (f x, g x))) = map κ f
参数：κ : Kernel α β；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_apply'`：fst_apply' (κ : Kernel α (β × γ)) (
a : α) {s : Set β} (hs : MeasurableSet s) : fst κ a s = κ a {p | p.1 in s}
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `Measurable.prod`：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun 
a => (f a).1) (hf₂ : Measurable fun a => (f a).2) : Measurable f
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.map_of_not_measurable`：map_of_not_measurable (κ
 : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f)) : map κ f = 0
· 使用引理 `ProbabilityTheory.Kernel.fst_zero`：fst_zero : fst (0 : Kernel α (β × γ))
 = 0
-/
lemma fst_map_prod (κ : Kernel α β) {f : β → γ} {g : β → δ} (hg : Measurable g) :
    fst (map κ (fun x ↦ (f x, g x))) = map κ f := by
  by_cases hf : Measurable f
  · ext x s hs
    rw [fst_apply' _ _ hs, map_apply' _ (hf.prod hg) _, map_apply' _ hf _ hs]
    · simp only [Set.preimage, Set.mem_ofPred]
    · exact measurable_fst hs
  · have : ¬ Measurable (fun x ↦ (f x, g x)) := by
      contrapose hf; exact hf.fst
    simp [map_of_not_measurable _ hf, map_of_not_measurable _ this]
/-
**ProbabilityTheory.Kernel.fst_map_id_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：fst_map_id_prod (κ : Kernel α β) {f : β -> γ} (hf : Measurable f) : fst (m
ap κ (fun a => (a, f a))) = κ
参数：κ : Kernel α β；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.fst_map_prod`：fst_map_prod (κ : Kernel α β) {f 
: β -> γ} {g : β -> δ} (hg : Measurable g) : fst (map κ (fun x => (f x, g x))) =
 map κ f
· 使用引理 `ProbabilityTheory.Kernel.map_id'`：map_id' (κ : Kernel α β) : map κ (fun 
a => a) = κ
-/
lemma fst_map_id_prod (κ : Kernel α β) {f : β → γ} (hf : Measurable f) :
    fst (map κ (fun a ↦ (a, f a))) = κ := by
  rw [fst_map_prod _ hf, Kernel.map_id']
/-
**ProbabilityTheory.Kernel.fst_prodMkLeft** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：fst_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : Kernel α (β × γ)) : fs
t (prodMkLeft δ κ) = prodMkLeft δ (fst κ)
参数：δ : Type*；κ : Kernel α (β × γ)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : Kernel α (β × γ)) :
    fst (prodMkLeft δ κ) = prodMkLeft δ (fst κ) := rfl
/-
**ProbabilityTheory.Kernel.fst_prodMkRight** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：fst_prodMkRight (κ : Kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] : f
st (prodMkRight δ κ) = prodMkRight δ (fst κ)
参数：κ : Kernel α (β × γ)；δ : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_prodMkRight (κ : Kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    fst (prodMkRight δ κ) = prodMkRight δ (fst κ) := rfl

/-- Define a `Kernel α γ` from a `Kernel α (β × γ)` by taking the map of the second projection.
We use `mapOfMeasurable` for better defeqs. -/
/-
**ProbabilityTheory.Kernel.snd** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Kern
el`。
形式化陈述：snd (κ : Kernel α (β × γ)) : Kernel α γ
参数：κ : Kernel α (β × γ)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)

--- 原说明 ---
Define a `Kernel α γ` from a `Kernel α (β × γ)` by taking the map of the second 
projection.
We use `mapOfMeasurable` for better defeqs.
-/
noncomputable def snd (κ : Kernel α (β × γ)) : Kernel α γ :=
  mapOfMeasurable κ Prod.snd measurable_snd
/-
**ProbabilityTheory.Kernel.snd_eq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.K
ernel`。
形式化陈述：snd_eq (κ : Kernel α (β × γ)) : snd κ = map κ Prod.snd
参数：κ : Kernel α (β × γ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.mapOfMeasurable_eq_map`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ 
: MeasurableSpace γ} (κ : Probability…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem snd_eq (κ : Kernel α (β × γ)) : snd κ = map κ Prod.snd := by simp [snd]
/-
**ProbabilityTheory.Kernel.snd_apply** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：snd_apply (κ : Kernel α (β × γ)) (a : α) : snd κ a = (κ a).map Prod.snd
参数：κ : Kernel α (β × γ)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_apply (κ : Kernel α (β × γ)) (a : α) : snd κ a = (κ a).map Prod.snd :=
  rfl
/-
**ProbabilityTheory.Kernel.snd_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：snd_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set γ} (hs : MeasurableSet 
s) : snd κ a s = κ a (Prod.snd ⁻¹' s)
参数：κ : Kernel α (β × γ)；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.snd_apply`：snd_apply (κ : Kernel α (β × γ)) (a 
: α) : snd κ a = (κ a).map Prod.snd
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem snd_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    snd κ a s = κ a (Prod.snd ⁻¹' s) := by rw [snd_apply, Measure.map_apply measurable_snd hs]

@[simp]
/-
**ProbabilityTheory.Kernel.snd_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：snd_zero : snd (0 : Kernel α (β × γ)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `ProbabilityTheory.Kernel.mapOfMeasurable_eq_map`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ 
: MeasurableSpace γ} (κ : Probability…
· 使用引理 `ProbabilityTheory.Kernel.map_zero`：map_zero : Kernel.map (0 : Kernel α β
) f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma snd_zero : snd (0 : Kernel α (β × γ)) = 0 := by simp [snd]
/-
**ProbabilityTheory.Kernel.lintegral_snd** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：lintegral_snd (κ : Kernel α (β × γ)) (a : α) {g : γ -> Real>=0∞} (hg : Mea
surable g) : ∫⁻ c, g c ∂snd κ a = ∫⁻ bc : β × γ, g bc.snd ∂κ a
参数：κ : Kernel α (β × γ)；a : α；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.snd_eq`：snd_eq (κ : Kernel α (β × γ)) : snd κ =
 map κ Prod.snd
· 使用定理 `ProbabilityTheory.Kernel.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} 
{mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Measura
bleSpace γ} {f : β → γ} (κ :…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem lintegral_snd (κ : Kernel α (β × γ)) (a : α) {g : γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂snd κ a = ∫⁻ bc : β × γ, g bc.snd ∂κ a := by
  rw [snd_eq, lintegral_map _ measurable_snd a hg]
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.snd** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsMarkovKernel κ],   ProbabilityTheory.IsMarkovKer
nel κ.snd
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.snd_eq`：snd_eq (κ : Kernel α (β × γ)) : snd κ =
 map κ Prod.snd
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} {f : β → γ} (κ :…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
instance IsMarkovKernel.snd (κ : Kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (snd κ) := by
  rw [Kernel.snd_eq]; exact IsMarkovKernel.map _ measurable_snd
/-
**ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.snd** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.IsZeroOrMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsZeroOrMarkovKernel κ],   ProbabilityTheory.IsZer
oOrMarkovKernel κ.snd
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.snd_eq`：snd_eq (κ : Kernel α (β × γ)) : snd κ =
 map κ Prod.snd
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.map`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {m
γ : MeasurableSpace γ} (κ : Probability…
-/
instance IsZeroOrMarkovKernel.snd (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (snd κ) := by
  rw [Kernel.snd_eq]; infer_instance
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.snd** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsFiniteKernel κ],   ProbabilityTheory.IsFiniteKer
nel κ.snd
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.snd_eq`：snd_eq (κ : Kernel α (β × γ)) : snd κ =
 map κ Prod.snd
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} (κ : Probability…
-/
instance IsFiniteKernel.snd (κ : Kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (snd κ) := by
  rw [Kernel.snd_eq]; infer_instance
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.snd** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α (β × γ)) [ProbabilityTheory.IsSFiniteKernel κ],   ProbabilityTheory.IsSFiniteK
ernel κ.snd
参数：κ : ProbabilityTheory.Kernel α (β × γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.snd_eq`：snd_eq (κ : Kernel α (β × γ)) : snd κ =
 map κ Prod.snd
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
-/
instance IsSFiniteKernel.snd (κ : Kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (snd κ) := by rw [Kernel.snd_eq]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isFiniteKernel_of_isFiniteKernel_snd {κ : Kernel α (β × γ)}
    [h : IsFiniteKernel (snd κ)] :
    IsFiniteKernel κ := by
  refine ⟨(snd κ).bound, (snd κ).bound_lt_top,
    fun a ↦ le_trans ?_ (measure_le_bound (snd κ) a Set.univ)⟩
  rw [snd_apply' _ _ MeasurableSet.univ]
  simp
/-
**ProbabilityTheory.Kernel.snd_map_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：snd_map_prod (κ : Kernel α β) {f : β -> γ} {g : β -> δ} (hf : Measurable f
) : snd (map κ (fun x => (f x, g x))) = map κ g
参数：κ : Kernel α β；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.snd_apply'`：snd_apply' (κ : Kernel α (β × γ)) (
a : α) {s : Set γ} (hs : MeasurableSet s) : snd κ a s = κ a (Prod.snd ⁻¹' s)
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `Measurable.prod`：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun 
a => (f a).1) (hf₂ : Measurable fun a => (f a).2) : Measurable f
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.map_of_not_measurable`：map_of_not_measurable (κ
 : Kernel α β) {f : β -> γ} (hf : ¬(Measurable f)) : map κ f = 0
· 使用引理 `ProbabilityTheory.Kernel.snd_zero`：snd_zero : snd (0 : Kernel α (β × γ))
 = 0
-/
lemma snd_map_prod (κ : Kernel α β) {f : β → γ} {g : β → δ} (hf : Measurable f) :
    snd (map κ (fun x ↦ (f x, g x))) = map κ g := by
  by_cases hg : Measurable g
  · ext x s hs
    rw [snd_apply' _ _ hs, map_apply' _ (hf.prod hg), map_apply' _ hg _ hs]
    · simp only [Set.preimage, Set.mem_ofPred]
    · exact measurable_snd hs
  · have : ¬ Measurable (fun x ↦ (f x, g x)) := by
      contrapose hg; exact hg.snd
    simp [map_of_not_measurable _ hg, map_of_not_measurable _ this]
/-
**ProbabilityTheory.Kernel.snd_map_prod_id** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：snd_map_prod_id (κ : Kernel α β) {f : β -> γ} (hf : Measurable f) : snd (m
ap κ (fun a => (f a, a))) = κ
参数：κ : Kernel α β；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.snd_map_prod`：snd_map_prod (κ : Kernel α β) {f 
: β -> γ} {g : β -> δ} (hf : Measurable f) : snd (map κ (fun x => (f x, g x))) =
 map κ g
· 使用引理 `ProbabilityTheory.Kernel.map_id'`：map_id' (κ : Kernel α β) : map κ (fun 
a => a) = κ
-/
lemma snd_map_prod_id (κ : Kernel α β) {f : β → γ} (hf : Measurable f) :
    snd (map κ (fun a ↦ (f a, a))) = κ := by
  rw [snd_map_prod _ hf, Kernel.map_id']
/-
**ProbabilityTheory.Kernel.snd_prodMkLeft** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：snd_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : Kernel α (β × γ)) : sn
d (prodMkLeft δ κ) = prodMkLeft δ (snd κ)
参数：δ : Type*；κ : Kernel α (β × γ)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : Kernel α (β × γ)) :
    snd (prodMkLeft δ κ) = prodMkLeft δ (snd κ) := rfl
/-
**ProbabilityTheory.Kernel.snd_prodMkRight** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：snd_prodMkRight (κ : Kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] : s
nd (prodMkRight δ κ) = prodMkRight δ (snd κ)
参数：κ : Kernel α (β × γ)；δ : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd_prodMkRight (κ : Kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    snd (prodMkRight δ κ) = prodMkRight δ (snd κ) := rfl

@[simp]
/-
**ProbabilityTheory.Kernel.fst_swapRight** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：fst_swapRight (κ : Kernel α (β × γ)) : fst (swapRight κ) = snd κ
参数：κ : Kernel α (β × γ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_apply'`：fst_apply' (κ : Kernel α (β × γ)) (
a : α) {s : Set β} (hs : MeasurableSet s) : fst κ a s = κ a {p | p.1 in s}
· 使用定理 `ProbabilityTheory.Kernel.swapRight_apply'`：swapRight_apply' (κ : Kernel 
α (β × γ)) (a : α) {s : Set (γ × β)} (hs : MeasurableSet s) : swapRight κ a s = 
κ a {p | p.swap in s}
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `ProbabilityTheory.Kernel.snd_apply'`：snd_apply' (κ : Kernel α (β × γ)) (
a : α) {s : Set γ} (hs : MeasurableSet s) : snd κ a s = κ a (Prod.snd ⁻¹' s)
-/
lemma fst_swapRight (κ : Kernel α (β × γ)) : fst (swapRight κ) = snd κ := by
  ext a s hs
  rw [fst_apply' _ _ hs, swapRight_apply', snd_apply' _ _ hs]
  · rfl
  · exact measurable_fst hs

@[simp]
/-
**ProbabilityTheory.Kernel.snd_swapRight** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：snd_swapRight (κ : Kernel α (β × γ)) : snd (swapRight κ) = fst κ
参数：κ : Kernel α (β × γ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.snd_apply'`：snd_apply' (κ : Kernel α (β × γ)) (
a : α) {s : Set γ} (hs : MeasurableSet s) : snd κ a s = κ a (Prod.snd ⁻¹' s)
· 使用定理 `ProbabilityTheory.Kernel.swapRight_apply'`：swapRight_apply' (κ : Kernel 
α (β × γ)) (a : α) {s : Set (γ × β)} (hs : MeasurableSet s) : swapRight κ a s = 
κ a {p | p.swap in s}
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `ProbabilityTheory.Kernel.fst_apply'`：fst_apply' (κ : Kernel α (β × γ)) (
a : α) {s : Set β} (hs : MeasurableSet s) : fst κ a s = κ a {p | p.1 in s}
-/
lemma snd_swapRight (κ : Kernel α (β × γ)) : snd (swapRight κ) = fst κ := by
  ext a s hs
  rw [snd_apply' _ _ hs, swapRight_apply', fst_apply' _ _ hs]
  · rfl
  · exact measurable_snd hs

end FstSnd

section sectLsectR

variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/-- Define a `Kernel α γ` from a `Kernel (α × β) γ` by taking the comap of `fun a ↦ (a, b)` for
a given `b : β`. -/
/-
**ProbabilityTheory.Kernel.sectL** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ke
rnel`。
形式化陈述：sectL (κ : Kernel (α × β) γ) (b : β) : Kernel α γ
参数：κ : Kernel (α × β) γ；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a `Kernel α γ` from a `Kernel (α × β) γ` by taking the comap of `fun a ↦ 
(a, b)` for
a given `b : β`.
-/
noncomputable def sectL (κ : Kernel (α × β) γ) (b : β) : Kernel α γ :=
  comap κ (fun a ↦ (a, b)) (measurable_id.prodMk measurable_const)
/-
**ProbabilityTheory.Kernel.sectL_apply** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
(α × β) γ) (b : β) (a : α), (κ.sectL b) a = κ (a, b)
参数：κ : ProbabilityTheory.Kernel (α × β) γ；b : β；a : α；κ.sectL b；a, b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sectL_apply (κ : Kernel (α × β) γ) (b : β) (a : α) : sectL κ b a = κ (a, b) := rfl
/-
**ProbabilityTheory.Kernel.sectL_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (b : β), ProbabilityTheory.Ker
nel.sectL 0 b = 0
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.comap_zero`：comap_zero (hg : Measurable g) : Ke
rnel.comap (0 : Kernel α β) g hg = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma sectL_zero (b : β) : sectL (0 : Kernel (α × β) γ) b = 0 := by simp [sectL]
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel (α × β) γ) (b : β) [IsMarkovKernel κ] : IsMarkovKernel (sectL κ b) := by
  rw [sectL]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel (α × β) γ) (b : β) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (sectL κ b) := by
  rw [sectL]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel (α × β) γ) (b : β) [IsFiniteKernel κ] : IsFiniteKernel (sectL κ b) := by
  rw [sectL]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel (α × β) γ) (b : β) [IsSFiniteKernel κ] : IsSFiniteKernel (sectL κ b) := by
  rw [sectL]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel (α × β) γ) (a : α) (b : β) [NeZero (κ (a, b))] : NeZero ((sectL κ b) a) := by
  rw [sectL_apply]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {κ : Kernel (α × β) γ} [∀ b, IsMarkovKernel (sectL κ b)] :
    IsMarkovKernel κ := by
  refine ⟨fun _ ↦ ⟨?_⟩⟩
  rw [← sectL_apply, measure_univ]

--I'm not sure this lemma is actually useful
/-
**ProbabilityTheory.Kernel.comap_sectL** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：comap_sectL (κ : Kernel (α × β) γ) (b : β) {f : δ -> α} (hf : Measurable f
) : comap (sectL κ b) f hf = comap κ (fun d => (f d, b)) (hf.prodMk measurable_c
onst)
参数：κ : Kernel (α × β) γ；b : β；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comap_apply`：comap_apply (κ : Kernel α β) (hg :
 Measurable g) (c : γ) : comap κ g hg c = κ (g c)
· 使用定理 `ProbabilityTheory.Kernel.sectL_apply`：∀ {α : Type u_1} {β : Type u_2} {m
α : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Measurabl
eSpace γ} (κ : Probability…
-/
lemma comap_sectL (κ : Kernel (α × β) γ) (b : β) {f : δ → α} (hf : Measurable f) :
    comap (sectL κ b) f hf = comap κ (fun d ↦ (f d, b)) (hf.prodMk measurable_const) := by
  ext d s
  rw [comap_apply, sectL_apply, comap_apply]

@[simp]
/-
**ProbabilityTheory.Kernel.sectL_prodMkLeft** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：sectL_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) 
{b : β} : sectL (prodMkLeft α κ) b a = κ b
参数：α : Type*；κ : Kernel β γ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sectL_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) {b : β} :
    sectL (prodMkLeft α κ) b a = κ b := rfl

@[simp]
/-
**ProbabilityTheory.Kernel.sectL_prodMkRight** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：sectL_prodMkRight (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β)
 : sectL (prodMkRight β κ) b = κ
参数：β : Type*；κ : Kernel α γ；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sectL_prodMkRight (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β) :
    sectL (prodMkRight β κ) b = κ := rfl

/-- Define a `Kernel β γ` from a `Kernel (α × β) γ` by taking the comap of `fun b ↦ (a, b)` for
a given `a : α`. -/
/-
**ProbabilityTheory.Kernel.sectR** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ke
rnel`。
形式化陈述：sectR (κ : Kernel (α × β) γ) (a : α) : Kernel β γ
参数：κ : Kernel (α × β) γ；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a `Kernel β γ` from a `Kernel (α × β) γ` by taking the comap of `fun b ↦ 
(a, b)` for
a given `a : α`.
-/
noncomputable def sectR (κ : Kernel (α × β) γ) (a : α) : Kernel β γ :=
  comap κ (fun b ↦ (a, b)) (measurable_const.prodMk measurable_id)
/-
**ProbabilityTheory.Kernel.sectR_apply** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
(α × β) γ) (b : β) (a : α), (κ.sectR a) b = κ (a, b)
参数：κ : ProbabilityTheory.Kernel (α × β) γ；b : β；a : α；κ.sectR a；a, b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sectR_apply (κ : Kernel (α × β) γ) (b : β) (a : α) : sectR κ a b = κ (a, b) := rfl
/-
**ProbabilityTheory.Kernel.sectR_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (a : α), ProbabilityTheory.Ker
nel.sectR 0 a = 0
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.comap_zero`：comap_zero (hg : Measurable g) : Ke
rnel.comap (0 : Kernel α β) g hg = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma sectR_zero (a : α) : sectR (0 : Kernel (α × β) γ) a = 0 := by simp [sectR]
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel (α × β) γ) (a : α) [IsMarkovKernel κ] : IsMarkovKernel (sectR κ a) := by
  rw [sectR]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel (α × β) γ) (a : α) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (sectR κ a) := by
  rw [sectR]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel (α × β) γ) (a : α) [IsFiniteKernel κ] : IsFiniteKernel (sectR κ a) := by
  rw [sectR]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel (α × β) γ) (a : α) [IsSFiniteKernel κ] : IsSFiniteKernel (sectR κ a) := by
  rw [sectR]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Kernel (α × β) γ) (a : α) (b : β) [NeZero (κ (a, b))] : NeZero ((sectR κ a) b) := by
  rw [sectR_apply]; infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {κ : Kernel (α × β) γ} [∀ b, IsMarkovKernel (sectR κ b)] :
    IsMarkovKernel κ := by
  refine ⟨fun _ ↦ ⟨?_⟩⟩
  rw [← sectR_apply, measure_univ]

--I'm not sure this lemma is actually useful
/-
**ProbabilityTheory.Kernel.comap_sectR** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：comap_sectR (κ : Kernel (α × β) γ) (a : α) {f : δ -> β} (hf : Measurable f
) : comap (sectR κ a) f hf = comap κ (fun d => (a, f d)) (measurable_const.prodM
k hf)
参数：κ : Kernel (α × β) γ；a : α；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comap_apply`：comap_apply (κ : Kernel α β) (hg :
 Measurable g) (c : γ) : comap κ g hg c = κ (g c)
· 使用定理 `ProbabilityTheory.Kernel.sectR_apply`：∀ {α : Type u_1} {β : Type u_2} {m
α : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Measurabl
eSpace γ} (κ : Probability…
-/
lemma comap_sectR (κ : Kernel (α × β) γ) (a : α) {f : δ → β} (hf : Measurable f) :
    comap (sectR κ a) f hf = comap κ (fun d ↦ (a, f d)) (measurable_const.prodMk hf) := by
  ext d s
  rw [comap_apply, sectR_apply, comap_apply]

@[simp]
/-
**ProbabilityTheory.Kernel.sectR_prodMkLeft** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：sectR_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) 
: sectR (prodMkLeft α κ) a = κ
参数：α : Type*；κ : Kernel β γ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sectR_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) :
    sectR (prodMkLeft α κ) a = κ := rfl

@[simp]
/-
**ProbabilityTheory.Kernel.sectR_prodMkRight** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：sectR_prodMkRight (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β)
 {a : α} : sectR (prodMkRight β κ) a b = κ a
参数：β : Type*；κ : Kernel α γ；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sectR_prodMkRight (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β) {a : α} :
    sectR (prodMkRight β κ) a b = κ a := rfl
/-
**ProbabilityTheory.Kernel.sectL_swapRight** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
(α × β) γ), κ.swapLeft.sectL = κ.sectR
参数：κ : ProbabilityTheory.Kernel (α × β) γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sectL_swapRight (κ : Kernel (α × β) γ) : sectL (swapLeft κ) = sectR κ := rfl
/-
**ProbabilityTheory.Kernel.sectR_swapRight** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
(α × β) γ), κ.swapLeft.sectR = κ.sectL
参数：κ : ProbabilityTheory.Kernel (α × β) γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sectR_swapRight (κ : Kernel (α × β) γ) : sectR (swapLeft κ) = sectL κ := rfl

end sectLsectR

/-
**ProbabilityTheory.Kernel.isSFiniteKernel_prodMkLeft_iff** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isSFiniteKernel_prodMkLeft_iff [Nonempty γ] {κ : Kernel α β} : IsSFiniteKe
rnel (prodMkLeft γ κ) ↔ IsSFiniteKernel κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.sectR_prodMkLeft`：sectR_prodMkLeft (α : Type*) 
[MeasurableSpace α] (κ : Kernel β γ) (a : α) : sectR (prodMkLeft α κ) a = κ
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelSectROfProd`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4
}   {mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
-/
lemma isSFiniteKernel_prodMkLeft_iff [Nonempty γ] {κ : Kernel α β} :
    IsSFiniteKernel (prodMkLeft γ κ) ↔ IsSFiniteKernel κ := by
  inhabit γ
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [← sectR_prodMkLeft γ κ default]
  infer_instance
/-
**ProbabilityTheory.Kernel.isSFiniteKernel_prodMkRight_iff** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：isSFiniteKernel_prodMkRight_iff [Nonempty γ] {κ : Kernel α β} : IsSFiniteK
ernel (prodMkRight γ κ) ↔ IsSFiniteKernel κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.sectL_prodMkRight`：sectL_prodMkRight (β : Type*
) [MeasurableSpace β] (κ : Kernel α γ) (b : β) : sectL (prodMkRight β κ) b = κ
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelSectLOfProd`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4
}   {mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkRight`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mγ : MeasurableSpace γ} (κ : Probability…
-/
lemma isSFiniteKernel_prodMkRight_iff [Nonempty γ] {κ : Kernel α β} :
    IsSFiniteKernel (prodMkRight γ κ) ↔ IsSFiniteKernel κ := by
  inhabit γ
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [← sectL_prodMkRight γ κ default]
  infer_instance

end Kernel
end ProbabilityTheory

