/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Defs

/-!
# Basic kernels

This file contains basic results about kernels in general and definitions of some particular
kernels.

## Main definitions

* `ProbabilityTheory.Kernel.deterministic (f : α → β) (hf : Measurable f)`:
  kernel `a ↦ Measure.dirac (f a)`.
* `ProbabilityTheory.Kernel.id`: the identity kernel, deterministic kernel for
  the identity function.
* `ProbabilityTheory.Kernel.copy α`: the deterministic kernel that maps `x : α` to
  the Dirac measure at `(x, x) : α × α`.
* `ProbabilityTheory.Kernel.discard α`: the Markov kernel to the type `PUnit`.
* `ProbabilityTheory.Kernel.swap α β`: the deterministic kernel that maps `(x, y)` to
  the Dirac measure at `(y, x)`.
* `ProbabilityTheory.Kernel.const α (μβ : measure β)`: constant kernel `a ↦ μβ`.
* `ProbabilityTheory.Kernel.restrict κ (hs : MeasurableSet s)`: kernel for which the image of
  `a : α` is `(κ a).restrict s`.
  Integral: `∫⁻ b, f b ∂(κ.restrict hs a) = ∫⁻ b in s, f b ∂(κ a)`
* `ProbabilityTheory.Kernel.comapRight`: Kernel with value `(κ a).comap f`,
  for a measurable embedding `f`. That is, for a measurable set `t : Set β`,
  `ProbabilityTheory.Kernel.comapRight κ hf a t = κ a (f '' t)`
* `ProbabilityTheory.Kernel.piecewise (hs : MeasurableSet s) κ η`: the kernel equal to `κ`
  on the measurable set `s` and to `η` on its complement.

## Main statements

-/

@[expose] public section

assert_not_exists MeasureTheory.integral

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Kernel α β}

namespace Kernel

section Deterministic

/-- Kernel which to `a` associates the dirac measure at `f a`. This is a Markov kernel. -/
/-
**ProbabilityTheory.Kernel.deterministic** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：deterministic (f : α -> β) (hf : Measurable f) : Kernel α β where toFun a
参数：f : α -> β；hf : Measurable f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Kernel which to `a` associates the dirac measure at `f a`. This is a Markov kern
el.
-/
noncomputable def deterministic (f : α → β) (hf : Measurable f) : Kernel α β where
  toFun a := Measure.dirac (f a)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.dirac_apply' _ hs]
    exact measurable_one.indicator (hf hs)
/-
**ProbabilityTheory.Kernel.deterministic_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：deterministic_apply {f : α -> β} (hf : Measurable f) (a : α) : determinist
ic f hf a = Measure.dirac (f a)
参数：hf : Measurable f；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deterministic_apply {f : α → β} (hf : Measurable f) (a : α) :
    deterministic f hf a = Measure.dirac (f a) :=
  rfl
/-
**ProbabilityTheory.Kernel.deterministic_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：deterministic_apply' {f : α -> β} (hf : Measurable f) (a : α) {s : Set β} 
(hs : MeasurableSet s) : deterministic f hf a s = s.indicator (fun _ => 1) (f a)
参数：hf : Measurable f；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic.eq_1`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (f : α → β) (hf : Measura
ble f),   ProbabilityTheory.Kerne…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deterministic_apply' {f : α → β} (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) : deterministic f hf a s = s.indicator (fun _ => 1) (f a) := by
  rw [deterministic]
  change Measure.dirac (f a) s = s.indicator 1 (f a)
  simp_rw [Measure.dirac_apply' _ hs]

/-- Because of the measurability field in `Kernel.deterministic`, `rw [h]` will not rewrite
`deterministic f hf` to `deterministic g ⋯`. Instead one can do `rw [deterministic_congr h]`. -/
/-
**ProbabilityTheory.Kernel.deterministic_congr** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：deterministic_congr {f g : α -> β} {hf : Measurable f} (h : f = g) : deter
ministic f hf = deterministic g (h ▸ hf)
参数：h : f = g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Because of the measurability field in `Kernel.deterministic`, `rw [h]` will not 
rewrite
`deterministic f hf` to `deterministic g ⋯`. Instead one can do `rw [determinist
ic_congr h]`.
-/
theorem deterministic_congr {f g : α → β} {hf : Measurable f} (h : f = g) :
    deterministic f hf = deterministic g (h ▸ hf) := by
  grind
/-
**ProbabilityTheory.Kernel.isMarkovKernel_deterministic** 是 Mathlib 中的一个实例，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：isMarkovKernel_deterministic {f : α -> β} (hf : Measurable f) : IsMarkovKe
rnel (deterministic f hf)
参数：hf : Measurable f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
-/
instance isMarkovKernel_deterministic {f : α → β} (hf : Measurable f) :
    IsMarkovKernel (deterministic f hf) :=
  ⟨fun a => by rw [deterministic_apply hf]; infer_instance⟩
/-
**ProbabilityTheory.Kernel.lintegral_deterministic'** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：lintegral_deterministic' {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Me
asurable g) (hf : Measurable f) : ∫⁻ x, f x ∂deterministic g hg a = f (g a)
参数：hg : Measurable g；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
-/
theorem lintegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    (hf : Measurable f) : ∫⁻ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, lintegral_dirac' _ hf]

@[simp]
/-
**ProbabilityTheory.Kernel.lintegral_deterministic** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：lintegral_deterministic {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Mea
surable g) [MeasurableSingletonClass β] : ∫⁻ x, f x ∂deterministic g hg a = f (g
 a)
参数：hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
-/
theorem lintegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] : ∫⁻ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, lintegral_dirac (g a) f]
/-
**ProbabilityTheory.Kernel.setLIntegral_deterministic'** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：setLIntegral_deterministic' {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg :
 Measurable g) (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) [Decidable
 (g a in s)] : ∫⁻ x in s, f x ∂deterministic g hg a = if g a in s then f (g a) e
lse 0
参数：hg : Measurable g；hf : Measurable f；hs : MeasurableSet s；g a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `MeasureTheory.setLIntegral_dirac'`：setLIntegral_dirac' {a : α} {f : α ->
 Real>=0∞} (hf : Measurable f) {s : Set α} (hs : MeasurableSet s) [Decidable (a 
in s)] : ∫⁻ x in s, f x…
-/
theorem setLIntegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a ∈ s)] :
    ∫⁻ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setLIntegral_dirac' hf hs]

@[simp]
/-
**ProbabilityTheory.Kernel.setLIntegral_deterministic** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：setLIntegral_deterministic {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : 
Measurable g) [MeasurableSingletonClass β] (s : Set β) [Decidable (g a in s)] : 
∫⁻ x in s, f x ∂deterministic g hg a = if g a in s then f (g a) else 0
参数：hg : Measurable g；s : Set β；g a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `MeasureTheory.setLIntegral_dirac`：setLIntegral_dirac {a : α} (f : α -> R
eal>=0∞) (s : Set α) [MeasurableSingletonClass α] [Decidable (a in s)] : ∫⁻ x in
 s, f x ∂Measure.dirac…
-/
theorem setLIntegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] (s : Set β) [Decidable (g a ∈ s)] :
    ∫⁻ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setLIntegral_dirac f s]

end Deterministic

section Id

/-- The identity kernel, that maps `x : α` to the Dirac measure at `x`. -/
protected noncomputable
/-
**ProbabilityTheory.Kernel.id** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Kerne
l`。
形式化陈述：id : Kernel α α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
def id : Kernel α α := Kernel.deterministic id measurable_id
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMarkovKernel (Kernel.id : Kernel α α) := by rw [Kernel.id]; infer_instance
/-
**ProbabilityTheory.Kernel.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：id_apply (a : α) : Kernel.id a = Measure.dirac a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.id.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace
 α}, ProbabilityTheory.Kernel.id = ProbabilityTheory.Kernel.deterministic id ⋯
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `id_def`：∀ {α : Sort u} (a : α), id a = a
-/
lemma id_apply (a : α) : Kernel.id a = Measure.dirac a := by
  rw [Kernel.id, deterministic_apply, id_def]
/-
**ProbabilityTheory.Kernel.lintegral_id'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：lintegral_id' {f : α -> Real>=0∞} (hf : Measurable f) (a : α) : ∫⁻ a, f a 
∂(@Kernel.id α mα a) = f a
参数：hf : Measurable f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
-/
lemma lintegral_id' {f : α → ℝ≥0∞} (hf : Measurable f) (a : α) :
    ∫⁻ a, f a ∂(@Kernel.id α mα a) = f a := by
  rw [id_apply, lintegral_dirac' _ hf]
/-
**ProbabilityTheory.Kernel.lintegral_id** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：lintegral_id [MeasurableSingletonClass α] {f : α -> Real>=0∞} (a : α) : ∫⁻
 a, f a ∂(@Kernel.id α mα a) = f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
-/
lemma lintegral_id [MeasurableSingletonClass α] {f : α → ℝ≥0∞} (a : α) :
    ∫⁻ a, f a ∂(@Kernel.id α mα a) = f a := by
  rw [id_apply, lintegral_dirac]

end Id

section Copy

/-- The deterministic kernel that maps `x : α` to the Dirac measure at `(x, x) : α × α`. -/
noncomputable
/-
**ProbabilityTheory.Kernel.copy** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ker
nel`。
形式化陈述：copy (α : Type*) [MeasurableSpace α] : Kernel α (α × α)
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def copy (α : Type*) [MeasurableSpace α] : Kernel α (α × α) :=
  Kernel.deterministic Function.diag (measurable_id.prod measurable_id)
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMarkovKernel (copy α) := by rw [copy]; infer_instance
/-
**ProbabilityTheory.Kernel.copy_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：copy_apply (a : α) : copy α a = Measure.dirac (a, a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma copy_apply (a : α) : copy α a = Measure.dirac (a, a) := by simp [copy, deterministic_apply]

end Copy

section Discard

/-- The Markov kernel to the `PUnit` type. -/
noncomputable
/-
**ProbabilityTheory.Kernel.discard** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.
Kernel`。
形式化陈述：discard (α : Type*) [MeasurableSpace α] : Kernel α PUnit
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
def discard (α : Type*) [MeasurableSpace α] : Kernel α PUnit :=
  Kernel.deterministic (fun _ ↦ PUnit.unit) measurable_const
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMarkovKernel (discard α) := by rw [discard]; infer_instance

@[simp]
/-
**ProbabilityTheory.Kernel.discard_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：discard_apply (a : α) : discard α a = Measure.dirac PUnit.unit
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
lemma discard_apply (a : α) : discard α a = Measure.dirac PUnit.unit := deterministic_apply _ _

end Discard

section Swap

/-- The deterministic kernel that maps `(x, y)` to the Dirac measure at `(y, x)`. -/
noncomputable
/-
**ProbabilityTheory.Kernel.swap** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ker
nel`。
形式化陈述：swap (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Kernel (α × β
) (β × α)
参数：α β : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
def swap (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Kernel (α × β) (β × α) :=
  Kernel.deterministic Prod.swap measurable_swap
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMarkovKernel (swap α β) := by rw [swap]; infer_instance

/-- See `swap_apply'` for a fully applied version of this lemma. -/
/-
**ProbabilityTheory.Kernel.swap_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：swap_apply (ab : α × β) : swap α β ab = Measure.dirac ab.swap
参数：ab : α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.swap.eq_1`：∀ (α : Type u_4) (β : Type u_5) [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β],   ProbabilityTheory.Kernel.
swap α β = ProbabilityTh…
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)

--- 原说明 ---
See `swap_apply'` for a fully applied version of this lemma.
-/
lemma swap_apply (ab : α × β) : swap α β ab = Measure.dirac ab.swap := by
  rw [swap, deterministic_apply]

/-- See `swap_apply` for a partially applied version of this lemma. -/
/-
**ProbabilityTheory.Kernel.swap_apply'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：swap_apply' (ab : α × β) {s : Set (β × α)} (hs : MeasurableSet s) : swap α
 β ab s = s.indicator 1 ab.swap
参数：ab : α × β；β × α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.swap_apply`：swap_apply (ab : α × β) : swap α β 
ab = Measure.dirac ab.swap
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a

--- 原说明 ---
See `swap_apply` for a partially applied version of this lemma.
-/
lemma swap_apply' (ab : α × β) {s : Set (β × α)} (hs : MeasurableSet s) :
    swap α β ab s = s.indicator 1 ab.swap := by
  rw [swap_apply, Measure.dirac_apply' _ hs]

end Swap

section Const

/-- Constant kernel, which always returns the same measure. -/
/-
**ProbabilityTheory.Kernel.const** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ke
rnel`。
形式化陈述：const (α : Type*) {β : Type*} [MeasurableSpace α] {_ : MeasurableSpace β} 
(μβ : Measure β) : Kernel α β where toFun _
参数：α : Type*；μβ : Measure β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constant kernel, which always returns the same measure.
-/
def const (α : Type*) {β : Type*} [MeasurableSpace α] {_ : MeasurableSpace β} (μβ : Measure β) :
    Kernel α β where
  toFun _ := μβ
  measurable' := measurable_const

@[simp]
/-
**ProbabilityTheory.Kernel.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：const_apply (μβ : Measure β) (a : α) : const α μβ a = μβ
参数：μβ : Measure β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_apply (μβ : Measure β) (a : α) : const α μβ a = μβ :=
  rfl

@[simp]
/-
**ProbabilityTheory.Kernel.const_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：const_zero : const α (0 : Measure β) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
lemma const_zero : const α (0 : Measure β) = 0 := by
  ext x s _; simp [const_apply]
/-
**ProbabilityTheory.Kernel.const_add** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：const_add (β : Type*) [MeasurableSpace β] (μ ν : Measure α) : const β (μ +
 ν) = const β μ + const β ν
参数：β : Type*；μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
lemma const_add (β : Type*) [MeasurableSpace β] (μ ν : Measure α) :
    const β (μ + ν) = const β μ + const β ν := by ext; simp
/-
**ProbabilityTheory.Kernel.sum_const** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：sum_const [Countable ι] (μ : ι -> Measure β) : Kernel.sum (fun n => const 
α (μ n)) = const α (Measure.sum μ)
参数：μ : ι -> Measure β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sum_const [Countable ι] (μ : ι → Measure β) :
    Kernel.sum (fun n ↦ const α (μ n)) = const α (Measure.sum μ) := rfl
/-
**ProbabilityTheory.Kernel.const.instIsFiniteKernel** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.const`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μβ : MeasureTheory.Measure β}   [MeasureTheory.IsFiniteMeasure μβ], Pro
babilityTheory.IsFiniteKernel (ProbabilityTheory.Kernel.const α μβ)
参数：ProbabilityTheory.Kernel.const α μβ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
instance const.instIsFiniteKernel {μβ : Measure β} [IsFiniteMeasure μβ] :
    IsFiniteKernel (const α μβ) :=
  ⟨⟨μβ Set.univ, measure_lt_top _ _, fun _ => le_rfl⟩⟩
/-
**ProbabilityTheory.Kernel.const.instIsSFiniteKernel** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.const`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μβ : MeasureTheory.Measure β}   [MeasureTheory.SFinite μβ], Probability
Theory.IsSFiniteKernel (ProbabilityTheory.Kernel.const α μβ)
参数：ProbabilityTheory.Kernel.const α μβ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.sum_const`：sum_const [Countable ι] (μ : ι -> Me
asure β) : Kernel.sum (fun n => const α (μ n)) = const α (Measure.sum μ)
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
-/
instance const.instIsSFiniteKernel {μβ : Measure β} [SFinite μβ] :
    IsSFiniteKernel (const α μβ) :=
  ⟨fun n ↦ const α (sfiniteSeq μβ n), fun n ↦ inferInstance, by rw [sum_const, sum_sfiniteSeq]⟩
/-
**ProbabilityTheory.Kernel.const.instIsMarkovKernel** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.const`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μβ : MeasureTheory.Measure β}   [hμβ : MeasureTheory.IsProbabilityMeasu
re μβ], ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.Kernel.const α μβ)
参数：ProbabilityTheory.Kernel.const α μβ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance const.instIsMarkovKernel {μβ : Measure β} [hμβ : IsProbabilityMeasure μβ] :
    IsMarkovKernel (const α μβ) :=
  ⟨fun _ => hμβ⟩
/-
**ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.Kernel.const`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μβ : MeasureTheory.Measure β}   [hμβ : MeasureTheory.IsZeroOrProbabilit
yMeasure μβ],   ProbabilityTheory.IsZeroOrMarkovKernel (ProbabilityTheory.Kernel
.const α μβ)
参数：ProbabilityTheory.Kernel.const α μβ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eq_zero_or_isProbabilityMeasure`：eq_zero_or_isProbabilityM
easure : μ = 0 ∨ IsProbabilityMeasure μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.const_zero`：const_zero : const α (0 : Measure β
) = 0
· 使用定理 `ProbabilityTheory.instIsZeroOrMarkovKernelOfNatKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   ProbabilityT
heory.IsZeroOrMarkovKernel 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsMarkovKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [hμβ : MeasureTheory.IsPr…
-/
instance const.instIsZeroOrMarkovKernel {μβ : Measure β} [hμβ : IsZeroOrProbabilityMeasure μβ] :
    IsZeroOrMarkovKernel (const α μβ) := by
  rcases eq_zero_or_isProbabilityMeasure μβ with rfl | h
  · simp only [const_zero]
    infer_instance
  · infer_instance
/-
**ProbabilityTheory.Kernel.isSFiniteKernel_const** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：isSFiniteKernel_const [Nonempty α] {μβ : Measure β} : IsSFiniteKernel (con
st α μβ) ↔ SFinite μβ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
-/
lemma isSFiniteKernel_const [Nonempty α] {μβ : Measure β} :
    IsSFiniteKernel (const α μβ) ↔ SFinite μβ :=
  ⟨fun h ↦ h.sFinite (Classical.arbitrary α), fun _ ↦ inferInstance⟩
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty β] : Nonempty {κ : Kernel α β // IsMarkovKernel κ} :=
  nonempty_subtype.2 ⟨Kernel.const _ (Measure.dirac Classical.ofNonempty), inferInstance⟩

@[simp]
/-
**ProbabilityTheory.Kernel.lintegral_const** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：lintegral_const {f : β -> Real>=0∞} {μ : Measure β} {a : α} : ∫⁻ x, f x ∂c
onst α μ a = ∫⁻ x, f x ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ
-/
theorem lintegral_const {f : β → ℝ≥0∞} {μ : Measure β} {a : α} :
    ∫⁻ x, f x ∂const α μ a = ∫⁻ x, f x ∂μ := by rw [const_apply]

@[simp]
/-
**ProbabilityTheory.Kernel.setLIntegral_const** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：setLIntegral_const {f : β -> Real>=0∞} {μ : Measure β} {a : α} {s : Set β}
 : ∫⁻ x in s, f x ∂const α μ a = ∫⁻ x in s, f x ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ
-/
theorem setLIntegral_const {f : β → ℝ≥0∞} {μ : Measure β} {a : α} {s : Set β} :
    ∫⁻ x in s, f x ∂const α μ a = ∫⁻ x in s, f x ∂μ := by rw [const_apply]
/-
**ProbabilityTheory.Kernel.discard_eq_const** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：discard_eq_const : discard α = const α (Measure.dirac PUnit.unit)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma discard_eq_const : discard α = const α (Measure.dirac PUnit.unit) := rfl

end Const

/-- In a countable space with measurable singletons, every function `α → MeasureTheory.Measure β`
defines a kernel. -/
/-
**ProbabilityTheory.Kernel.ofFunOfCountable** 是 Mathlib 中的一个定义，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：ofFunOfCountable [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α]
 [MeasurableSingletonClass α] (f : α -> Measure β) : Kernel α β where toFun
参数：f : α -> Measure β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a countable space with measurable singletons, every function `α → MeasureTheo
ry.Measure β`
defines a kernel.
-/
def ofFunOfCountable [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α]
    [MeasurableSingletonClass α] (f : α → Measure β) : Kernel α β where
  toFun := f
  measurable' := measurable_of_countable f

section Restrict

variable {s t : Set β}

/-- Kernel given by the restriction of the measures in the image of a kernel to a set. -/
/-
**ProbabilityTheory.Kernel.restrict** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {mα : MeasurableSpace α} →       {
mβ : MeasurableSpace β} →         {s : Set β} → ProbabilityTheory.Kernel α β → M
easurableSet s → ProbabilityTheory.Kernel α β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Kernel given by the restriction of the measures in the image of a kernel to a se
t.
-/
protected noncomputable def restrict (κ : Kernel α β) (hs : MeasurableSet s) : Kernel α β where
  toFun a := (κ a).restrict s
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    simp_rw [Measure.restrict_apply ht]
    exact Kernel.measurable_coe κ (ht.inter hs)
/-
**ProbabilityTheory.Kernel.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：restrict_apply (κ : Kernel α β) (hs : MeasurableSet s) (a : α) : κ.restric
t hs a = (κ a).restrict s
参数：κ : Kernel α β；hs : MeasurableSet s；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_apply (κ : Kernel α β) (hs : MeasurableSet s) (a : α) :
    κ.restrict hs a = (κ a).restrict s :=
  rfl
/-
**ProbabilityTheory.Kernel.restrict_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：restrict_apply' (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (ht : Meas
urableSet t) : κ.restrict hs a t = (κ a) (t inter s)
参数：κ : Kernel α β；hs : MeasurableSet s；a : α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply`：restrict_apply (κ : Kernel α β)
 (hs : MeasurableSet s) (a : α) : κ.restrict hs a = (κ a).restrict s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
-/
theorem restrict_apply' (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (ht : MeasurableSet t) :
    κ.restrict hs a t = (κ a) (t ∩ s) := by
  rw [restrict_apply κ hs a, Measure.restrict_apply ht]

/-- The restriction of a constant kernel to a measurable set is equal
to the constant kernel of the restricted measure. -/
/-
**ProbabilityTheory.Kernel.restrict_const** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：restrict_const {μ : Measure β} (hs : MeasurableSet s) : (Kernel.const α μ)
.restrict hs = Kernel.const α (μ.restrict s)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The restriction of a constant kernel to a measurable set is equal
to the constant kernel of the restricted measure.
-/
theorem restrict_const {μ : Measure β} (hs : MeasurableSet s) :
    (Kernel.const α μ).restrict hs = Kernel.const α (μ.restrict s) := by
  ext a
  simp [Kernel.restrict_apply, Kernel.const_apply]

@[simp]
/-
**ProbabilityTheory.Kernel.restrict_univ** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：restrict_univ : κ.restrict MeasurableSet.univ = κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply`：restrict_apply (κ : Kernel α β)
 (hs : MeasurableSet s) (a : α) : κ.restrict hs a = (κ a).restrict s
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
theorem restrict_univ : κ.restrict MeasurableSet.univ = κ := by
  ext1 a
  rw [Kernel.restrict_apply, Measure.restrict_univ]

@[simp]
/-
**ProbabilityTheory.Kernel.lintegral_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：lintegral_restrict (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (f : β 
-> Real>=0∞) : ∫⁻ b, f b ∂κ.restrict hs a = ∫⁻ b in s, f b ∂κ a
参数：κ : Kernel α β；hs : MeasurableSet s；a : α；f : β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply`：restrict_apply (κ : Kernel α β)
 (hs : MeasurableSet s) (a : α) : κ.restrict hs a = (κ a).restrict s
-/
theorem lintegral_restrict (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (f : β → ℝ≥0∞) :
    ∫⁻ b, f b ∂κ.restrict hs a = ∫⁻ b in s, f b ∂κ a := by rw [restrict_apply]

@[simp]
/-
**ProbabilityTheory.Kernel.setLIntegral_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：setLIntegral_restrict (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (f :
 β -> Real>=0∞) (t : Set β) : ∫⁻ b in t, f b ∂κ.restrict hs a = ∫⁻ b in t inter 
s, f b ∂κ a
参数：κ : Kernel α β；hs : MeasurableSet s；a : α；f : β -> Real>=0∞；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply`：restrict_apply (κ : Kernel α β)
 (hs : MeasurableSet s) (a : α) : κ.restrict hs a = (κ a).restrict s
· 使用定理 `MeasureTheory.Measure.restrict_restrict'`：restrict_restrict' (ht : Measu
rableSet t) : (μ.restrict t).restrict s = μ.restrict (s inter t)
-/
theorem setLIntegral_restrict (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (f : β → ℝ≥0∞)
    (t : Set β) : ∫⁻ b in t, f b ∂κ.restrict hs a = ∫⁻ b in t ∩ s, f b ∂κ a := by
  rw [restrict_apply, Measure.restrict_restrict' hs]
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.restrict** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {s : Set β}   (κ : ProbabilityTheory.Kernel α β) [ProbabilityTheory.IsFi
niteKernel κ] (hs : MeasurableSet s),   ProbabilityTheory.IsFiniteKernel (κ.rest
rict hs)
参数：κ : ProbabilityTheory.Kernel α β；hs : MeasurableSet s；κ.restrict hs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply'`：restrict_apply' (κ : Kernel α 
β) (hs : MeasurableSet s) (a : α) (ht : MeasurableSet t) : κ.restrict hs a t = (
κ a) (t inter s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
-/
instance IsFiniteKernel.restrict (κ : Kernel α β) [IsFiniteKernel κ] (hs : MeasurableSet s) :
    IsFiniteKernel (κ.restrict hs) := by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [restrict_apply' κ hs a MeasurableSet.univ]
  exact measure_le_bound κ a _
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.restrict** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {s : Set β}   (κ : ProbabilityTheory.Kernel α β) [ProbabilityTheory.IsSF
initeKernel κ] (hs : MeasurableSet s),   ProbabilityTheory.IsSFiniteKernel (κ.re
strict hs)
参数：κ : ProbabilityTheory.Kernel α β；hs : MeasurableSet s；κ.restrict hs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.restrict`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {s : Set β}   (κ : P
robabilityTheory.Kernel α β) [Probabil…
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_sum`：restrict_sum (μ : ι -> Measure α) {s
 : Set α} (hs : MeasurableSet s) : (sum μ).restrict s = sum fun i => (μ i).restr
ict s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.kernel_sum_seq`：kernel_sum_seq (κ : Kernel α β)
 [h : IsSFiniteKernel κ] : Kernel.sum (seq κ) = κ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance IsSFiniteKernel.restrict (κ : Kernel α β) [IsSFiniteKernel κ] (hs : MeasurableSet s) :
    IsSFiniteKernel (κ.restrict hs) := by
  refine ⟨⟨fun n => Kernel.restrict (seq κ n) hs, inferInstance, ?_⟩⟩
  ext1 a
  simp_rw [sum_apply, restrict_apply, ← Measure.restrict_sum _ hs, ← sum_apply, kernel_sum_seq]

end Restrict

section ComapRight

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : γ → β}

/-- Kernel with value `(κ a).comap f`, for a measurable embedding `f`. That is, for a measurable set
`t : Set β`, `ProbabilityTheory.Kernel.comapRight κ hf a t = κ a (f '' t)`. -/
/-
**ProbabilityTheory.Kernel.comapRight** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：comapRight (κ : Kernel α β) (hf : MeasurableEmbedding f) : Kernel α γ wher
e toFun a
参数：κ : Kernel α β；hf : MeasurableEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Kernel with value `(κ a).comap f`, for a measurable embedding `f`. That is, for 
a measurable set
`t : Set β`, `ProbabilityTheory.Kernel.comapRight κ hf a t = κ a (f '' t)`.
-/
noncomputable def comapRight (κ : Kernel α β) (hf : MeasurableEmbedding f) : Kernel α γ where
  toFun a := (κ a).comap f
  measurable' := by
    refine Measure.measurable_measure.mpr fun t ht => ?_
    have : (fun a => Measure.comap f (κ a) t) = fun a => κ a (f '' t) := by
      ext1 a
      rw [Measure.comap_apply _ hf.injective _ _ ht]
      exact fun s' hs' ↦ hf.measurableSet_image.mpr hs'
    rw [this]
    exact Kernel.measurable_coe _ (hf.measurableSet_image.mpr ht)
/-
**ProbabilityTheory.Kernel.comapRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：comapRight_apply (κ : Kernel α β) (hf : MeasurableEmbedding f) (a : α) : c
omapRight κ hf a = Measure.comap f (κ a)
参数：κ : Kernel α β；hf : MeasurableEmbedding f；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapRight_apply (κ : Kernel α β) (hf : MeasurableEmbedding f) (a : α) :
    comapRight κ hf a = Measure.comap f (κ a) :=
  rfl
/-
**ProbabilityTheory.Kernel.comapRight_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：comapRight_apply' (κ : Kernel α β) (hf : MeasurableEmbedding f) (a : α) {t
 : Set γ} (ht : MeasurableSet t) : comapRight κ hf a t = κ a (f '' t)
参数：κ : Kernel α β；hf : MeasurableEmbedding f；a : α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comapRight_apply`：comapRight_apply (κ : Kernel 
α β) (hf : MeasurableEmbedding f) (a : α) : comapRight κ hf a = Measure.comap f 
(κ a)
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
-/
theorem comapRight_apply' (κ : Kernel α β) (hf : MeasurableEmbedding f) (a : α) {t : Set γ}
    (ht : MeasurableSet t) : comapRight κ hf a t = κ a (f '' t) := by
  rw [comapRight_apply,
    Measure.comap_apply _ hf.injective (fun s => hf.measurableSet_image.mpr) _ ht]

@[simp]
/-
**ProbabilityTheory.Kernel.comapRight_id** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：comapRight_id (κ : Kernel α β) : comapRight κ MeasurableEmbedding.id = κ
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasurableEmbedding.id`：id : MeasurableEmbedding (id : α -> α)
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comapRight_apply'`：comapRight_apply' (κ : Kerne
l α β) (hf : MeasurableEmbedding f) (a : α) {t : Set γ} (ht : MeasurableSet t) :
 comapRight κ hf a t = κ a (f ''…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comapRight_id (κ : Kernel α β) : comapRight κ MeasurableEmbedding.id = κ := by
  ext _ _ hs; rw [comapRight_apply' _ _ _ hs]; simp
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.comapRight** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} {f : γ → β} (κ : ProbabilityTh
eory.Kernel α β) (hf : MeasurableEmbedding f),   (∀ (a : α), (κ a) (Set.range f)
 = 1) → ProbabilityTheory.IsMarkovKernel (κ.comapRight hf)
参数：κ : ProbabilityTheory.Kernel α β；hf : MeasurableEmbedding f；∀ (a : α), (κ a) 
(Set.range f) = 1；κ.comapRight hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comapRight_apply'`：comapRight_apply' (κ : Kerne
l α β) (hf : MeasurableEmbedding f) (a : α) {t : Set γ} (ht : MeasurableSet t) :
 comapRight κ hf a t = κ a (f ''…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem IsMarkovKernel.comapRight (κ : Kernel α β) (hf : MeasurableEmbedding f)
    (hκ : ∀ a, κ a (Set.range f) = 1) : IsMarkovKernel (comapRight κ hf) := by
  refine ⟨fun a => ⟨?_⟩⟩
  rw [comapRight_apply' κ hf a MeasurableSet.univ]
  simp only [Set.image_univ]
  exact hκ a
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.comapRight** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} {f : γ → β} (κ : ProbabilityTh
eory.Kernel α β) [ProbabilityTheory.IsFiniteKernel κ]   (hf : MeasurableEmbeddin
g f), ProbabilityTheory.IsFiniteKernel (κ.comapRight hf)
参数：κ : ProbabilityTheory.Kernel α β；hf : MeasurableEmbedding f；κ.comapRight hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comapRight_apply'`：comapRight_apply' (κ : Kerne
l α β) (hf : MeasurableEmbedding f) (a : α) {t : Set γ} (ht : MeasurableSet t) :
 comapRight κ hf a t = κ a (f ''…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
-/
instance IsFiniteKernel.comapRight (κ : Kernel α β) [IsFiniteKernel κ]
    (hf : MeasurableEmbedding f) : IsFiniteKernel (comapRight κ hf) := by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩⟩
  rw [comapRight_apply' κ hf a .univ]
  exact measure_le_bound κ a _
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.comapRight** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} {f : γ → β} (κ : ProbabilityTh
eory.Kernel α β) [ProbabilityTheory.IsSFiniteKernel κ]   (hf : MeasurableEmbeddi
ng f), ProbabilityTheory.IsSFiniteKernel (κ.comapRight hf)
参数：κ : ProbabilityTheory.Kernel α β；hf : MeasurableEmbedding f；κ.comapRight hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comapRight`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {
mγ : MeasurableSpace γ} {f : γ → β} (κ :…
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.sum_apply`：sum_apply [Countable ι] (κ : ι -> Ke
rnel α β) (a : α) : Kernel.sum κ a = Measure.sum fun n => κ n a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.comapRight_apply`：comapRight_apply (κ : Kernel 
α β) (hf : MeasurableEmbedding f) (a : α) : comapRight κ hf a = Measure.comap f 
(κ a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `ProbabilityTheory.Kernel.measure_sum_seq`：measure_sum_seq (κ : Kernel α 
β) [h : IsSFiniteKernel κ] (a : α) : (Measure.sum fun n => seq κ n a) = κ a
-/
protected instance IsSFiniteKernel.comapRight (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : MeasurableEmbedding f) : IsSFiniteKernel (comapRight κ hf) := by
  refine ⟨⟨fun n => comapRight (seq κ n) hf, inferInstance, ?_⟩⟩
  ext1 a
  rw [sum_apply]
  simp_rw [comapRight_apply _ hf]
  have :
    (Measure.sum fun n => Measure.comap f (seq κ n a)) =
      Measure.comap f (Measure.sum fun n => seq κ n a) := by
    ext1 t ht
    rw [Measure.comap_apply _ hf.injective (fun s' => hf.measurableSet_image.mpr) _ ht,
      Measure.sum_apply _ ht, Measure.sum_apply _ (hf.measurableSet_image.mpr ht)]
    congr with n : 1
    rw [Measure.comap_apply _ hf.injective (fun s' => hf.measurableSet_image.mpr) _ ht]
  rw [this, measure_sum_seq]

end ComapRight

section Piecewise

variable {η : Kernel α β} {s : Set α} {hs : MeasurableSet s} [DecidablePred (· ∈ s)]

/-- `ProbabilityTheory.Kernel.piecewise hs κ η` is the kernel equal to `κ` on the measurable set `s`
and to `η` on its complement. -/
/-
**ProbabilityTheory.Kernel.piecewise** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：piecewise (hs : MeasurableSet s) (κ η : Kernel α β) : Kernel α β where toF
un a
参数：hs : MeasurableSet s；κ η : Kernel α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ProbabilityTheory.Kernel.piecewise hs κ η` is the kernel equal to `κ` on the me
asurable set `s`
and to `η` on its complement.
-/
def piecewise (hs : MeasurableSet s) (κ η : Kernel α β) : Kernel α β where
  toFun a := if a ∈ s then κ a else η a
  measurable' := κ.measurable.piecewise hs η.measurable
/-
**ProbabilityTheory.Kernel.piecewise_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：piecewise_apply (a : α) : piecewise hs κ η a = if a in s then κ a else η a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piecewise_apply (a : α) : piecewise hs κ η a = if a ∈ s then κ a else η a :=
  rfl
/-
**ProbabilityTheory.Kernel.piecewise_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：piecewise_apply' (a : α) (t : Set β) : piecewise hs κ η a t = if a in s th
en κ a t else η a t
参数：a : α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.piecewise_apply`：piecewise_apply (a : α) : piec
ewise hs κ η a = if a in s then κ a else η a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem piecewise_apply' (a : α) (t : Set β) :
    piecewise hs κ η a t = if a ∈ s then κ a t else η a t := by
  rw [piecewise_apply]; split_ifs <;> rfl
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.piecewise** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ η : ProbabilityTheory.Kernel α β}   {s : Set α} {hs : MeasurableSet s
} [inst : DecidablePred fun x => x ∈ s] [ProbabilityTheory.IsMarkovKernel κ]   [
ProbabilityTheory.IsMarkovKernel η], ProbabilityTheory.IsMarkovKernel (Probabili
tyTheory.Kernel.piecewise hs κ η)
参数：ProbabilityTheory.Kernel.piecewise hs κ η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.piecewise_apply'`：piecewise_apply' (a : α) (t :
 Set β) : piecewise hs κ η a t = if a in s then κ a t else η a t
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
instance IsMarkovKernel.piecewise [IsMarkovKernel κ] [IsMarkovKernel η] :
    IsMarkovKernel (piecewise hs κ η) := by
  refine ⟨fun a => ⟨?_⟩⟩
  rw [piecewise_apply', measure_univ, measure_univ, ite_self]
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.piecewise** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ η : ProbabilityTheory.Kernel α β}   {s : Set α} {hs : MeasurableSet s
} [inst : DecidablePred fun x => x ∈ s] [ProbabilityTheory.IsFiniteKernel κ]   [
ProbabilityTheory.IsFiniteKernel η], ProbabilityTheory.IsFiniteKernel (Probabili
tyTheory.Kernel.piecewise hs κ η)
参数：ProbabilityTheory.Kernel.piecewise hs κ η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `ProbabilityTheory.Kernel.bound_lt_top`：bound_lt_top (κ : Kernel α β) [h 
: IsFiniteKernel κ] : κ.bound < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.piecewise_apply'`：piecewise_apply' (a : α) (t :
 Set β) : piecewise hs κ η a t = if a in s then κ a t else η a t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ite_le_sup`：ite_le_sup (a b : α) (P : Prop) [Decidable P] : ite P a b <=
 a ⊔ b
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
-/
instance IsFiniteKernel.piecewise [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (piecewise hs κ η) := by
  refine ⟨⟨max κ.bound η.bound, max_lt κ.bound_lt_top η.bound_lt_top, fun a => ?_⟩⟩
  rw [piecewise_apply']
  exact (ite_le_sup _ _ _).trans (sup_le_sup (measure_le_bound _ _ _) (measure_le_bound _ _ _))
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.piecewise** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ η : ProbabilityTheory.Kernel α β}   {s : Set α} {hs : MeasurableSet s
} [inst : DecidablePred fun x => x ∈ s] [ProbabilityTheory.IsSFiniteKernel κ]   
[ProbabilityTheory.IsSFiniteKernel η], ProbabilityTheory.IsSFiniteKernel (Probab
ilityTheory.Kernel.piecewise hs κ η)
参数：ProbabilityTheory.Kernel.piecewise hs κ η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.piecewise`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : ProbabilityT
heory.Kernel α β}   {s : Set α} {hs : M…
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.measure_sum_seq`：measure_sum_seq (κ : Kernel α 
β) [h : IsSFiniteKernel κ] (a : α) : (Measure.sum fun n => seq κ n a) = κ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
protected instance IsSFiniteKernel.piecewise [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (piecewise hs κ η) := by
  refine ⟨⟨fun n => piecewise hs (seq κ n) (seq η n), inferInstance, ?_⟩⟩
  ext1 a
  simp_rw [sum_apply, Kernel.piecewise_apply]
  split_ifs <;> exact (measure_sum_seq _ a).symm
/-
**ProbabilityTheory.Kernel.lintegral_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：lintegral_piecewise (a : α) (g : β -> Real>=0∞) : ∫⁻ b, g b ∂piecewise hs 
κ η a = if a in s then ∫⁻ b, g b ∂κ a else ∫⁻ b, g b ∂η a
参数：a : α；g : β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem lintegral_piecewise (a : α) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂piecewise hs κ η a = if a ∈ s then ∫⁻ b, g b ∂κ a else ∫⁻ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl
/-
**ProbabilityTheory.Kernel.setLIntegral_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：setLIntegral_piecewise (a : α) (g : β -> Real>=0∞) (t : Set β) : ∫⁻ b in t
, g b ∂piecewise hs κ η a = if a in s then ∫⁻ b in t, g b ∂κ a else ∫⁻ b in t, g
 b ∂η a
参数：a : α；g : β -> Real>=0∞；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem setLIntegral_piecewise (a : α) (g : β → ℝ≥0∞) (t : Set β) :
    ∫⁻ b in t, g b ∂piecewise hs κ η a =
      if a ∈ s then ∫⁻ b in t, g b ∂κ a else ∫⁻ b in t, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

end Piecewise

/-
**ProbabilityTheory.Kernel.exists_ae_eq_isMarkovKernel** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：exists_ae_eq_isMarkovKernel {μ : Measure α} (h : forallᵐ a ∂μ, IsProbabili
tyMeasure (κ a)) (h' : μ != 0) : exists (η : Kernel α β), (κ =ᵐ[μ] η) ∧ IsMarkov
Kernel η
参数：h : forallᵐ a ∂μ, IsProbabilityMeasure (κ a)；h' : μ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `MeasureTheory.measure_univ_le_add_compl`：measure_univ_le_add_compl (s : 
Set α) : μ univ <= μ s + μ sᶜ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.measure_eq_zero_iff_ae_notMem`：measure_eq_zero_iff_ae_notM
em {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma exists_ae_eq_isMarkovKernel {μ : Measure α}
    (h : ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a)) (h' : μ ≠ 0) :
    ∃ (η : Kernel α β), (κ =ᵐ[μ] η) ∧ IsMarkovKernel η := by
  classical
  obtain ⟨s, s_meas, μs, hs⟩ : ∃ s, MeasurableSet s ∧ μ s = 0
      ∧ ∀ a ∉ s, IsProbabilityMeasure (κ a) := by
    refine ⟨toMeasurable μ {a | ¬ IsProbabilityMeasure (κ a)}, measurableSet_toMeasurable _ _,
      by simpa [measure_toMeasurable] using! h, ?_⟩
    intro a ha
    contrapose ha
    exact subset_toMeasurable _ _ ha
  obtain ⟨a, ha⟩ : sᶜ.Nonempty := by
    contrapose! h'; simpa [μs, h'] using! measure_univ_le_add_compl s (μ := μ)
  refine ⟨Kernel.piecewise s_meas (Kernel.const _ (κ a)) κ, ?_, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 μs] with b hb
    simp [hb, piecewise]
  · refine ⟨fun b ↦ ?_⟩
    by_cases hb : b ∈ s
    · simpa [hb, piecewise] using! hs _ ha
    · simpa [hb, piecewise] using! hs _ hb

section Bool

variable {μ ν : Measure α}

/-- The kernel from `Bool` that sends `false` to `μ` and `true` to `ν`. -/
/-
**ProbabilityTheory.Kernel.boolKernel** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：boolKernel (μ ν : Measure α) : Kernel Bool α where toFun
参数：μ ν : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel from `Bool` that sends `false` to `μ` and `true` to `ν`.
-/
def boolKernel (μ ν : Measure α) : Kernel Bool α where
  toFun := fun b ↦ if b then ν else μ
  measurable' := .of_discrete
/-
**ProbabilityTheory.Kernel.boolKernel_false** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：boolKernel_false : boolKernel μ ν false = μ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma boolKernel_false : boolKernel μ ν false = μ := rfl
/-
**ProbabilityTheory.Kernel.boolKernel_true** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：boolKernel_true : boolKernel μ ν true = ν
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma boolKernel_true : boolKernel μ ν true = ν := rfl
/-
**ProbabilityTheory.Kernel.boolKernel_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} 
(b : Bool),   (ProbabilityTheory.Kernel.boolKernel μ ν) b = if b = true then ν e
lse μ
参数：b : Bool；ProbabilityTheory.Kernel.boolKernel μ ν。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma boolKernel_apply (b : Bool) : boolKernel μ ν b = if b then ν else μ := rfl
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteKernel (boolKernel μ ν) :=
  ⟨max (μ .univ) (ν .univ), max_lt (measure_lt_top _ _) (measure_lt_top _ _),
    fun b ↦ by cases b <;> simp⟩
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsMarkovKernel (boolKernel μ ν) where
  isProbabilityMeasure b := by
    cases b
      <;> simp only [boolKernel_apply, Bool.false_eq_true, ↓reduceIte]
      <;> infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SFinite μ] [SFinite ν] : IsSFiniteKernel (boolKernel μ ν) where
  tsum_finite := by
    refine ⟨fun n ↦ boolKernel (sfiniteSeq μ n) (sfiniteSeq ν n), fun n ↦ inferInstance, ?_⟩
    ext b
    rw [Kernel.sum_apply]
    cases b <;> simp [sum_sfiniteSeq]
/-
**ProbabilityTheory.Kernel.eq_boolKernel** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：eq_boolKernel (κ : Kernel Bool α) : κ = boolKernel (κ false) (κ true)
参数：κ : Kernel Bool α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
lemma eq_boolKernel (κ : Kernel Bool α) : κ = boolKernel (κ false) (κ true) := by
  ext (_ | _) <;> simp

end Bool

end Kernel
end ProbabilityTheory

