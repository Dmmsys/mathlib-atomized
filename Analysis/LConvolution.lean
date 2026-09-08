/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Convolution of functions using the Lebesgue integral

In this file we define and prove properties about the convolution of two functions
using the Lebesgue integral.

## Design Decisions

We define the convolution of two functions using the Lebesgue integral (in the additive case)
by the formula `(f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (-y + x)) ∂μ`. This does not agree with the
formula used by `MeasureTheory.convolution` for convolution of two functions, however it does agree
when the domain of `f` and `g` is a commutative group. The main reason for this is so that
(under sufficient conditions) if `{μ ν π : Measure G} {f g : G → ℝ≥0∞}` are such that
`μ = π.withDensity f`, `ν = π.withDensity g` where `π` is left-invariant then
`(μ ∗ ν) = π.withDensity (f ⋆ₗ[π] g)`. If the formula in `MeasureTheory.convolution` was used
the order of the densities would be flipped.

## Main Definitions

* `MeasureTheory.mlconvolution f g μ x = (f ⋆ₘₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ`
  is the multiplicative convolution of `f` and `g` w.r.t. the measure `μ`.
* `MeasureTheory.lconvolution f g μ x = (f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (-y + x)) ∂μ`
  is the additive convolution of `f` and `g` w.r.t. the measure `μ`.
-/

@[expose] public section

namespace MeasureTheory
open Measure
open scoped ENNReal

variable {G : Type*} {mG : MeasurableSpace G}

section NoGroup

variable [Mul G] [Inv G]

/-- Multiplicative convolution of functions. -/
@[to_additive /-- Additive convolution of functions -/]
/-
**MeasureTheory.mlconvolution** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：mlconvolution (f g : G -> Real>=0∞) (μ : Measure G) : G -> Real>=0∞
参数：f g : G -> Real>=0∞；μ : Measure G。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplicative convolution of functions.
-/
noncomputable def mlconvolution (f g : G → ℝ≥0∞) (μ : Measure G) :
    G → ℝ≥0∞ := fun x ↦ ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ

/-- Scoped notation for the multiplicative convolution of functions with respect to a measure `μ`.
-/
scoped[MeasureTheory] notation:67 f " ⋆ₘₗ[" μ:67 "] " g:66 => MeasureTheory.mlconvolution f g μ

/-- Scoped notation for the multiplicative convolution of functions with respect to `volume`. -/
scoped[MeasureTheory] notation:67 f " ⋆ₘₗ " g:66 => MeasureTheory.mlconvolution f g volume

/-- Scoped notation for the additive convolution of functions with respect to a measure `μ`. -/
scoped[MeasureTheory] notation:67 f " ⋆ₗ[" μ:67 "] " g:66 => MeasureTheory.lconvolution f g μ

/-- Scoped notation for the additive convolution of functions with respect to `volume`. -/
scoped[MeasureTheory] notation:67 f " ⋆ₗ " g:66 => MeasureTheory.lconvolution f g volume

/-- The definition of multiplicative convolution of functions. -/
@[to_additive /-- The definition of additive convolution of functions. -/]
/-
**MeasureTheory.mlconvolution_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mlconvolution_def {f g : G -> Real>=0∞} {μ : Measure G} {x : G} : (f ⋆ₘₗ[μ
] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of multiplicative convolution of functions.
-/
theorem mlconvolution_def {f g : G → ℝ≥0∞} {μ : Measure G} {x : G} :
    (f ⋆ₘₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ := rfl

/-- Convolution of the zero function with a function returns the zero function. -/
@[to_additive (attr := simp)
/-- Convolution of the zero function with a function returns the zero function. -/]
/-
**MeasureTheory.zero_mlconvolution** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：zero_mlconvolution (f : G -> Real>=0∞) (μ : Measure G) : 0 ⋆ₘₗ[μ] f = 0
参数：f : G -> Real>=0∞；μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_mlconvolution (f : G → ℝ≥0∞) (μ : Measure G) : 0 ⋆ₘₗ[μ] f = 0 := by
  ext; simp [mlconvolution]

/-- Convolution of a function with the zero function returns the zero function. -/
@[to_additive (attr := simp)
/-- Convolution of a function with the zero function returns the zero function. -/]
/-
**MeasureTheory.mlconvolution_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mlconvolution_zero (f : G -> Real>=0∞) (μ : Measure G) : f ⋆ₘₗ[μ] 0 = 0
参数：f : G -> Real>=0∞；μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mlconvolution_zero (f : G → ℝ≥0∞) (μ : Measure G) : f ⋆ₘₗ[μ] 0 = 0 := by
  ext; simp [mlconvolution]

section Measurable

variable [MeasurableMul₂ G] [MeasurableInv G]

/-- The convolution of measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The convolution of measurable functions is measurable. -/]
/-
**MeasureTheory.measurable_mlconvolution** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measurable_mlconvolution {f g : G -> Real>=0∞} (μ : Measure G) [SFinite μ]
 (hf : Measurable f) (hg : Measurable g) : Measurable (f ⋆ₘₗ[μ] g)
参数：μ : Measure G；hf : Measurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.lintegral_prod_right`：Measurable.lintegral_prod_right [SFinit
e ν] {f : α -> β -> Real>=0∞} (hf : Measurable (uncurry f)) : Measurable fun x =
> ∫⁻ y, f x y ∂ν
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fun_inv`：∀ {G : Type u_2} {α : Type u_3} [inst : Inv G] [inst
_1 : MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}   {f : α → G},
 Measura…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
-/
theorem measurable_mlconvolution {f g : G → ℝ≥0∞} (μ : Measure G) [SFinite μ]
    (hf : Measurable f) (hg : Measurable g) : Measurable (f ⋆ₘₗ[μ] g) := by
  unfold mlconvolution
  fun_prop

end Measurable

end NoGroup

section Group

variable [Group G] [MeasurableMul₂ G] [MeasurableInv G]

variable {μ : Measure G} [IsMulLeftInvariant μ] [SFinite μ]

/-- The convolution of `AEMeasurable` functions is `AEMeasurable`. -/
@[to_additive (attr := fun_prop)
/-- The convolution of `AEMeasurable` functions is `AEMeasurable`. -/]
/-
**MeasureTheory.aemeasurable_mlconvolution** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：aemeasurable_mlconvolution {f g : G -> Real>=0∞} (hf : AEMeasurable f μ) (
hg : AEMeasurable g μ) : AEMeasurable (f ⋆ₘₗ[μ] g) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.lintegral_prod_left`：AEMeasurable.lintegral_prod_left [SFin
ite ν] [SFinite μ] {f : α -> β -> Real>=0∞} (hf : AEMeasurable f.uncurry (μ.prod
 ν)) : AEMeasurable (f…
· 使用定理 `AEMeasurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTh
eory.Measu…
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.QuasiMeasurePreserving.fst`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst
_2 : MeasurableSpace γ] {μ : M…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.id`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α),   MeasureTheory.Measure.Quasi
MeasurePreserving id μ μ
· 使用定理 `MeasureTheory.quasiMeasurePreserving_inv_mul`：quasiMeasurePreserving_inv
_mul [IsMulLeftInvariant ν] : QuasiMeasurePreserving (fun p => p.1⁻¹ * p.2) (μ.p
rod ν) ν
-/
theorem aemeasurable_mlconvolution {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f ⋆ₘₗ[μ] g) μ := by
  unfold mlconvolution
  fun_prop

@[to_additive]
/-
**MeasureTheory.mlconvolution_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mlconvolution_assoc {f g k : G -> Real>=0∞} (hf : Measurable f) (hg : Meas
urable g) (hk : Measurable k) : f ⋆ₘₗ[μ] g ⋆ₘₗ[μ] k = (f ⋆ₘₗ[μ] g) ⋆ₘₗ[μ] k
参数：hf : Measurable f；hg : Measurable g；hk : Measurable k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.mlconvolution_assoc₀`：mlconvolution_assoc₀ {f g k : G -> R
eal>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hk : AEMeasurable k μ)
 : f ⋆ₘₗ[μ] g ⋆ₘₗ[μ] k =…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem mlconvolution_assoc₀ {f g k : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hk : AEMeasurable k μ) :
    f ⋆ₘₗ[μ] g ⋆ₘₗ[μ] k = (f ⋆ₘₗ[μ] g) ⋆ₘₗ[μ] k := by
  ext x
  simp only [mlconvolution_def]
  conv in f _ * (∫⁻ _, _ ∂μ) =>
    rw [← lintegral_const_mul'' _ (by fun_prop), ← lintegral_mul_left_eq_self _ y⁻¹]
  conv in (∫⁻ _, _ ∂μ) * k _ =>
    rw [← lintegral_mul_const'' _ (by fun_prop)]
  rw [lintegral_lintegral_swap]
  · simp [mul_assoc]
  simpa [mul_assoc] using by fun_prop

/-- Convolution is associative. -/
@[to_additive /-- Convolution is associative. -/]
/-
**MeasureTheory.mlconvolution_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mlconvolution_assoc {f g k : G -> Real>=0∞} (hf : Measurable f) (hg : Meas
urable g) (hk : Measurable k) : f ⋆ₘₗ[μ] g ⋆ₘₗ[μ] k = (f ⋆ₘₗ[μ] g) ⋆ₘₗ[μ] k
参数：hf : Measurable f；hg : Measurable g；hk : Measurable k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.mlconvolution_assoc₀`：mlconvolution_assoc₀ {f g k : G -> R
eal>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hk : AEMeasurable k μ)
 : f ⋆ₘₗ[μ] g ⋆ₘₗ[μ] k =…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
Convolution is associative.
-/
theorem mlconvolution_assoc {f g k : G → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) :
    f ⋆ₘₗ[μ] g ⋆ₘₗ[μ] k = (f ⋆ₘₗ[μ] g) ⋆ₘₗ[μ] k :=
  mlconvolution_assoc₀ hf.aemeasurable hg.aemeasurable hk.aemeasurable

end Group

section CommGroup

variable [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G}

/-- Convolution is commutative when the group is commutative. -/
@[to_additive /-- Convolution is commutative when the group is commutative. -/]
/-
**MeasureTheory.mlconvolution_comm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mlconvolution_comm [IsMulLeftInvariant μ] [IsInvInvariant μ] {f g : G -> R
eal>=0∞} : (f ⋆ₘₗ[μ] g) = (g ⋆ₘₗ[μ] f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_mul_left_eq_self`：lintegral_mul_left_eq_self [Is
MulLeftInvariant μ] (f : G -> Real>=0∞) (g : G) : (∫⁻ x, f (g * x) ∂μ) = ∫⁻ x, f
 x ∂μ
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.lintegral_inv_eq_self`：lintegral_inv_eq_self [IsInvInvaria
nt μ] (f : G -> Real>=0∞) : ∫⁻ x, f x⁻¹ ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_inv_cancel_comm_assoc`：∀ {G : Type u_1} [inst : CommGroup G] (a b : 
G), a * (b * a⁻¹) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Convolution is commutative when the group is commutative.
-/
theorem mlconvolution_comm [IsMulLeftInvariant μ] [IsInvInvariant μ] {f g : G → ℝ≥0∞} :
    (f ⋆ₘₗ[μ] g) = (g ⋆ₘₗ[μ] f) := by
  ext x
  simp only [mlconvolution_def]
  rw [← lintegral_mul_left_eq_self _ x, ← lintegral_inv_eq_self]
  simp [mul_comm]

end CommGroup

end MeasureTheory

