/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Group.Measure

/-!
# Lebesgue Integration on Groups

We develop properties of integrals with a group as domain.
This file contains properties about Lebesgue integration.
-/

public section

assert_not_exists NormedSpace

namespace MeasureTheory

open Measure TopologicalSpace

open scoped ENNReal

variable {G : Type*} [MeasurableSpace G] {μ : Measure G}

section MeasurableInv

variable [InvolutiveInv G] [MeasurableInv G]

/-- The Lebesgue integral of a function with respect to an inverse invariant measure is
invariant under the change of variables x ↦ x⁻¹. -/
@[to_additive
      /-- The Lebesgue integral of a function with respect to an inverse invariant measure is
invariant under the change of variables x ↦ -x. -/]
/-
**MeasureTheory.lintegral_inv_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_inv_eq_self [IsInvInvariant μ] (f : G -> Real>=0∞) : ∫⁻ x, f x⁻¹
 ∂μ = ∫⁻ x, f x ∂μ
参数：f : G -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasurableEquiv.inv_apply`：∀ (G : Type u_4) [inst : MeasurableSpace G] [
inst_1 : InvolutiveInv G] [inst_2 : MeasurableInv G],   ⇑(MeasurableEquiv.inv G)
 = Inv.inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.map_inv_eq_self`：map_inv_eq_self (μ : Measure G) [
IsInvInvariant μ] : map Inv.inv μ = μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_map_equiv`：lintegral_map_equiv (f : β -> Real>=0
∞) (g : α ≃ᵐ β) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ
-/
theorem lintegral_inv_eq_self [IsInvInvariant μ] (f : G → ℝ≥0∞) :
    ∫⁻ x, f x⁻¹ ∂μ = ∫⁻ x, f x ∂μ := by
  simpa using (lintegral_map_equiv f (μ := μ) <| MeasurableEquiv.inv G).symm

end MeasurableInv

section MeasurableMul

variable [Group G] [MeasurableMul G]

/-- Translating a function by left-multiplication does not change its Lebesgue integral
with respect to a left-invariant measure. -/
@[to_additive
      /-- Translating a function by left-addition does not change its Lebesgue integral with
      respect to a left-invariant measure. -/]
/-
**MeasureTheory.lintegral_mul_left_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：lintegral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G -> Real>=0∞) (g :
 G) : (∫⁻ x, f (g * x) ∂μ) = ∫⁻ x, f x ∂μ
参数：f : G -> Real>=0∞；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_map_equiv`：lintegral_map_equiv (f : β -> Real>=0
∞) (g : α ≃ᵐ β) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ
-/
theorem lintegral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (g * x) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert! (lintegral_map_equiv f <| MeasurableEquiv.mulLeft g).symm
  simp [map_mul_left_eq_self μ g]

/-- Translating a function by right-multiplication does not change its Lebesgue integral
with respect to a right-invariant measure. -/
@[to_additive
      /-- Translating a function by right-addition does not change its Lebesgue integral with
      respect to a right-invariant measure. -/]
/-
**MeasureTheory.lintegral_mul_right_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：lintegral_mul_right_eq_self [IsMulRightInvariant μ] (f : G -> Real>=0∞) (g
 : G) : (∫⁻ x, f (x * g) ∂μ) = ∫⁻ x, f x ∂μ
参数：f : G -> Real>=0∞；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_map_equiv`：lintegral_map_equiv (f : β -> Real>=0
∞) (g : α ≃ᵐ β) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ
-/
theorem lintegral_mul_right_eq_self [IsMulRightInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (x * g) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert! (lintegral_map_equiv f <| MeasurableEquiv.mulRight g).symm using 1
  simp [map_mul_right_eq_self μ g]

@[to_additive]
/-
**MeasureTheory.lintegral_div_right_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：lintegral_div_right_eq_self [IsMulRightInvariant μ] (f : G -> Real>=0∞) (g
 : G) : (∫⁻ x, f (x / g) ∂μ) = ∫⁻ x, f x ∂μ
参数：f : G -> Real>=0∞；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_mul_right_eq_self`：lintegral_mul_right_eq_self [
IsMulRightInvariant μ] (f : G -> Real>=0∞) (g : G) : (∫⁻ x, f (x * g) ∂μ) = ∫⁻ x
, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_div_right_eq_self [IsMulRightInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (x / g) ∂μ) = ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, lintegral_mul_right_eq_self f g⁻¹]

@[to_additive]
/-
**MeasureTheory.lintegral_div_left_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：lintegral_div_left_eq_self [IsMulLeftInvariant μ] [MeasurableInv G] [IsInv
Invariant μ] (f : G -> Real>=0∞) (g : G) : (∫⁻ x, f (g / x) ∂μ) = ∫⁻ x, f x ∂μ
参数：f : G -> Real>=0∞；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MeasureTheory.lintegral_inv_eq_self`：lintegral_inv_eq_self [IsInvInvaria
nt μ] (f : G -> Real>=0∞) : ∫⁻ x, f x⁻¹ ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_mul_left_eq_self`：lintegral_mul_left_eq_self [Is
MulLeftInvariant μ] (f : G -> Real>=0∞) (g : G) : (∫⁻ x, f (g * x) ∂μ) = ∫⁻ x, f
 x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_div_left_eq_self [IsMulLeftInvariant μ] [MeasurableInv G] [IsInvInvariant μ]
    (f : G → ℝ≥0∞) (g : G) : (∫⁻ x, f (g / x) ∂μ) = ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, lintegral_inv_eq_self (f <| g * ·), lintegral_mul_left_eq_self]

end MeasurableMul


section IsTopologicalGroup

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [BorelSpace G] [IsMulLeftInvariant μ]

/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
@[to_additive
      /-- For nonzero regular left invariant measures, the integral of a continuous nonnegative
      function `f` is 0 iff `f` is 0. -/]
/-
**MeasureTheory.lintegral_eq_zero_of_isMulLeftInvariant** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：lintegral_eq_zero_of_isMulLeftInvariant [Regular μ] [NeZero μ] {f : G -> R
eal>=0∞} (hf : Continuous f) : ∫⁻ x, f x ∂μ = 0 ↔ f = 0
参数：hf : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.ae_eq_iff_eq`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] {m : MeasurableSpace X} [inst_1 : TopologicalSpace Y]   [T2Space Y]
 (μ : Measure…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `MeasureTheory.isOpenPosMeasure_of_mulLeftInvariant_of_regular`：∀ {G : Ty
pe u_1} [inst : MeasurableSpace G] [inst_1 : TopologicalSpace G] [BorelSpace G] 
{μ : MeasureTheory.Measure G}   [inst_3 : Group G] …
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lintegral_eq_zero_of_isMulLeftInvariant [Regular μ] [NeZero μ] {f : G → ℝ≥0∞}
    (hf : Continuous f) : ∫⁻ x, f x ∂μ = 0 ↔ f = 0 := by
  rw [lintegral_eq_zero_iff hf.measurable, hf.ae_eq_iff_eq μ continuous_zero]

end IsTopologicalGroup

end MeasureTheory

