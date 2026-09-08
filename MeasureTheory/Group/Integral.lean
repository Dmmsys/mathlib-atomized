/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Bochner Integration on Groups

We develop properties of integrals with a group as domain.
This file contains properties about integrability and Bochner integration.
-/

public section

namespace MeasureTheory

open Measure TopologicalSpace

open scoped ENNReal

variable {𝕜 M α G E F : Type*} [MeasurableSpace G]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
variable {μ : Measure G} {f : G → E} {g : G}

section MeasurableInv

variable [Group G] [MeasurableInv G]

@[to_additive]
/-
**MeasureTheory.Integrable.comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {G : Type u_4} {F : Type u_6} [inst : MeasurableSpace G] [inst_1 : Norme
dAddCommGroup F] {μ : MeasureTheory.Measure G}   [inst_2 : Group G] [MeasurableI
nv G] [μ.IsInvInvariant] {f : G → F},   MeasureTheory.Integrable f μ → MeasureTh
eory.Integrable (fun t => f t⁻¹) μ
参数：fun t => f t⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.comp_measurable`：∀ {α : Type u_1} {ε : Type u_5
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace
 ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.Measure.map_inv_eq_self`：map_inv_eq_self (μ : Measure G) [
IsInvInvariant μ] : map Inv.inv μ = μ
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
-/
theorem Integrable.comp_inv [IsInvInvariant μ] {f : G → F} (hf : Integrable f μ) :
    Integrable (fun t => f t⁻¹) μ :=
  (hf.mono_measure (map_inv_eq_self μ).le).comp_measurable measurable_inv

@[to_additive]
/-
**MeasureTheory.integral_inv_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_inv_eq_self (f : G -> E) (μ : Measure G) [IsInvInvariant μ] : ∫ x
, f x⁻¹ ∂μ = ∫ x, f x ∂μ
参数：f : G -> E；μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.integral_map`：∀ {α : Type u_1} {G : Type u_5} [inst 
: NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}   {μ 
: MeasureTheory.Measur…
· 使用定理 `MeasureTheory.Measure.map_inv_eq_self`：map_inv_eq_self (μ : Measure G) [
IsInvInvariant μ] : map Inv.inv μ = μ
-/
theorem integral_inv_eq_self (f : G → E) (μ : Measure G) [IsInvInvariant μ] :
    ∫ x, f x⁻¹ ∂μ = ∫ x, f x ∂μ := by
  have h : MeasurableEmbedding fun x : G => x⁻¹ := (MeasurableEquiv.inv G).measurableEmbedding
  rw [← h.integral_map, map_inv_eq_self]

@[to_additive]
/-
**MeasureTheory.IntegrableOn.comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrableOn`。
形式化陈述：∀ {G : Type u_4} {F : Type u_6} [inst : MeasurableSpace G] [inst_1 : Norme
dAddCommGroup F] {μ : MeasureTheory.Measure G}   [inst_2 : Group G] [MeasurableI
nv G] [μ.IsInvInvariant] {f : G → F} {s : Set G},   MeasureTheory.IntegrableOn f
 s μ → MeasureTheory.IntegrableOn (fun x => f x⁻¹) s⁻¹ μ
参数：fun x => f x⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_map_equiv`：integrable_map_equiv (f : α ≃ᵐ δ) (g
 : δ -> ε) : Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableEquiv.inv_apply`：∀ (G : Type u_4) [inst : MeasurableSpace G] [
inst_1 : InvolutiveInv G] [inst_2 : MeasurableInv G],   ⇑(MeasurableEquiv.inv G)
 = Inv.inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEquiv.restrict_map`：∀ {α : Type u_2} {β : Type u_3} {m0 : Meas
urableSpace α} {m1 : MeasurableSpace β} (e : α ≃ᵐ β)   (μ : MeasureTheory.Measur
e α) (s : Set β), …
· 使用定理 `MeasureTheory.Measure.map_inv_eq_self`：map_inv_eq_self (μ : Measure G) [
IsInvInvariant μ] : map Inv.inv μ = μ
-/
theorem IntegrableOn.comp_inv [IsInvInvariant μ] {f : G → F} {s : Set G} (hf : IntegrableOn f s μ) :
    IntegrableOn (fun x => f x⁻¹) s⁻¹ μ := by
  apply (integrable_map_equiv (MeasurableEquiv.inv G) f).mp
  have : s⁻¹ = MeasurableEquiv.inv G ⁻¹' s := by simp
  rw [this, ← MeasurableEquiv.restrict_map]
  simpa using! hf

end MeasurableInv

section MeasurableInvOrder

variable [PartialOrder G] [CommGroup G] [IsOrderedMonoid G] [MeasurableInv G]
variable [IsInvInvariant μ]

@[to_additive]
/-
**MeasureTheory.IntegrableOn.comp_inv_Iic** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IntegrableOn`。
形式化陈述：∀ {G : Type u_4} {F : Type u_6} [inst : MeasurableSpace G] [inst_1 : Norme
dAddCommGroup F] {μ : MeasureTheory.Measure G}   [inst_2 : PartialOrder G] [inst
_3 : CommGroup G] [IsOrderedMonoid G] [MeasurableInv G] [μ.IsInvInvariant] {c : 
G}   {f : G → F}, MeasureTheory.IntegrableOn f (Set.Ici c⁻¹) μ → MeasureTheory.I
ntegrableOn (fun x => f x⁻¹) (Set.Iic c) μ
参数：Set.Ici c⁻¹；fun x => f x⁻¹；Set.Iic c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inv_Ici`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ici a)⁻¹ = Set.Iic a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `MeasureTheory.IntegrableOn.comp_inv`：∀ {G : Type u_4} {F : Type u_6} [in
st : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Measu
re G}   [inst_2 : Group G…
-/
theorem IntegrableOn.comp_inv_Iic {c : G} {f : G → F} (hf : IntegrableOn f (Set.Ici c⁻¹) μ) :
    IntegrableOn (fun x => f x⁻¹) (Set.Iic c) μ := by
  simpa using hf.comp_inv

@[to_additive]
/-
**MeasureTheory.IntegrableOn.comp_inv_Ici** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IntegrableOn`。
形式化陈述：∀ {G : Type u_4} {F : Type u_6} [inst : MeasurableSpace G] [inst_1 : Norme
dAddCommGroup F] {μ : MeasureTheory.Measure G}   [inst_2 : PartialOrder G] [inst
_3 : CommGroup G] [IsOrderedMonoid G] [MeasurableInv G] [μ.IsInvInvariant] {c : 
G}   {f : G → F}, MeasureTheory.IntegrableOn f (Set.Iic c⁻¹) μ → MeasureTheory.I
ntegrableOn (fun x => f x⁻¹) (Set.Ici c) μ
参数：Set.Iic c⁻¹；fun x => f x⁻¹；Set.Ici c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inv_Iic`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iic a)⁻¹ = Set.Ici a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `MeasureTheory.IntegrableOn.comp_inv`：∀ {G : Type u_4} {F : Type u_6} [in
st : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Measu
re G}   [inst_2 : Group G…
-/
theorem IntegrableOn.comp_inv_Ici {c : G} {f : G → F} (hf : IntegrableOn f (Set.Iic c⁻¹) μ) :
    IntegrableOn (fun x => f x⁻¹) (Set.Ici c) μ := by
  simpa using hf.comp_inv

@[to_additive]
/-
**MeasureTheory.IntegrableOn.comp_inv_Iio** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IntegrableOn`。
形式化陈述：∀ {G : Type u_4} {F : Type u_6} [inst : MeasurableSpace G] [inst_1 : Norme
dAddCommGroup F] {μ : MeasureTheory.Measure G}   [inst_2 : PartialOrder G] [inst
_3 : CommGroup G] [IsOrderedMonoid G] [MeasurableInv G] [μ.IsInvInvariant] {c : 
G}   {f : G → F}, MeasureTheory.IntegrableOn f (Set.Ioi c⁻¹) μ → MeasureTheory.I
ntegrableOn (fun x => f x⁻¹) (Set.Iio c) μ
参数：Set.Ioi c⁻¹；fun x => f x⁻¹；Set.Iio c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inv_Ioi`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Ioi a)⁻¹ = Set.Iio a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `MeasureTheory.IntegrableOn.comp_inv`：∀ {G : Type u_4} {F : Type u_6} [in
st : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Measu
re G}   [inst_2 : Group G…
-/
theorem IntegrableOn.comp_inv_Iio {c : G} {f : G → F} (hf : IntegrableOn f (Set.Ioi c⁻¹) μ) :
    IntegrableOn (fun x => f x⁻¹) (Set.Iio c) μ := by
  simpa using hf.comp_inv

@[to_additive]
/-
**MeasureTheory.IntegrableOn.comp_inv_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.IntegrableOn`。
形式化陈述：∀ {G : Type u_4} {F : Type u_6} [inst : MeasurableSpace G] [inst_1 : Norme
dAddCommGroup F] {μ : MeasureTheory.Measure G}   [inst_2 : PartialOrder G] [inst
_3 : CommGroup G] [IsOrderedMonoid G] [MeasurableInv G] [μ.IsInvInvariant] {c : 
G}   {f : G → F}, MeasureTheory.IntegrableOn f (Set.Iio c⁻¹) μ → MeasureTheory.I
ntegrableOn (fun x => f x⁻¹) (Set.Ioi c) μ
参数：Set.Iio c⁻¹；fun x => f x⁻¹；Set.Ioi c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inv_Iio`：∀ {α : Type u_1} [inst : CommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedMonoid α] (a : α), (Set.Iio a)⁻¹ = Set.Ioi a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `MeasureTheory.IntegrableOn.comp_inv`：∀ {G : Type u_4} {F : Type u_6} [in
st : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Measu
re G}   [inst_2 : Group G…
-/
theorem IntegrableOn.comp_inv_Ioi {c : G} {f : G → F} (hf : IntegrableOn f (Set.Iio c⁻¹) μ) :
    IntegrableOn (fun x => f x⁻¹) (Set.Ioi c) μ := by
  simpa using hf.comp_inv

end MeasurableInvOrder

section MeasurableMul

variable [Group G] [MeasurableMul G]

/-- Translating a function by left-multiplication does not change its integral with respect to a
left-invariant measure. -/
@[to_additive
      /-- Translating a function by left-addition does not change its integral with respect to a
      left-invariant measure. -/]
/-
**MeasureTheory.integral_mul_left_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G -> E) (g : G) : (∫
 x, f (g * x) ∂μ) = ∫ x, f x ∂μ
参数：f : G -> E；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.integral_map`：∀ {α : Type u_1} {G : Type u_5} [inst 
: NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}   {μ 
: MeasureTheory.Measur…
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
-/
theorem integral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G → E) (g : G) :
    (∫ x, f (g * x) ∂μ) = ∫ x, f x ∂μ := by
  have h_mul : MeasurableEmbedding fun x => g * x := (MeasurableEquiv.mulLeft g).measurableEmbedding
  rw [← h_mul.integral_map, map_mul_left_eq_self]

/-- Translating a function by right-multiplication does not change its integral with respect to a
right-invariant measure. -/
@[to_additive
      /-- Translating a function by right-addition does not change its integral with respect to a
      right-invariant measure. -/]
/-
**MeasureTheory.integral_mul_right_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integral_mul_right_eq_self [IsMulRightInvariant μ] (f : G -> E) (g : G) : 
(∫ x, f (x * g) ∂μ) = ∫ x, f x ∂μ
参数：f : G -> E；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.integral_map`：∀ {α : Type u_1} {G : Type u_5} [inst 
: NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}   {μ 
: MeasureTheory.Measur…
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
-/
theorem integral_mul_right_eq_self [IsMulRightInvariant μ] (f : G → E) (g : G) :
    (∫ x, f (x * g) ∂μ) = ∫ x, f x ∂μ := by
  have h_mul : MeasurableEmbedding fun x => x * g :=
    (MeasurableEquiv.mulRight g).measurableEmbedding
  rw [← h_mul.integral_map, map_mul_right_eq_self]

@[to_additive]
/-
**MeasureTheory.integral_div_right_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integral_div_right_eq_self [IsMulRightInvariant μ] (f : G -> E) (g : G) : 
(∫ x, f (x / g) ∂μ) = ∫ x, f x ∂μ
参数：f : G -> E；g : G。
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
· 使用定理 `MeasureTheory.integral_mul_right_eq_self`：integral_mul_right_eq_self [Is
MulRightInvariant μ] (f : G -> E) (g : G) : (∫ x, f (x * g) ∂μ) = ∫ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_div_right_eq_self [IsMulRightInvariant μ] (f : G → E) (g : G) :
    (∫ x, f (x / g) ∂μ) = ∫ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, integral_mul_right_eq_self f g⁻¹]

/-- If some left-translate of a function negates it, then the integral of the function with respect
to a left-invariant measure is 0. -/
@[to_additive
      /-- If some left-translate of a function negates it, then the integral of the function with
      respect to a left-invariant measure is 0. -/]
/-
**MeasureTheory.integral_eq_zero_of_mul_left_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：integral_eq_zero_of_mul_left_eq_neg [IsMulLeftInvariant μ] (hf' : forall x
, f (g * x) = -f x) : ∫ x, f x ∂μ = 0
参数：hf' : forall x, f (g * x) = -f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_mul_left_eq_self`：integral_mul_left_eq_self [IsMu
lLeftInvariant μ] (f : G -> E) (g : G) : (∫ x, f (g * x) ∂μ) = ∫ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq_zero_of_mul_left_eq_neg [IsMulLeftInvariant μ] (hf' : ∀ x, f (g * x) = -f x) :
    ∫ x, f x ∂μ = 0 := by
  have : IsAddTorsionFree E := .of_isTorsionFree ℝ E
  simp_rw [← self_eq_neg, ← integral_neg, ← hf', integral_mul_left_eq_self]

/-- If some right-translate of a function negates it, then the integral of the function with respect
to a right-invariant measure is 0. -/
@[to_additive
      /-- If some right-translate of a function negates it, then the integral of the function with
      respect to a right-invariant measure is 0. -/]
/-
**MeasureTheory.integral_eq_zero_of_mul_right_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：integral_eq_zero_of_mul_right_eq_neg [IsMulRightInvariant μ] (hf' : forall
 x, f (x * g) = -f x) : ∫ x, f x ∂μ = 0
参数：hf' : forall x, f (x * g) = -f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_mul_right_eq_self`：integral_mul_right_eq_self [Is
MulRightInvariant μ] (f : G -> E) (g : G) : (∫ x, f (x * g) ∂μ) = ∫ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq_zero_of_mul_right_eq_neg [IsMulRightInvariant μ] (hf' : ∀ x, f (x * g) = -f x) :
    ∫ x, f x ∂μ = 0 := by
  have : IsAddTorsionFree E := .of_isTorsionFree ℝ E
  simp_rw [← self_eq_neg, ← integral_neg, ← hf', integral_mul_right_eq_self]

@[to_additive]
/-
**MeasureTheory.Integrable.comp_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Integrable`。
形式化陈述：∀ {G : Type u_4} {F : Type u_6} [inst : MeasurableSpace G] [inst_1 : Norme
dAddCommGroup F] {μ : MeasureTheory.Measure G}   [inst_2 : Group G] [MeasurableM
ul G] {f : G → F} [μ.IsMulLeftInvariant],   MeasureTheory.Integrable f μ → ∀ (g 
: G), MeasureTheory.Integrable (fun t => f (g * t)) μ
参数：g : G；fun t => f (g * t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.comp_measurable`：∀ {α : Type u_1} {ε : Type u_5
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace
 ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
-/
theorem Integrable.comp_mul_left {f : G → F} [IsMulLeftInvariant μ] (hf : Integrable f μ) (g : G) :
    Integrable (fun t => f (g * t)) μ :=
  (hf.mono_measure (map_mul_left_eq_self μ g).le).comp_measurable <| measurable_const_mul g

@[to_additive]
/-
**MeasureTheory.Integrable.comp_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Integrable`。
形式化陈述：∀ {G : Type u_4} {F : Type u_6} [inst : MeasurableSpace G] [inst_1 : Norme
dAddCommGroup F] {μ : MeasureTheory.Measure G}   [inst_2 : Group G] [MeasurableM
ul G] {f : G → F} [μ.IsMulRightInvariant],   MeasureTheory.Integrable f μ → ∀ (g
 : G), MeasureTheory.Integrable (fun t => f (t * g)) μ
参数：g : G；fun t => f (t * g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.comp_measurable`：∀ {α : Type u_1} {ε : Type u_5
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace
 ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
-/
theorem Integrable.comp_mul_right {f : G → F} [IsMulRightInvariant μ] (hf : Integrable f μ)
    (g : G) : Integrable (fun t => f (t * g)) μ :=
  (hf.mono_measure (map_mul_right_eq_self μ g).le).comp_measurable <| measurable_mul_const g

@[to_additive]
/-
**MeasureTheory.Integrable.comp_div_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Integrable`。
形式化陈述：∀ {G : Type u_4} {F : Type u_6} [inst : MeasurableSpace G] [inst_1 : Norme
dAddCommGroup F] {μ : MeasureTheory.Measure G}   [inst_2 : Group G] [MeasurableM
ul G] {f : G → F} [μ.IsMulRightInvariant],   MeasureTheory.Integrable f μ → ∀ (g
 : G), MeasureTheory.Integrable (fun t => f (t / g)) μ
参数：g : G；fun t => f (t / g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MeasureTheory.Integrable.comp_mul_right`：∀ {G : Type u_4} {F : Type u_6}
 [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.M
easure G}   [inst_2 : Group G…
-/
theorem Integrable.comp_div_right {f : G → F} [IsMulRightInvariant μ] (hf : Integrable f μ)
    (g : G) : Integrable (fun t => f (t / g)) μ := by
  simp_rw [div_eq_mul_inv]
  exact hf.comp_mul_right g⁻¹

variable [MeasurableInv G]

@[to_additive]
/-
**MeasureTheory.Integrable.comp_div_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Integrable`。
形式化陈述：∀ {G : Type u_4} {F : Type u_6} [inst : MeasurableSpace G] [inst_1 : Norme
dAddCommGroup F] {μ : MeasureTheory.Measure G}   [inst_2 : Group G] [MeasurableM
ul G] [MeasurableInv G] {f : G → F} [μ.IsInvInvariant] [μ.IsMulLeftInvariant],  
 MeasureTheory.Integrable f μ → ∀ (g : G), MeasureTheory.Integrable (fun t => f 
(g / t)) μ
参数：g : G；fun t => f (g / t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp`：∀ {α : Type u_1} {δ : T
ype u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
[inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `MeasureTheory.Measure.measurePreserving_div_left`：measurePreserving_div_
left (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) : Measure
Preserving (fun t => g / t) μ μ
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.comp_div_left {f : G → F} [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (hf : Integrable f μ) (g : G) : Integrable (fun t => f (g / t)) μ :=
  ((measurePreserving_div_left μ g).integrable_comp hf.aestronglyMeasurable).mpr hf

@[to_additive]
/-
**MeasureTheory.integrable_comp_div_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrable_comp_div_left (f : G -> F) [IsInvInvariant μ] [IsMulLeftInvaria
nt μ] (g : G) : Integrable (fun t => f (g / t)) μ ↔ Integrable f μ
参数：f : G -> F；g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Integrable.comp_mul_left`：∀ {G : Type u_4} {F : Type u_6} 
[inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Me
asure G}   [inst_2 : Group G…
· 使用定理 `MeasureTheory.Integrable.comp_inv`：∀ {G : Type u_4} {F : Type u_6} [inst
 : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Measure
 G}   [inst_2 : Group G…
· 使用定理 `MeasureTheory.Integrable.comp_div_left`：∀ {G : Type u_4} {F : Type u_6} 
[inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Me
asure G}   [inst_2 : Group G…
-/
theorem integrable_comp_div_left (f : G → F) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) :
    Integrable (fun t => f (g / t)) μ ↔ Integrable f μ := by
  refine ⟨fun h => ?_, fun h => h.comp_div_left g⟩
  convert! h.comp_inv.comp_mul_left g⁻¹
  simp_rw [div_inv_eq_mul, mul_inv_cancel_left]

@[to_additive]
/-
**MeasureTheory.integral_div_left_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integral_div_left_eq_self (f : G -> E) (μ : Measure G) [IsInvInvariant μ] 
[IsMulLeftInvariant μ] (x' : G) : (∫ x, f (x' / x) ∂μ) = ∫ x, f x ∂μ
参数：f : G -> E；μ : Measure G；x' : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MeasureTheory.integral_inv_eq_self`：integral_inv_eq_self (f : G -> E) (μ
 : Measure G) [IsInvInvariant μ] : ∫ x, f x⁻¹ ∂μ = ∫ x, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_mul_left_eq_self`：integral_mul_left_eq_self [IsMu
lLeftInvariant μ] (f : G -> E) (g : G) : (∫ x, f (g * x) ∂μ) = ∫ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_div_left_eq_self (f : G → E) (μ : Measure G) [IsInvInvariant μ]
    [IsMulLeftInvariant μ] (x' : G) : (∫ x, f (x' / x) ∂μ) = ∫ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, integral_inv_eq_self (fun x => f (x' * x)) μ,
    integral_mul_left_eq_self f x']

end MeasurableMul

section SMul

variable {G : Type*} [Group G] [MeasurableSpace α] [MulAction G α] [MeasurableConstSMul G α]

@[to_additive]
/-
**MeasureTheory.integral_smul_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_smul_eq_self {μ : Measure α} [SMulInvariantMeasure G α μ] (f : α 
-> E) {g : G} : (∫ x, f (g • x) ∂μ) = ∫ x, f x ∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.integral_map`：∀ {α : Type u_1} {G : Type u_5} [inst 
: NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}   {μ 
: MeasureTheory.Measur…
· 使用定理 `MeasureTheory.map_smul`：∀ {M : Type v} {α : Type w} {m : MeasurableSpace
 α} [inst : SMul M α] [MeasurableConstSMul M α] (c : M)   (μ : MeasureTheory.Mea
sure α) [Mea…
-/
theorem integral_smul_eq_self {μ : Measure α} [SMulInvariantMeasure G α μ] (f : α → E) {g : G} :
    (∫ x, f (g • x) ∂μ) = ∫ x, f x ∂μ := by
  have h : MeasurableEmbedding fun x : α => g • x := (MeasurableEquiv.smul g).measurableEmbedding
  rw [← h.integral_map, MeasureTheory.map_smul]

end SMul

end MeasureTheory

