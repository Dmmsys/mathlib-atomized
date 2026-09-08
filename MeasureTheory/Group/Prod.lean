/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Group.Measure

/-!
# Measure theory in the product of groups

In this file we show properties about measure theory in products of measurable groups
and properties of iterated integrals in measurable groups.

These lemmas show the uniqueness of left invariant measures on measurable groups, up to
scaling. In this file we follow the proof and refer to the book *Measure Theory* by Paul Halmos.

The idea of the proof is to use the translation invariance of measures to prove `μ(t) = c * μ(s)`
for two sets `s` and `t`, where `c` is a constant that does not depend on `μ`. Let `e` and `f` be
the characteristic functions of `s` and `t`.
Assume that `μ` and `ν` are left-invariant measures. Then the map `(x, y) ↦ (y * x, x⁻¹)`
preserves the measure `μ × ν`, which means that
```
  ∫ x, ∫ y, h x y ∂ν ∂μ = ∫ x, ∫ y, h (y * x) x⁻¹ ∂ν ∂μ
```
If we apply this to `h x y := e x * f y⁻¹ / ν ((fun h ↦ h * y⁻¹) ⁻¹' s)`, we can rewrite the RHS to
`μ(t)`, and the LHS to `c * μ(s)`, where `c = c(ν)` does not depend on `μ`.
Applying this to `μ` and to `ν` gives `μ (t) / μ (s) = ν (t) / ν (s)`, which is the uniqueness up to
scalar multiplication.

The proof in [Halmos] seems to contain an omission in §60 Th. A, see
`MeasureTheory.measure_lintegral_div_measure`.

Note that this theory only applies in measurable groups, i.e., when multiplication and inversion
are measurable. This is not the case in general in locally compact groups, or even in compact
groups, when the topology is not second-countable. For arguments along the same line, but using
continuous functions instead of measurable sets and working in the general locally compact
setting, see the file `Mathlib/MeasureTheory/Measure/Haar/Unique.lean`.
-/

@[expose] public section


noncomputable section

open Set hiding prod_eq

open Function MeasureTheory

open Filter hiding map

open scoped ENNReal Pointwise MeasureTheory

variable (G : Type*) [MeasurableSpace G]
variable [Group G] [MeasurableMul₂ G]
variable (μ ν : Measure G) [SFinite ν] [SFinite μ] {s : Set G}

/-- The map `(x, y) ↦ (x, xy)` as a `MeasurableEquiv`. -/
@[to_additive /-- The map `(x, y) ↦ (x, x + y)` as a `MeasurableEquiv`. -/]
/-
**MeasurableEquiv.shearMulRight** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：(G : Type u_1) →   [inst : MeasurableSpace G] → [inst_1 : Group G] → [Meas
urableMul₂ G] → [MeasurableInv G] → G × G ≃ᵐ G × G
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The map `(x, y) ↦ (x, xy)` as a `MeasurableEquiv`.
-/
protected def MeasurableEquiv.shearMulRight [MeasurableInv G] : G × G ≃ᵐ G × G where
  toEquiv := .prodShear (.refl _) .mulLeft

/-- The map `(x, y) ↦ (x, y / x)` as a `MeasurableEquiv` with inverse `(x, y) ↦ (x, yx)` -/
@[to_additive
/-- The map `(x, y) ↦ (x, y - x)` as a `MeasurableEquiv` with inverse `(x, y) ↦ (x, y + x)`. -/]
/-
**MeasurableEquiv.shearDivRight** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：(G : Type u_1) →   [inst : MeasurableSpace G] → [inst_1 : Group G] → [Meas
urableMul₂ G] → [MeasurableInv G] → G × G ≃ᵐ G × G
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
protected def MeasurableEquiv.shearDivRight [MeasurableInv G] : G × G ≃ᵐ G × G where
  toEquiv := .prodShear (.refl _) .divRight

variable {G}

namespace MeasureTheory

open Measure

section LeftInvariant

/-- The multiplicative shear mapping `(x, y) ↦ (x, xy)` preserves the measure `μ × ν`.
This condition is part of the definition of a measurable group in [Halmos, §59].
There, the map in this lemma is called `S`. -/
@[to_additive measurePreserving_prod_add
/-- The shear mapping `(x, y) ↦ (x, x + y)` preserves the measure `μ × ν`. -/]
/-
**MeasureTheory.measurePreserving_prod_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measurePreserving_prod_mul [IsMulLeftInvariant ν] : MeasurePreserving (fun
 z : G × G => (z.1, z.1 * z.2)) (μ.prod ν) (μ.prod ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.skew_product`：skew_product [SFinite μa] 
[SFinite μc] {f : α -> β} (hf : MeasurePreserving f μa μb) {g : α -> γ -> δ} (hg
m : Measurable (uncurry g)) (hg : …
· 使用定理 `MeasureTheory.MeasurePreserving.id`：∀ {α : Type u_1} [inst : MeasurableS
pace α] (μ : MeasureTheory.Measure α), MeasureTheory.MeasurePreserving id μ μ
· 使用定理 `MeasurableMul₂.measurable_mul`：∀ {M : Type u_2} {inst : MeasurableSpace 
M} {inst_1 : Mul M} [self : MeasurableMul₂ M], Measurable fun p => p.1 * p.2
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
-/
theorem measurePreserving_prod_mul [IsMulLeftInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.1 * z.2)) (μ.prod ν) (μ.prod ν) :=
  (MeasurePreserving.id μ).skew_product measurable_mul <|
    Filter.Eventually.of_forall <| map_mul_left_eq_self ν

/-- The map `(x, y) ↦ (y, yx)` sends the measure `μ × ν` to `ν × μ`.
This is the map `SR` in [Halmos, §59].
`S` is the map `(x, y) ↦ (x, xy)` and `R` is `Prod.swap`. -/
@[to_additive measurePreserving_prod_add_swap
/-- The map `(x, y) ↦ (y, y + x)` sends the measure `μ × ν` to `ν × μ`. -/]
/-
**MeasureTheory.measurePreserving_prod_mul_swap** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measurePreserving_prod_mul_swap [IsMulLeftInvariant μ] : MeasurePreserving
 (fun z : G × G => (z.2, z.2 * z.1)) (μ.prod ν) (ν.prod μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_prod_mul`：measurePreserving_prod_mul [Is
MulLeftInvariant ν] : MeasurePreserving (fun z : G × G => (z.1, z.1 * z.2)) (μ.p
rod ν) (μ.prod ν)
· 使用定理 `MeasureTheory.Measure.measurePreserving_swap`：measurePreserving_swap : M
easurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
-/
theorem measurePreserving_prod_mul_swap [IsMulLeftInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.2, z.2 * z.1)) (μ.prod ν) (ν.prod μ) :=
  (measurePreserving_prod_mul ν μ).comp measurePreserving_swap

@[to_additive]
/-
**MeasureTheory.measurable_measure_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：measurable_measure_mul_right (hs : MeasurableSet s) : Measurable fun x => 
μ ((fun y => y * x) ⁻¹' s)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_measure_prodMk_right`：measurable_measure_prodMk_right {μ : Me
asure α} [SFinite μ] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun y
 => μ ((fun x => (x, …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasurableMul₂.measurable_mul`：∀ {M : Type u_2} {inst : MeasurableSpace 
M} {inst_1 : Mul M} [self : MeasurableMul₂ M], Measurable fun p => p.1 * p.2
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem measurable_measure_mul_right (hs : MeasurableSet s) :
    Measurable fun x => μ ((fun y => y * x) ⁻¹' s) := by
  suffices
    Measurable fun y =>
      μ ((fun x => (x, y)) ⁻¹' ((fun z : G × G => ((1 : G), z.1 * z.2)) ⁻¹' univ ×ˢ s))
    by convert! this using 1; ext1 x; congr 1 with y : 1; simp
  apply measurable_measure_prodMk_right
  apply measurable_const.prodMk measurable_mul (MeasurableSet.univ.prod hs)
  infer_instance

variable [MeasurableInv G]

/-- The map `(x, y) ↦ (x, x⁻¹y)` is measure-preserving.
This is the function `S⁻¹` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)`. -/
@[to_additive measurePreserving_prod_neg_add
/-- The map `(x, y) ↦ (x, - x + y)` is measure-preserving. -/]
/-
**MeasureTheory.measurePreserving_prod_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measurePreserving_prod_inv_mul [IsMulLeftInvariant ν] : MeasurePreserving 
(fun z : G × G => (z.1, z.1⁻¹ * z.2)) (μ.prod ν) (μ.prod ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.measurePreserving_prod_mul`：measurePreserving_prod_mul [Is
MulLeftInvariant ν] : MeasurePreserving (fun z : G × G => (z.1, z.1 * z.2)) (μ.p
rod ν) (μ.prod ν)
-/
theorem measurePreserving_prod_inv_mul [IsMulLeftInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.1⁻¹ * z.2)) (μ.prod ν) (μ.prod ν) :=
  (measurePreserving_prod_mul μ ν).symm <| MeasurableEquiv.shearMulRight G

variable [IsMulLeftInvariant μ]

/-- The map `(x, y) ↦ (y, y⁻¹x)` sends `μ × ν` to `ν × μ`.
This is the function `S⁻¹R` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)` and `R` is `Prod.swap`. -/
@[to_additive measurePreserving_prod_neg_add_swap
/-- The map `(x, y) ↦ (y, - y + x)` sends `μ × ν` to `ν × μ`. -/]
/-
**MeasureTheory.measurePreserving_prod_inv_mul_swap** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：measurePreserving_prod_inv_mul_swap : MeasurePreserving (fun z : G × G => 
(z.2, z.2⁻¹ * z.1)) (μ.prod ν) (ν.prod μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_prod_inv_mul`：measurePreserving_prod_inv
_mul [IsMulLeftInvariant ν] : MeasurePreserving (fun z : G × G => (z.1, z.1⁻¹ * 
z.2)) (μ.prod ν) (μ.prod ν)
· 使用定理 `MeasureTheory.Measure.measurePreserving_swap`：measurePreserving_swap : M
easurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
-/
theorem measurePreserving_prod_inv_mul_swap :
    MeasurePreserving (fun z : G × G => (z.2, z.2⁻¹ * z.1)) (μ.prod ν) (ν.prod μ) :=
  (measurePreserving_prod_inv_mul ν μ).comp measurePreserving_swap

/-- The map `(x, y) ↦ (yx, x⁻¹)` is measure-preserving.
This is the function `S⁻¹RSR` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)` and `R` is `Prod.swap`. -/
@[to_additive measurePreserving_add_prod_neg
/-- The map `(x, y) ↦ (y + x, - x)` is measure-preserving. -/]
/-
**MeasureTheory.measurePreserving_mul_prod_inv** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measurePreserving_mul_prod_inv [IsMulLeftInvariant ν] : MeasurePreserving 
(fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.prod ν) (μ.prod ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_prod_inv_mul_swap`：measurePreserving_pro
d_inv_mul_swap : MeasurePreserving (fun z : G × G => (z.2, z.2⁻¹ * z.1)) (μ.prod
 ν) (ν.prod μ)
· 使用定理 `MeasureTheory.measurePreserving_prod_mul_swap`：measurePreserving_prod_mu
l_swap [IsMulLeftInvariant μ] : MeasurePreserving (fun z : G × G => (z.2, z.2 * 
z.1)) (μ.prod ν) (ν.prod μ)
-/
theorem measurePreserving_mul_prod_inv [IsMulLeftInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.prod ν) (μ.prod ν) := by
  convert!
    (measurePreserving_prod_inv_mul_swap ν μ).comp (measurePreserving_prod_mul_swap μ ν) using 1
  ext1 ⟨x, y⟩
  simp_rw [Function.comp_apply, mul_inv_rev, inv_mul_cancel_right]

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.quasiMeasurePreserving_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：quasiMeasurePreserving_inv : QuasiMeasurePreserving (Inv.inv : G -> G) μ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Set.inv_preimage`：inv_preimage : Inv.inv ⁻¹' s = s⁻¹
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `Measurable.inv`：Measurable.inv (hf : Measurable f) : Measurable f⁻¹
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasurableSet.inv`：MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) 
: MeasurableSet s⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.prod_apply_symm`：prod_apply_symm {s : Set (α × β)}
 (hs : MeasurableSet s) : μ.prod ν s = ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_zero`：lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.measurePreserving_mul_prod_inv`：measurePreserving_mul_prod
_inv [IsMulLeftInvariant ν] : MeasurePreserving (fun z : G × G => (z.2 * z.1, z.
1⁻¹)) (μ.prod ν) (μ.prod ν)
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
-/
theorem quasiMeasurePreserving_inv : QuasiMeasurePreserving (Inv.inv : G → G) μ μ := by
  refine ⟨measurable_inv, AbsolutelyContinuous.mk fun s hsm hμs => ?_⟩
  rw [map_apply measurable_inv hsm, inv_preimage]
  have hf : Measurable fun z : G × G => (z.2 * z.1, z.1⁻¹) :=
    (measurable_snd.mul measurable_fst).prodMk measurable_fst.inv
  suffices map (fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.prod μ) (s⁻¹ ×ˢ s⁻¹) = 0 by
    simpa only [(measurePreserving_mul_prod_inv μ μ).map_eq, prod_prod, mul_eq_zero (M₀ := ℝ≥0∞),
      or_self_iff] using this
  have hsm' : MeasurableSet (s⁻¹ ×ˢ s⁻¹) := hsm.inv.prod hsm.inv
  simp_rw [map_apply hf hsm', prod_apply_symm (μ := μ) (ν := μ) (hf hsm'), preimage_preimage,
    mk_preimage_prod, inv_preimage, inv_inv, measure_mono_null inter_subset_right hμs,
    lintegral_zero]

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_inv_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_inv_null : μ s⁻¹ = 0 ↔ μ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null`：preimage_nul
l (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) : μa (f ⁻¹' s
) = 0
· 使用定理 `MeasureTheory.quasiMeasurePreserving_inv`：quasiMeasurePreserving_inv : Q
uasiMeasurePreserving (Inv.inv : G -> G) μ μ
-/
theorem measure_inv_null : μ s⁻¹ = 0 ↔ μ s = 0 := by
  refine ⟨fun hs => ?_, (quasiMeasurePreserving_inv μ).preimage_null⟩
  rw [← inv_inv s]
  exact (quasiMeasurePreserving_inv μ).preimage_null hs

@[to_additive (attr := simp)]
/-
**MeasureTheory.inv_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：inv_ae : (ae μ)⁻¹ = ae μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.tendsto_ae`：tendsto_ae (h :
 QuasiMeasurePreserving f μa μb) : Tendsto f (ae μa) (ae μb)
· 使用定理 `MeasureTheory.quasiMeasurePreserving_inv`：quasiMeasurePreserving_inv : Q
uasiMeasurePreserving (Inv.inv : G -> G) μ μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem inv_ae : (ae μ)⁻¹ = ae μ := by
  refine le_antisymm (quasiMeasurePreserving_inv μ).tendsto_ae ?_
  nth_rewrite 1 [← inv_inv (ae μ)]
  exact Filter.map_mono (quasiMeasurePreserving_inv μ).tendsto_ae

@[to_additive (attr := simp)]
/-
**MeasureTheory.eventuallyConst_inv_set_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：eventuallyConst_inv_set_ae : EventuallyConst (s⁻¹ : Set G) (ae μ) ↔ Eventu
allyConst s (ae μ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inv_preimage`：inv_preimage : Inv.inv ⁻¹' s = s⁻¹
· 使用定理 `Filter.eventuallyConst_preimage`：eventuallyConst_preimage {s : Set β} {f
 : α -> β} : EventuallyConst (f ⁻¹' s) l ↔ EventuallyConst s (map f l)
· 使用定理 `Filter.map_inv`：∀ {α : Type u_2} [inst : Inv α] {f : Filter α}, Filter.m
ap Inv.inv f = f⁻¹
· 使用定理 `MeasureTheory.inv_ae`：inv_ae : (ae μ)⁻¹ = ae μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventuallyConst_inv_set_ae :
    EventuallyConst (s⁻¹ : Set G) (ae μ) ↔ EventuallyConst s (ae μ) := by
  rw [← inv_preimage, eventuallyConst_preimage, Filter.map_inv, inv_ae]

@[to_additive]
/-
**MeasureTheory.inv_absolutelyContinuous** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：inv_absolutelyContinuous : μ.inv ≪ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.quasiMeasurePreserving_inv`：quasiMeasurePreserving_inv : Q
uasiMeasurePreserving (Inv.inv : G -> G) μ μ
-/
theorem inv_absolutelyContinuous : μ.inv ≪ μ :=
  (quasiMeasurePreserving_inv μ).absolutelyContinuous

@[to_additive]
/-
**MeasureTheory.absolutelyContinuous_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：absolutelyContinuous_inv : μ ≪ μ.inv
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.inv_apply`：inv_apply (μ : Measure G) (s : Set G) :
 μ.inv s = μ s⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem absolutelyContinuous_inv : μ ≪ μ.inv := by
  refine AbsolutelyContinuous.mk fun s _ => ?_
  simp_rw [inv_apply μ s, measure_inv_null, imp_self]

@[to_additive]
/-
**MeasureTheory.lintegral_lintegral_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：lintegral_lintegral_mul_inv [IsMulLeftInvariant ν] (f : G -> G -> Real>=0∞
) (hf : AEMeasurable (uncurry f) (μ.prod ν)) : (∫⁻ x, ∫⁻ y, f (y * x) x⁻¹ ∂ν ∂μ)
 = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ
参数：f : G -> G -> Real>=0∞；hf : AEMeasurable (uncurry f) (μ.prod ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `Measurable.inv`：Measurable.inv (hf : Measurable f) : Measurable f⁻¹
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_mul_prod_inv`：measurePreserving_mul_prod
_inv [IsMulLeftInvariant ν] : MeasurePreserving (fun z : G × G => (z.2 * z.1, z.
1⁻¹)) (μ.prod ν) (μ.prod ν)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_lintegral`：lintegral_lintegral ⦃f : α -> β -> Re
al>=0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) : ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫
⁻ z, f z.1 z.2 ∂μ.prod …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…
· 使用定理 `AEMeasurable.mono'`：∀ {α : Type u_2} {β : Type u_3} {m0 : MeasurableSpac
e α} [inst : MeasurableSpace β] {f : α → β}   {μ ν : MeasureTheory.Measure α}, A
EMeasura…
· 使用定理 `Eq.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν 
: MeasureTheory.Measure α}, μ = ν → μ.AbsolutelyContinuous ν
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem lintegral_lintegral_mul_inv [IsMulLeftInvariant ν] (f : G → G → ℝ≥0∞)
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    (∫⁻ x, ∫⁻ y, f (y * x) x⁻¹ ∂ν ∂μ) = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ := by
  have h : Measurable fun z : G × G => (z.2 * z.1, z.1⁻¹) :=
    (measurable_snd.mul measurable_fst).prodMk measurable_fst.inv
  have h2f : AEMeasurable (uncurry fun x y => f (y * x) x⁻¹) (μ.prod ν) :=
    hf.comp_quasiMeasurePreserving (measurePreserving_mul_prod_inv μ ν).quasiMeasurePreserving
  simp_rw [lintegral_lintegral h2f, lintegral_lintegral hf]
  conv_rhs => rw [← (measurePreserving_mul_prod_inv μ ν).map_eq]
  symm
  exact
    lintegral_map' (hf.mono' (measurePreserving_mul_prod_inv μ ν).map_eq.absolutelyContinuous)
      h.aemeasurable

@[to_additive]
/-
**MeasureTheory.measure_mul_right_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_mul_right_null (y : G) : μ ((fun x => x * y) ⁻¹' s) = 0 ↔ μ s = 0
参数：y : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.measure_inv_null`：measure_inv_null : μ s⁻¹ = 0 ↔ μ s = 0
· 使用定理 `MeasureTheory.measure_preimage_mul`：measure_preimage_mul (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) (A : Set G) : μ ((fun h => g * h) ⁻¹' A) = μ A
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
-/
theorem measure_mul_right_null (y : G) : μ ((fun x => x * y) ⁻¹' s) = 0 ↔ μ s = 0 :=
  calc
    μ ((fun x => x * y) ⁻¹' s) = 0 ↔ μ ((fun x => y⁻¹ * x) ⁻¹' s⁻¹)⁻¹ = 0 := by
      simp_rw [← inv_preimage, preimage_preimage, mul_inv_rev, inv_inv]
    _ ↔ μ s = 0 := by simp only [measure_inv_null μ, measure_preimage_mul]

@[to_additive]
/-
**MeasureTheory.measure_mul_right_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：measure_mul_right_ne_zero (h2s : μ s != 0) (y : G) : μ ((fun x => x * y) ⁻
¹' s) != 0
参数：h2s : μ s != 0；y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.measure_mul_right_null`：measure_mul_right_null (y : G) : μ
 ((fun x => x * y) ⁻¹' s) = 0 ↔ μ s = 0
-/
theorem measure_mul_right_ne_zero (h2s : μ s ≠ 0) (y : G) : μ ((fun x => x * y) ⁻¹' s) ≠ 0 :=
  (not_congr (measure_mul_right_null μ y)).mpr h2s

@[to_additive]
/-
**MeasureTheory.absolutelyContinuous_map_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：absolutelyContinuous_map_mul_right (g : G) : μ ≪ map (· * g) μ
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.measure_mul_right_null`：measure_mul_right_null (y : G) : μ
 ((fun x => x * y) ⁻¹' s) = 0 ↔ μ s = 0
-/
theorem absolutelyContinuous_map_mul_right (g : G) : μ ≪ map (· * g) μ := by
  refine AbsolutelyContinuous.mk fun s hs => ?_
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null]; exact id

@[to_additive]
/-
**MeasureTheory.absolutelyContinuous_map_div_left** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：absolutelyContinuous_map_div_left (g : G) : μ ≪ map (fun h => g / h) μ
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.map`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.M
easure α},   μ.AbsolutelyContinuous …
· 使用定理 `MeasureTheory.absolutelyContinuous_inv`：absolutelyContinuous_inv : μ ≪ μ
.inv
-/
theorem absolutelyContinuous_map_div_left (g : G) : μ ≪ map (fun h => g / h) μ := by
  simp_rw [div_eq_mul_inv]
  have := map_map (μ := μ) (measurable_const_mul g) measurable_inv
  simp only [Function.comp_def] at this
  rw [← this]
  conv_lhs => rw [← map_mul_left_eq_self μ g]
  exact (absolutelyContinuous_inv μ).map (measurable_const_mul g)

/-- This is the computation performed in the proof of [Halmos, §60 Th. A]. -/
@[to_additive /-- This is the computation performed in the proof of [Halmos, §60 Th. A]. -/]
/-
**MeasureTheory.measure_mul_lintegral_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_mul_lintegral_eq [IsMulLeftInvariant ν] (sm : MeasurableSet s) (f 
: G -> Real>=0∞) (hf : Measurable f) : (μ s * ∫⁻ y, f y ∂ν) = ∫⁻ x, ν ((fun z =>
 z * x) ⁻¹' s) * f x⁻¹ ∂μ
参数：sm : MeasurableSet s；f : G -> Real>=0∞；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_one`：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ =
 μ s
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_lintegral_mul`：lintegral_lintegral_mul {β} [Meas
urableSpace β] {ν : Measure β} {f : α -> Real>=0∞} {g : β -> Real>=0∞} (hf : AEM
easurable f μ) (hg : AEMeas…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.lintegral_lintegral_mul_inv`：lintegral_lintegral_mul_inv [
IsMulLeftInvariant ν] (f : G -> G -> Real>=0∞) (hf : AEMeasurable (uncurry f) (μ
.prod ν)) : (∫⁻ x, ∫⁻ y, f (y *…
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_comp_right`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_3}
 [inst : Zero M] {s : Set α} (f : β → α) {g : α → M} {x : β},   (f ⁻¹' s).indica
tor (g ∘ f) x …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_mul_const`：lintegral_mul_const (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This is the computation performed in the proof of [Halmos, §60 Th. A].
-/
theorem measure_mul_lintegral_eq [IsMulLeftInvariant ν] (sm : MeasurableSet s) (f : G → ℝ≥0∞)
    (hf : Measurable f) : (μ s * ∫⁻ y, f y ∂ν) = ∫⁻ x, ν ((fun z => z * x) ⁻¹' s) * f x⁻¹ ∂μ := by
  rw [← setLIntegral_one, ← lintegral_indicator sm,
    ← lintegral_lintegral_mul (measurable_const.indicator sm).aemeasurable hf.aemeasurable,
    ← lintegral_lintegral_mul_inv μ ν]
  swap
  · exact (((measurable_const.indicator sm).comp measurable_fst).mul
      (hf.comp measurable_snd)).aemeasurable
  have ms :
    ∀ x : G, Measurable fun y => ((fun z => z * x) ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) y :=
    fun x => measurable_const.indicator (measurable_mul_const _ sm)
  have : ∀ x y, s.indicator (fun _ : G => (1 : ℝ≥0∞)) (y * x) =
      ((fun z => z * x) ⁻¹' s).indicator (fun b : G => 1) y := by
    intro x y; symm; convert! indicator_comp_right (M := ℝ≥0∞) fun y => y * x using 2; ext1; rfl
  simp_rw [this, lintegral_mul_const _ (ms _), lintegral_indicator (measurable_mul_const _ sm),
    setLIntegral_one]

/-- Any two nonzero left-invariant measures are absolutely continuous w.r.t. each other. -/
@[to_additive
/-- Any two nonzero left-invariant measures are absolutely continuous w.r.t. each other. -/]
/-
**MeasureTheory.absolutelyContinuous_of_isMulLeftInvariant** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：absolutelyContinuous_of_isMulLeftInvariant [IsMulLeftInvariant ν] (hν : ν 
!= 0) : μ ≪ ν
参数：hν : ν != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `MeasureTheory.measure_mul_lintegral_eq`：measure_mul_lintegral_eq [IsMulL
eftInvariant ν] (sm : MeasurableSet s) (f : G -> Real>=0∞) (hf : Measurable f) :
 (μ s * ∫⁻ y, f y ∂ν) = ∫⁻ x…
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `MeasureTheory.lintegral_zero`：lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_mul_right_null`：measure_mul_right_null (y : G) : μ
 ((fun x => x * y) ⁻¹' s) = 0 ↔ μ s = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
-/
theorem absolutelyContinuous_of_isMulLeftInvariant [IsMulLeftInvariant ν] (hν : ν ≠ 0) : μ ≪ ν := by
  refine AbsolutelyContinuous.mk fun s sm hνs => ?_
  have h1 := measure_mul_lintegral_eq μ ν sm 1 measurable_one
  simp_rw [Pi.one_apply, lintegral_one, mul_one, (measure_mul_right_null ν _).mpr hνs,
    lintegral_zero, mul_eq_zero (M₀ := ℝ≥0∞), measure_univ_eq_zero.not.mpr hν, or_false] at h1
  exact h1

section SigmaFinite

variable (μ' ν' : Measure G) [SigmaFinite μ'] [SigmaFinite ν'] [IsMulLeftInvariant μ']
  [IsMulLeftInvariant ν']

@[to_additive]
/-
**MeasureTheory.ae_measure_preimage_mul_right_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：ae_measure_preimage_mul_right_lt_top (hμs : μ' s != ∞) : forallᵐ x ∂μ', ν'
 ((· * x) ⁻¹' s) < ∞
参数：hμs : μ' s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `MeasureTheory.ae_of_forall_measure_lt_top_ae_restrict'`：ae_of_forall_mea
sure_lt_top_ae_restrict' {μ : Measure α} (ν : Measure α) [SigmaFinite μ] [SigmaF
inite ν] (P : α -> Prop) (h : forall s, Meas…
· 使用定理 `MeasureTheory.Measure.inv.instSigmaFinite`：∀ {G : Type u_1} [inst : Meas
urableSpace G] [inst_1 : InvolutiveInv G] [MeasurableInv G] (μ : MeasureTheory.M
easure G)   [MeasureTheory.Sigm…
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `MeasureTheory.measurable_measure_mul_right`：measurable_measure_mul_right
 (hs : MeasurableSet s) : Measurable fun x => μ ((fun y => y * x) ⁻¹' s)
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.measure_mul_lintegral_eq`：measure_mul_lintegral_eq [IsMulL
eftInvariant ν] (sm : MeasurableSet s) (f : G -> Real>=0∞) (hf : Measurable f) :
 (μ s * ∫⁻ y, f y ∂ν) = ∫⁻ x…
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
· 使用定理 `MeasurableSet.inv`：MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) 
: MeasurableSet s⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Set.indicator_mul_right`：indicator_mul_right (s : Set ι) (f g : ι -> M₀)
 : indicator s (fun j => f j * g j) i = f i * indicator s g i
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.indicator_image`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_3} [ins
t : Zero M] {s : Set α} {f : β → M} {g : α → β},   Function.Injective g → ∀ {x :
 α}, (g '…
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.setLIntegral_one`：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ =
 μ s
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `MeasureTheory.Measure.inv_apply`：inv_apply (μ : Measure G) (s : Set G) :
 μ.inv s = μ s⁻¹
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Eq.trans_ne`：∀ {α : Sort u_1} {a b c : α}, a = b → b ≠ c → a ≠ c
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
（共 35 条，此处仅展示前 30 条）
-/
theorem ae_measure_preimage_mul_right_lt_top (hμs : μ' s ≠ ∞) :
    ∀ᵐ x ∂μ', ν' ((· * x) ⁻¹' s) < ∞ := by
  wlog sm : MeasurableSet s generalizing s
  · filter_upwards [this ((measure_toMeasurable _).trans_ne hμs) (measurableSet_toMeasurable ..)]
      with x hx using lt_of_le_of_lt (by gcongr; apply subset_toMeasurable) hx
  refine ae_of_forall_measure_lt_top_ae_restrict' ν'.inv _ ?_
  intro A hA _ h3A
  simp only [ν'.inv_apply] at h3A
  apply ae_lt_top (measurable_measure_mul_right ν' sm)
  have h1 := measure_mul_lintegral_eq μ' ν' sm (A⁻¹.indicator 1) (measurable_one.indicator hA.inv)
  rw [lintegral_indicator hA.inv] at h1
  simp_rw [Pi.one_apply, setLIntegral_one, ← image_inv_eq_inv, indicator_image inv_injective,
    image_inv_eq_inv, ← indicator_mul_right _ fun x => ν' ((· * x) ⁻¹' s), Function.comp,
    Pi.one_apply, mul_one] at h1
  rw [← lintegral_indicator hA, ← h1]
  finiteness

@[to_additive]
/-
**MeasureTheory.ae_measure_preimage_mul_right_lt_top_of_ne_zero** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_measure_preimage_mul_right_lt_top_of_ne_zero (h2s : ν' s != 0) (h3s : ν
' s != ∞) : forallᵐ x ∂μ', ν' ((fun y => y * x) ⁻¹' s) < ∞
参数：h2s : ν' s != 0；h3s : ν' s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `MeasureTheory.absolutelyContinuous_of_isMulLeftInvariant`：absolutelyCont
inuous_of_isMulLeftInvariant [IsMulLeftInvariant ν] (hν : ν != 0) : μ ≪ ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.coe_zero`：coe_zero {_m : MeasurableSpace α} : ⇑(0 
: Measure α) = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `MeasureTheory.ae_measure_preimage_mul_right_lt_top`：ae_measure_preimage_
mul_right_lt_top (hμs : μ' s != ∞) : forallᵐ x ∂μ', ν' ((· * x) ⁻¹' s) < ∞
-/
theorem ae_measure_preimage_mul_right_lt_top_of_ne_zero (h2s : ν' s ≠ 0) (h3s : ν' s ≠ ∞) :
    ∀ᵐ x ∂μ', ν' ((fun y => y * x) ⁻¹' s) < ∞ := by
  refine (ae_measure_preimage_mul_right_lt_top ν' ν' h3s).filter_mono ?_
  refine (absolutelyContinuous_of_isMulLeftInvariant μ' ν' ?_).ae_le
  refine mt ?_ h2s
  intro hν
  rw [hν, Measure.coe_zero, Pi.zero_apply]

/-- A technical lemma relating two different measures. This is basically [Halmos, §60 Th. A].
  Note that if `f` is the characteristic function of a measurable set `t` this states that
  `μ t = c * μ s` for a constant `c` that does not depend on `μ`.

  Note: There is a gap in the last step of the proof in [Halmos].
  In the last line, the equality `g(x⁻¹)ν(sx⁻¹) = f(x)` holds if we can prove that
  `0 < ν(sx⁻¹) < ∞`. The first inequality follows from §59, Th. D, but the second inequality is
  not justified. We prove this inequality for almost all `x` in
  `MeasureTheory.ae_measure_preimage_mul_right_lt_top_of_ne_zero`. -/
@[to_additive
/-- A technical lemma relating two different measures. This is basically [Halmos, §60 Th. A]. Note
that if `f` is the characteristic function of a measurable set `t` this states that `μ t = c * μ s`
for a constant `c` that does not depend on `μ`.

Note: There is a gap in the last step of the proof in [Halmos]. In the last line, the equality
`g(-x) + ν(s - x) = f(x)` holds if we can prove that `0 < ν(s - x) < ∞`. The first inequality
follows from §59, Th. D, but the second inequality is not justified. We prove this inequality for
almost all `x` in `MeasureTheory.ae_measure_preimage_add_right_lt_top_of_ne_zero`. -/]
/-
**MeasureTheory.measure_lintegral_div_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measure_lintegral_div_measure (sm : MeasurableSet s) (h2s : ν' s != 0) (h3
s : ν' s != ∞) (f : G -> Real>=0∞) (hf : Measurable f) : (μ' s * ∫⁻ y, f y⁻¹ / ν
' ((· * y⁻¹) ⁻¹' s) ∂ν') = ∫⁻ x, f x ∂μ'
参数：sm : MeasurableSet s；h2s : ν' s != 0；h3s : ν' s != ∞；f : G -> Real>=0∞；hf : M
easurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Measurable.div`：Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (h
g : Measurable g) : Measurable (f / g)
· 使用定理 `measurableDiv₂_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [
inst_1 : DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G],   MeasurableDiv₂ 
G
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
· 使用定理 `MeasureTheory.measurable_measure_mul_right`：measurable_measure_mul_right
 (hs : MeasurableSet s) : Measurable fun x => μ ((fun y => y * x) ⁻¹' s)
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measure_mul_lintegral_eq`：measure_mul_lintegral_eq [IsMulL
eftInvariant ν] (sm : MeasurableSet s) (f : G -> Real>=0∞) (hf : Measurable f) :
 (μ s * ∫⁻ y, f y ∂ν) = ∫⁻ x…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_measure_preimage_mul_right_lt_top_of_ne_zero`：ae_measur
e_preimage_mul_right_lt_top_of_ne_zero (h2s : ν' s != 0) (h3s : ν' s != ∞) : for
allᵐ x ∂μ', ν' ((fun y => y * x) ⁻¹' s) < ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.mul_div_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (b / a) =
 b
· 使用定理 `MeasureTheory.measure_mul_right_ne_zero`：measure_mul_right_ne_zero (h2s 
: μ s != 0) (y : G) : μ ((fun x => x * y) ⁻¹' s) != 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measure_lintegral_div_measure (sm : MeasurableSet s) (h2s : ν' s ≠ 0) (h3s : ν' s ≠ ∞)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (μ' s * ∫⁻ y, f y⁻¹ / ν' ((· * y⁻¹) ⁻¹' s) ∂ν') = ∫⁻ x, f x ∂μ' := by
  set g := fun y => f y⁻¹ / ν' ((fun x => x * y⁻¹) ⁻¹' s)
  have hg : Measurable g :=
    (hf.comp measurable_inv).div ((measurable_measure_mul_right ν' sm).comp measurable_inv)
  simp_rw [measure_mul_lintegral_eq μ' ν' sm g hg, g, inv_inv]
  refine lintegral_congr_ae ?_
  refine (ae_measure_preimage_mul_right_lt_top_of_ne_zero μ' ν' h2s h3s).mono fun x hx => ?_
  simp_rw [ENNReal.mul_div_cancel (measure_mul_right_ne_zero ν' h2s _) hx.ne]

@[to_additive]
/-
**MeasureTheory.measure_mul_measure_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_mul_measure_eq (s t : Set G) (h2s : ν' s != 0) (h3s : ν' s != ∞) :
 μ' s * ν' t = ν' s * μ' t
参数：s t : Set G；h2s : ν' s != 0；h3s : ν' s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `MeasureTheory.measure_lintegral_div_measure`：measure_lintegral_div_measu
re (sm : MeasurableSet s) (h2s : ν' s != 0) (h3s : ν' s != ∞) (f : G -> Real>=0∞
) (hf : Measurable f) : (μ' s * ∫…
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_one`：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ =
 μ s
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `MeasureTheory.exists_measurable_superset₂`：exists_measurable_superset₂ (
μ ν : Measure α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 
μ s ∧ ν t = ν s
-/
theorem measure_mul_measure_eq (s t : Set G) (h2s : ν' s ≠ 0) (h3s : ν' s ≠ ∞) :
    μ' s * ν' t = ν' s * μ' t := by
  wlog hs : MeasurableSet s generalizing s
  · rcases exists_measurable_superset₂ μ' ν' s with ⟨s', -, hm, hμ, hν⟩
    rw [← hμ, ← hν, this s' _ _ hm] <;> rwa [hν]
  wlog ht : MeasurableSet t generalizing t
  · rcases exists_measurable_superset₂ μ' ν' t with ⟨t', -, hm, hμ, hν⟩
    rw [← hμ, ← hν, this _ hm]
  have h1 := measure_lintegral_div_measure ν' ν' hs h2s h3s (t.indicator fun _ => 1)
    (measurable_const.indicator ht)
  have h2 := measure_lintegral_div_measure μ' ν' hs h2s h3s (t.indicator fun _ => 1)
    (measurable_const.indicator ht)
  rw [lintegral_indicator ht, setLIntegral_one] at h1 h2
  rw [← h1, mul_left_comm, h2]

/-- Left invariant Borel measures on a measurable group are unique (up to a scalar). -/
@[to_additive
/-- Left invariant Borel measures on an additive measurable group are unique (up to a scalar). -/]
/-
**MeasureTheory.measure_eq_div_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_div_smul (h2s : ν' s != 0) (h3s : ν' s != ∞) : μ' = (μ' s / ν' 
s) • ν'
参数：h2s : ν' s != 0；h3s : ν' s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `MeasureTheory.measure_mul_measure_eq`：measure_mul_measure_eq (s t : Set 
G) (h2s : ν' s != 0) (h3s : ν' s != ∞) : μ' s * ν' t = ν' s * μ' t
· 使用定理 `ENNReal.mul_div_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (b / a) =
 b
-/
theorem measure_eq_div_smul (h2s : ν' s ≠ 0) (h3s : ν' s ≠ ∞) :
    μ' = (μ' s / ν' s) • ν' := by
  ext1 t -
  rw [Measure.smul_apply, smul_eq_mul, mul_comm, ← mul_div_assoc, mul_comm,
    measure_mul_measure_eq μ' ν' s t h2s h3s, mul_div_assoc, ENNReal.mul_div_cancel h2s h3s]

end SigmaFinite

end LeftInvariant

section RightInvariant

@[to_additive measurePreserving_prod_add_right]
/-
**MeasureTheory.measurePreserving_prod_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：measurePreserving_prod_mul_right [IsMulRightInvariant ν] : MeasurePreservi
ng (fun z : G × G => (z.1, z.2 * z.1)) (μ.prod ν) (μ.prod ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.skew_product`：skew_product [SFinite μa] 
[SFinite μc] {f : α -> β} (hf : MeasurePreserving f μa μb) {g : α -> γ -> δ} (hg
m : Measurable (uncurry g)) (hg : …
· 使用定理 `MeasureTheory.MeasurePreserving.id`：∀ {α : Type u_1} [inst : MeasurableS
pace α] (μ : MeasureTheory.Measure α), MeasureTheory.MeasurePreserving id μ μ
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
-/
theorem measurePreserving_prod_mul_right [IsMulRightInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.2 * z.1)) (μ.prod ν) (μ.prod ν) :=
  MeasurePreserving.skew_product (g := fun x y => y * x) (MeasurePreserving.id μ)
    (measurable_snd.mul measurable_fst) <| Filter.Eventually.of_forall <| map_mul_right_eq_self ν

/-- The map `(x, y) ↦ (y, xy)` sends the measure `μ × ν` to `ν × μ`. -/
@[to_additive measurePreserving_prod_add_swap_right
/-- The map `(x, y) ↦ (y, x + y)` sends the measure `μ × ν` to `ν × μ`. -/]
/-
**MeasureTheory.measurePreserving_prod_mul_swap_right** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：measurePreserving_prod_mul_swap_right [IsMulRightInvariant μ] : MeasurePre
serving (fun z : G × G => (z.2, z.1 * z.2)) (μ.prod ν) (ν.prod μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_prod_mul_right`：measurePreserving_prod_m
ul_right [IsMulRightInvariant ν] : MeasurePreserving (fun z : G × G => (z.1, z.2
 * z.1)) (μ.prod ν) (μ.prod ν)
· 使用定理 `MeasureTheory.Measure.measurePreserving_swap`：measurePreserving_swap : M
easurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
-/
theorem measurePreserving_prod_mul_swap_right [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.2, z.1 * z.2)) (μ.prod ν) (ν.prod μ) :=
  (measurePreserving_prod_mul_right ν μ).comp measurePreserving_swap

/-- The map `(x, y) ↦ (xy, y)` preserves the measure `μ × ν`. -/
@[to_additive measurePreserving_add_prod
/-- The map `(x, y) ↦ (x + y, y)` preserves the measure `μ × ν`. -/]
/-
**MeasureTheory.measurePreserving_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measurePreserving_mul_prod [IsMulRightInvariant μ] : MeasurePreserving (fu
n z : G × G => (z.1 * z.2, z.2)) (μ.prod ν) (μ.prod ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.Measure.measurePreserving_swap`：measurePreserving_swap : M
easurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
· 使用定理 `MeasureTheory.measurePreserving_prod_mul_swap_right`：measurePreserving_p
rod_mul_swap_right [IsMulRightInvariant μ] : MeasurePreserving (fun z : G × G =>
 (z.2, z.1 * z.2)) (μ.prod ν) (ν.prod μ)
-/
theorem measurePreserving_mul_prod [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.1 * z.2, z.2)) (μ.prod ν) (μ.prod ν) :=
  measurePreserving_swap.comp (measurePreserving_prod_mul_swap_right μ ν)

variable [MeasurableInv G]

/-- The map `(x, y) ↦ (x, y / x)` is measure-preserving. -/
@[to_additive measurePreserving_prod_sub
/-- The map `(x, y) ↦ (x, y - x)` is measure-preserving. -/]
/-
**MeasureTheory.measurePreserving_prod_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measurePreserving_prod_div [IsMulRightInvariant ν] : MeasurePreserving (fu
n z : G × G => (z.1, z.2 / z.1)) (μ.prod ν) (μ.prod ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.measurePreserving_prod_mul_right`：measurePreserving_prod_m
ul_right [IsMulRightInvariant ν] : MeasurePreserving (fun z : G × G => (z.1, z.2
 * z.1)) (μ.prod ν) (μ.prod ν)
-/
theorem measurePreserving_prod_div [IsMulRightInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.2 / z.1)) (μ.prod ν) (μ.prod ν) :=
  (measurePreserving_prod_mul_right μ ν).symm (MeasurableEquiv.shearDivRight G).symm

/-- The map `(x, y) ↦ (y, x / y)` sends `μ × ν` to `ν × μ`. -/
@[to_additive measurePreserving_prod_sub_swap
/-- The map `(x, y) ↦ (y, x - y)` sends `μ × ν` to `ν × μ`. -/]
/-
**MeasureTheory.measurePreserving_prod_div_swap** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measurePreserving_prod_div_swap [IsMulRightInvariant μ] : MeasurePreservin
g (fun z : G × G => (z.2, z.1 / z.2)) (μ.prod ν) (ν.prod μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_prod_div`：measurePreserving_prod_div [Is
MulRightInvariant ν] : MeasurePreserving (fun z : G × G => (z.1, z.2 / z.1)) (μ.
prod ν) (μ.prod ν)
· 使用定理 `MeasureTheory.Measure.measurePreserving_swap`：measurePreserving_swap : M
easurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
-/
theorem measurePreserving_prod_div_swap [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.2, z.1 / z.2)) (μ.prod ν) (ν.prod μ) :=
  (measurePreserving_prod_div ν μ).comp measurePreserving_swap

/-- The map `(x, y) ↦ (x / y, y)` preserves the measure `μ × ν`. -/
@[to_additive measurePreserving_sub_prod
/-- The map `(x, y) ↦ (x - y, y)` preserves the measure `μ × ν`. -/]
/-
**MeasureTheory.measurePreserving_div_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measurePreserving_div_prod [IsMulRightInvariant μ] : MeasurePreserving (fu
n z : G × G => (z.1 / z.2, z.2)) (μ.prod ν) (μ.prod ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.Measure.measurePreserving_swap`：measurePreserving_swap : M
easurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
· 使用定理 `MeasureTheory.measurePreserving_prod_div_swap`：measurePreserving_prod_di
v_swap [IsMulRightInvariant μ] : MeasurePreserving (fun z : G × G => (z.2, z.1 /
 z.2)) (μ.prod ν) (ν.prod μ)
-/
theorem measurePreserving_div_prod [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.1 / z.2, z.2)) (μ.prod ν) (μ.prod ν) :=
  measurePreserving_swap.comp (measurePreserving_prod_div_swap μ ν)

/-- The map `(x, y) ↦ (xy, x⁻¹)` is measure-preserving. -/
@[to_additive measurePreserving_add_prod_neg_right
/-- The map `(x, y) ↦ (x + y, - x)` is measure-preserving. -/]
/-
**MeasureTheory.measurePreserving_mul_prod_inv_right** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：measurePreserving_mul_prod_inv_right [IsMulRightInvariant μ] [IsMulRightIn
variant ν] : MeasurePreserving (fun z : G × G => (z.1 * z.2, z.1⁻¹)) (μ.prod ν) 
(μ.prod ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_eq_div_div_swap`：div_mul_eq_div_div_swap : a / (b * c) = a / c /
 b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_prod_div_swap`：measurePreserving_prod_di
v_swap [IsMulRightInvariant μ] : MeasurePreserving (fun z : G × G => (z.2, z.1 /
 z.2)) (μ.prod ν) (ν.prod μ)
· 使用定理 `MeasureTheory.measurePreserving_prod_mul_swap_right`：measurePreserving_p
rod_mul_swap_right [IsMulRightInvariant μ] : MeasurePreserving (fun z : G × G =>
 (z.2, z.1 * z.2)) (μ.prod ν) (ν.prod μ)
-/
theorem measurePreserving_mul_prod_inv_right [IsMulRightInvariant μ] [IsMulRightInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1 * z.2, z.1⁻¹)) (μ.prod ν) (μ.prod ν) := by
  convert!
    (measurePreserving_prod_div_swap ν μ).comp (measurePreserving_prod_mul_swap_right μ ν) using 1
  ext1 ⟨x, y⟩
  simp_rw [Function.comp_apply, div_mul_eq_div_div_swap, div_self', one_div]

end RightInvariant

section QuasiMeasurePreserving

/-- The map `(x, y) ↦ x * y` is quasi-measure-preserving. -/
@[to_additive (attr := fun_prop) /-- The map `(x, y) ↦ x + y` is quasi-measure-preserving. -/]
/-
**MeasureTheory.quasiMeasurePreserving_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：quasiMeasurePreserving_mul [IsMulLeftInvariant ν] : QuasiMeasurePreserving
 (fun p => p.1 * p.2) (μ.prod ν) ν
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_prod_mul`：measurePreserving_prod_mul [Is
MulLeftInvariant ν] : MeasurePreserving (fun z : G × G => (z.1, z.1 * z.2)) (μ.p
rod ν) (μ.prod ν)

--- 原说明 ---
The map `(x, y) ↦ x * y` is quasi-measure-preserving.
-/
theorem quasiMeasurePreserving_mul [IsMulLeftInvariant ν] :
    QuasiMeasurePreserving (fun p ↦ p.1 * p.2) (μ.prod ν) ν :=
  quasiMeasurePreserving_snd.comp (measurePreserving_prod_mul _ _).quasiMeasurePreserving

/-- The map `(x, y) ↦ y * x` is quasi-measure-preserving. -/
@[to_additive (attr := fun_prop) /-- The map `(x, y) ↦ y + x` is quasi-measure-preserving. -/]
/-
**MeasureTheory.quasiMeasurePreserving_mul_swap** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：quasiMeasurePreserving_mul_swap [IsMulLeftInvariant μ] : QuasiMeasurePrese
rving (fun p => p.2 * p.1) (μ.prod ν) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_prod_mul_swap`：measurePreserving_prod_mu
l_swap [IsMulLeftInvariant μ] : MeasurePreserving (fun z : G × G => (z.2, z.2 * 
z.1)) (μ.prod ν) (ν.prod μ)

--- 原说明 ---
The map `(x, y) ↦ y * x` is quasi-measure-preserving.
-/
theorem quasiMeasurePreserving_mul_swap [IsMulLeftInvariant μ] :
    QuasiMeasurePreserving (fun p ↦ p.2 * p.1) (μ.prod ν) μ :=
  quasiMeasurePreserving_snd.comp (measurePreserving_prod_mul_swap _ _).quasiMeasurePreserving

section MeasurableInv

variable [MeasurableInv G]

/-- The map `(x, y) ↦ x⁻¹ * y` is quasi-measure-preserving. -/
@[to_additive (attr := fun_prop) /-- The map `(x, y) ↦ -x + y` is quasi-measure-preserving. -/]
/-
**MeasureTheory.quasiMeasurePreserving_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：quasiMeasurePreserving_inv_mul [IsMulLeftInvariant ν] : QuasiMeasurePreser
ving (fun p => p.1⁻¹ * p.2) (μ.prod ν) ν
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_prod_inv_mul`：measurePreserving_prod_inv
_mul [IsMulLeftInvariant ν] : MeasurePreserving (fun z : G × G => (z.1, z.1⁻¹ * 
z.2)) (μ.prod ν) (μ.prod ν)

--- 原说明 ---
The map `(x, y) ↦ x⁻¹ * y` is quasi-measure-preserving.
-/
theorem quasiMeasurePreserving_inv_mul [IsMulLeftInvariant ν] :
    QuasiMeasurePreserving (fun p ↦ p.1⁻¹ * p.2) (μ.prod ν) ν :=
  quasiMeasurePreserving_snd.comp (measurePreserving_prod_inv_mul _ _).quasiMeasurePreserving

/-- The map `(x, y) ↦ y⁻¹ * x` is quasi-measure-preserving. -/
@[to_additive (attr := fun_prop) /-- The map `(x, y) ↦ -y + x` is quasi-measure-preserving. -/]
/-
**MeasureTheory.quasiMeasurePreserving_inv_mul_swap** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：quasiMeasurePreserving_inv_mul_swap [IsMulLeftInvariant μ] : QuasiMeasureP
reserving (fun p => p.2⁻¹ * p.1) (μ.prod ν) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_prod_inv_mul_swap`：measurePreserving_pro
d_inv_mul_swap : MeasurePreserving (fun z : G × G => (z.2, z.2⁻¹ * z.1)) (μ.prod
 ν) (ν.prod μ)

--- 原说明 ---
The map `(x, y) ↦ y⁻¹ * x` is quasi-measure-preserving.
-/
theorem quasiMeasurePreserving_inv_mul_swap [IsMulLeftInvariant μ] :
    QuasiMeasurePreserving (fun p ↦ p.2⁻¹ * p.1) (μ.prod ν) μ :=
  quasiMeasurePreserving_snd.comp (measurePreserving_prod_inv_mul_swap _ _).quasiMeasurePreserving

@[to_additive (attr := fun_prop)]
/-
**MeasureTheory.quasiMeasurePreserving_inv_of_right_invariant** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：quasiMeasurePreserving_inv_of_right_invariant [IsMulRightInvariant μ] : Qu
asiMeasurePreserving (Inv.inv : G -> G) μ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.inv_inv`：∀ {G : Type u_1} [inst : MeasurableSpace 
G] [inst_1 : InvolutiveInv G] [MeasurableInv G] (μ : MeasureTheory.Measure G),  
 μ.inv.inv = μ
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.mono`：mono (ha : μa' ≪ μa) 
(hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving f 
μa' μb'
· 使用定理 `MeasureTheory.inv_absolutelyContinuous`：inv_absolutelyContinuous : μ.inv
 ≪ μ
· 使用定理 `MeasureTheory.Measure.inv.instSFinite`：∀ {G : Type u_1} [inst : Measurab
leSpace G] [inst_1 : Inv G] (μ : MeasureTheory.Measure G) [MeasureTheory.SFinite
 μ],   MeasureTheory.SFinit…
· 使用定理 `MeasureTheory.Measure.inv.instIsMulLeftInvariant`：∀ {G : Type u_1} [inst
 : MeasurableSpace G] [inst_1 : DivisionMonoid G] [MeasurableMul G] [MeasurableI
nv G]   {μ : MeasureTheory.Measure G} …
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.absolutelyContinuous_inv`：absolutelyContinuous_inv : μ ≪ μ
.inv
· 使用定理 `MeasureTheory.quasiMeasurePreserving_inv`：quasiMeasurePreserving_inv : Q
uasiMeasurePreserving (Inv.inv : G -> G) μ μ
-/
theorem quasiMeasurePreserving_inv_of_right_invariant [IsMulRightInvariant μ] :
    QuasiMeasurePreserving (Inv.inv : G → G) μ μ := by
  rw [← μ.inv_inv]
  exact
    (quasiMeasurePreserving_inv μ.inv).mono (inv_absolutelyContinuous μ.inv)
      (absolutelyContinuous_inv μ.inv)

@[to_additive]
/-
**MeasureTheory.quasiMeasurePreserving_div_left** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：quasiMeasurePreserving_div_left [IsMulLeftInvariant μ] (g : G) : QuasiMeas
urePreserving (fun h : G => g / h) μ μ
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_mul_left`：measurePreserving_mul_left (μ 
: Measure G) [IsMulLeftInvariant μ] (g : G) : MeasurePreserving (g * ·) μ μ
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.quasiMeasurePreserving_inv`：quasiMeasurePreserving_inv : Q
uasiMeasurePreserving (Inv.inv : G -> G) μ μ
-/
theorem quasiMeasurePreserving_div_left [IsMulLeftInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => g / h) μ μ := by
  simp_rw [div_eq_mul_inv]
  exact
    (measurePreserving_mul_left μ g).quasiMeasurePreserving.comp (quasiMeasurePreserving_inv μ)

@[to_additive]
/-
**MeasureTheory.quasiMeasurePreserving_div_left_of_right_invariant** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：quasiMeasurePreserving_div_left_of_right_invariant [IsMulRightInvariant μ]
 (g : G) : QuasiMeasurePreserving (fun h : G => g / h) μ μ
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.inv_inv`：∀ {G : Type u_1} [inst : MeasurableSpace 
G] [inst_1 : InvolutiveInv G] [MeasurableInv G] (μ : MeasureTheory.Measure G),  
 μ.inv.inv = μ
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.mono`：mono (ha : μa' ≪ μa) 
(hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving f 
μa' μb'
· 使用定理 `MeasureTheory.inv_absolutelyContinuous`：inv_absolutelyContinuous : μ.inv
 ≪ μ
· 使用定理 `MeasureTheory.Measure.inv.instSFinite`：∀ {G : Type u_1} [inst : Measurab
leSpace G] [inst_1 : Inv G] (μ : MeasureTheory.Measure G) [MeasureTheory.SFinite
 μ],   MeasureTheory.SFinit…
· 使用定理 `MeasureTheory.Measure.inv.instIsMulLeftInvariant`：∀ {G : Type u_1} [inst
 : MeasurableSpace G] [inst_1 : DivisionMonoid G] [MeasurableMul G] [MeasurableI
nv G]   {μ : MeasureTheory.Measure G} …
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.absolutelyContinuous_inv`：absolutelyContinuous_inv : μ ≪ μ
.inv
· 使用定理 `MeasureTheory.quasiMeasurePreserving_div_left`：quasiMeasurePreserving_di
v_left [IsMulLeftInvariant μ] (g : G) : QuasiMeasurePreserving (fun h : G => g /
 h) μ μ
-/
theorem quasiMeasurePreserving_div_left_of_right_invariant [IsMulRightInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => g / h) μ μ := by
  rw [← μ.inv_inv]
  exact
    (quasiMeasurePreserving_div_left μ.inv g).mono (inv_absolutelyContinuous μ.inv)
      (absolutelyContinuous_inv μ.inv)

@[to_additive]
/-
**MeasureTheory.quasiMeasurePreserving_div_of_right_invariant** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：quasiMeasurePreserving_div_of_right_invariant [IsMulRightInvariant μ] : Qu
asiMeasurePreserving (fun p : G × G => p.1 / p.2) (μ.prod ν) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.QuasiMeasurePreserving.prod_of_left`：prod_of_left {α β γ} 
[MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α × β -> γ} {μ 
: Measure α} {ν : Measure β} {τ : Measu…
· 使用定理 `MeasurableDiv₂.measurable_div`：∀ {G₀ : Type u_2} {inst : MeasurableSpace
 G₀} {inst_1 : Div G₀} [self : MeasurableDiv₂ G₀],   Measurable fun p => p.1 / p
.2
· 使用定理 `measurableDiv₂_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [
inst_1 : DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G],   MeasurableDiv₂ 
G
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_div_right`：measurePreserving_div_right (
μ : Measure G) [IsMulRightInvariant μ] (g : G) : MeasurePreserving (· / g) μ μ
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
-/
theorem quasiMeasurePreserving_div_of_right_invariant [IsMulRightInvariant μ] :
    QuasiMeasurePreserving (fun p : G × G => p.1 / p.2) (μ.prod ν) μ := by
  refine QuasiMeasurePreserving.prod_of_left measurable_div (Eventually.of_forall fun y => ?_)
  exact (measurePreserving_div_right μ y).quasiMeasurePreserving

@[to_additive]
/-
**MeasureTheory.quasiMeasurePreserving_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：quasiMeasurePreserving_div [IsMulLeftInvariant μ] : QuasiMeasurePreserving
 (fun p : G × G => p.1 / p.2) (μ.prod ν) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.mono`：mono (ha : μa' ≪ μa) 
(hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving f 
μa' μb'
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.prod`：∀ {α : Type u_1} {β : T
ype u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ μ' : Measure
Theory.Measure α}   {ν ν' : MeasureTh…
· 使用定理 `MeasureTheory.absolutelyContinuous_inv`：absolutelyContinuous_inv : μ ≪ μ
.inv
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `MeasureTheory.inv_absolutelyContinuous`：inv_absolutelyContinuous : μ.inv
 ≪ μ
· 使用定理 `MeasureTheory.quasiMeasurePreserving_div_of_right_invariant`：quasiMeasur
ePreserving_div_of_right_invariant [IsMulRightInvariant μ] : QuasiMeasurePreserv
ing (fun p : G × G => p.1 / p.2) (μ.prod ν) μ
· 使用定理 `MeasureTheory.Measure.inv.instSFinite`：∀ {G : Type u_1} [inst : Measurab
leSpace G] [inst_1 : Inv G] (μ : MeasureTheory.Measure G) [MeasureTheory.SFinite
 μ],   MeasureTheory.SFinit…
· 使用定理 `MeasureTheory.Measure.inv.instIsMulRightInvariant`：∀ {G : Type u_1} [ins
t : MeasurableSpace G] [inst_1 : DivisionMonoid G] [MeasurableMul G] [Measurable
Inv G]   {μ : MeasureTheory.Measure G} …
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
-/
theorem quasiMeasurePreserving_div [IsMulLeftInvariant μ] :
    QuasiMeasurePreserving (fun p : G × G => p.1 / p.2) (μ.prod ν) μ :=
  (quasiMeasurePreserving_div_of_right_invariant μ.inv ν).mono
    ((absolutelyContinuous_inv μ).prod AbsolutelyContinuous.rfl) (inv_absolutelyContinuous μ)

/-- A *left*-invariant measure is quasi-preserved by *right*-multiplication.
This should not be confused with `(measurePreserving_mul_right μ g).quasiMeasurePreserving`. -/
@[to_additive (attr := fun_prop)
/-- A *left*-invariant measure is quasi-preserved by *right*-addition.
This should not be confused with `(measurePreserving_add_right μ g).quasiMeasurePreserving`. -/]
/-
**MeasureTheory.quasiMeasurePreserving_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：quasiMeasurePreserving_mul_right [IsMulLeftInvariant μ] (g : G) : QuasiMea
surePreserving (fun h : G => h * g) μ μ
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.measure_mul_right_null`：measure_mul_right_null (y : G) : μ
 ((fun x => x * y) ⁻¹' s) = 0 ↔ μ s = 0
-/
theorem quasiMeasurePreserving_mul_right [IsMulLeftInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => h * g) μ μ := by
  refine ⟨measurable_mul_const g, AbsolutelyContinuous.mk fun s hs => ?_⟩
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null]; exact id

/-- A *right*-invariant measure is quasi-preserved by *left*-multiplication.
This should not be confused with `(measurePreserving_mul_left μ g).quasiMeasurePreserving`. -/
@[to_additive (attr := fun_prop)
/-- A *right*-invariant measure is quasi-preserved by *left*-addition.
This should not be confused with `(measurePreserving_add_left μ g).quasiMeasurePreserving`. -/]
/-
**MeasureTheory.quasiMeasurePreserving_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：quasiMeasurePreserving_mul_left [IsMulRightInvariant μ] (g : G) : QuasiMea
surePreserving (fun h : G => g * h) μ μ
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.mono`：mono (ha : μa' ≪ μa) 
(hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving f 
μa' μb'
· 使用定理 `MeasureTheory.inv_absolutelyContinuous`：inv_absolutelyContinuous : μ.inv
 ≪ μ
· 使用定理 `MeasureTheory.Measure.inv.instSFinite`：∀ {G : Type u_1} [inst : Measurab
leSpace G] [inst_1 : Inv G] (μ : MeasureTheory.Measure G) [MeasureTheory.SFinite
 μ],   MeasureTheory.SFinit…
· 使用定理 `MeasureTheory.Measure.inv.instIsMulLeftInvariant`：∀ {G : Type u_1} [inst
 : MeasurableSpace G] [inst_1 : DivisionMonoid G] [MeasurableMul G] [MeasurableI
nv G]   {μ : MeasureTheory.Measure G} …
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.absolutelyContinuous_inv`：absolutelyContinuous_inv : μ ≪ μ
.inv
· 使用定理 `MeasureTheory.quasiMeasurePreserving_mul_right`：quasiMeasurePreserving_m
ul_right [IsMulLeftInvariant μ] (g : G) : QuasiMeasurePreserving (fun h : G => h
 * g) μ μ
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用定理 `MeasureTheory.quasiMeasurePreserving_inv_of_right_invariant`：quasiMeasur
ePreserving_inv_of_right_invariant [IsMulRightInvariant μ] : QuasiMeasurePreserv
ing (Inv.inv : G -> G) μ μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.inv_inv`：∀ {G : Type u_1} [inst : MeasurableSpace 
G] [inst_1 : InvolutiveInv G] [MeasurableInv G] (μ : MeasureTheory.Measure G),  
 μ.inv.inv = μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
-/
theorem quasiMeasurePreserving_mul_left [IsMulRightInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => g * h) μ μ := by
  have :=
    (quasiMeasurePreserving_mul_right μ.inv g⁻¹).mono (inv_absolutelyContinuous μ.inv)
      (absolutelyContinuous_inv μ.inv)
  rw [μ.inv_inv] at this
  have :=
    (quasiMeasurePreserving_inv_of_right_invariant μ).comp
      (this.comp (quasiMeasurePreserving_inv_of_right_invariant μ))
  simp_rw [Function.comp_def, mul_inv_rev, inv_inv] at this
  exact this

end MeasurableInv

end QuasiMeasurePreserving

end MeasureTheory

