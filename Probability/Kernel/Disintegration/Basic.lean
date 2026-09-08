/-
Copyright (c) 2024 Yaël Dillies, Kin Yau James Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kin Yau James Wong, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Disintegration of measures and kernels

This file defines predicates for a kernel to "disintegrate" a measure or a kernel. This kernel is
also called the "conditional kernel" of the measure or kernel.

A measure `ρ : Measure (α × Ω)` is disintegrated by a kernel `ρCond : Kernel α Ω` if
`ρ.fst ⊗ₘ ρCond = ρ`.

A kernel `ρ : Kernel α (β × Ω)` is disintegrated by a kernel `κCond : Kernel (α × β) Ω` if
`κ.fst ⊗ₖ κCond = κ`.

## Main definitions

* `MeasureTheory.Measure.IsCondKernel ρ ρCond`: Predicate for the kernel `ρCond` to disintegrate the
  measure `ρ`.
* `ProbabilityTheory.Kernel.IsCondKernel κ κCond`: Predicate for the kernel `κ Cond` to disintegrate
  the kernel `κ`.

Further, if `κ` is an s-finite kernel from a countable `α` such that each measure `κ a` is
disintegrated by some kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`.

## See also

`Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean` for a **construction** of
disintegrating kernels.
-/

@[expose] public section

open MeasureTheory Set Filter MeasurableSpace ProbabilityTheory
open scoped ENNReal MeasureTheory Topology

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mΩ : MeasurableSpace Ω}

/-!
### Disintegration of measures

This section provides a predicate for a kernel to disintegrate a measure.
-/

namespace MeasureTheory.Measure
variable (ρ : Measure (α × Ω)) (ρCond : Kernel α Ω)

/-- A kernel `ρCond` is a conditional kernel for a measure `ρ` if it disintegrates it in the sense
that `ρ.fst ⊗ₘ ρCond = ρ`. -/
/-
**MeasureTheory.Measure.IsCondKernel** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：{α : Type u_1} →   {Ω : Type u_3} →     {mα : MeasurableSpace α} →       {
mΩ : MeasurableSpace Ω} → MeasureTheory.Measure (α × Ω) → ProbabilityTheory.Kern
el α Ω → Prop
参数：α × Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel `ρCond` is a conditional kernel for a measure `ρ` if it disintegrates i
t in the sense
that `ρ.fst ⊗ₘ ρCond = ρ`.
-/
class IsCondKernel : Prop where
  disintegrate : ρ.fst ⊗ₘ ρCond = ρ

variable [ρ.IsCondKernel ρCond]
/-
**MeasureTheory.Measure.disintegrate** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：disintegrate : ρ.fst otimesₘ ρCond = ρ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsCondKernel.disintegrate`：∀ {α : Type u_1} {Ω : T
ype u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} {ρ : MeasureTheory.Me
asure (α × Ω)}   {ρCond : Probability…
-/
lemma disintegrate : ρ.fst ⊗ₘ ρCond = ρ := IsCondKernel.disintegrate
/-
**MeasureTheory.Measure.IsCondKernel.isSFiniteKernel** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.IsCondKernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableS
pace Ω} (ρ : MeasureTheory.Measure (α × Ω))   (ρCond : ProbabilityTheory.Kernel 
α Ω) [ρ.IsCondKernel ρCond], ρ ≠ 0 → ProbabilityTheory.IsSFiniteKernel ρCond
参数：ρ : MeasureTheory.Measure (α × Ω)；ρCond : ProbabilityTheory.Kernel α Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用引理 `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel`：compProd_of_not_i
sSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) : μ ot
imesₘ κ = 0
-/
lemma IsCondKernel.isSFiniteKernel (hρ : ρ ≠ 0) : IsSFiniteKernel ρCond := by
  contrapose hρ; rwa [← ρ.disintegrate ρCond, Measure.compProd_of_not_isSFiniteKernel]

variable [IsFiniteMeasure ρ]

/-- Auxiliary lemma for `IsCondKernel.apply_of_ne_zero`. -/
/-
**MeasureTheory.Measure.IsCondKernel.apply_of_ne_zero_of_measurableSet** 是 Mathl
ib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for `IsCondKernel.apply_of_ne_zero`.
-/
private lemma IsCondKernel.apply_of_ne_zero_of_measurableSet [MeasurableSingletonClass α] {x : α}
    (hx : ρ.fst {x} ≠ 0) {s : Set Ω} (hs : MeasurableSet s) :
    ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have := isSFiniteKernel ρ ρCond (by rintro rfl; simp at hx)
  nth_rewrite 2 [← ρ.disintegrate ρCond]
  rw [Measure.compProd_apply (measurableSet_prod.mpr (Or.inl ⟨measurableSet_singleton x, hs⟩))]
  have (a : _) : ρCond a (Prod.mk a ⁻¹' {x} ×ˢ s) = ({x} : Set α).indicator (ρCond · s) a := by
    obtain rfl | hax := eq_or_ne a x
    · simp only [singleton_prod, mem_singleton_iff, indicator_of_mem]
      congr with y
      simp
    · simp only [singleton_prod, mem_singleton_iff, hax, not_false_eq_true, indicator_of_notMem]
      have : Prod.mk a ⁻¹' Prod.mk x '' s = ∅ := by ext y; simp [Ne.symm hax]
      simp only [this, measure_empty]
  simp_rw [this]
  rw [MeasureTheory.lintegral_indicator (measurableSet_singleton x)]
  simp only [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top _ _), one_mul]

/-- If the singleton `{x}` has non-zero mass for `ρ.fst`, then for all `s : Set Ω`,
`ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)` . -/
/-
**MeasureTheory.Measure.IsCondKernel.apply_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure.IsCondKernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableS
pace Ω} (ρ : MeasureTheory.Measure (α × Ω))   (ρCond : ProbabilityTheory.Kernel 
α Ω) [ρ.IsCondKernel ρCond] [MeasureTheory.IsFiniteMeasure ρ]   [MeasurableSingl
etonClass α] {x : α}, ρ.fst {x} ≠ 0 → ∀ (s : Set Ω), (ρCond x) s = (ρ.fst {x})⁻¹
 * ρ ({x} ×ˢ s)
参数：ρ : MeasureTheory.Measure (α × Ω)；ρCond : ProbabilityTheory.Kernel α Ω；s : Se
t Ω；ρCond x；ρ.fst {x}；{x} ×ˢ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Probability.Kernel.Disintegration.Basic.0.MeasureTheory
.Measure.IsCondKernel.apply_of_ne_zero_of_measurableSet`：∀ {α : Type u_1} {Ω : T
ype u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} (ρ : MeasureTheory.Me
asure (α × Ω))   (ρCond : Probability…
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用引理 `measurableEmbedding_prodMk_left`：measurableEmbedding_prodMk_left [Measur
ableSingletonClass α] (x : α) : MeasurableEmbedding (Prod.mk x : β -> α × β)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the singleton `{x}` has non-zero mass for `ρ.fst`, then for all `s : Set Ω`,
`ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)` .
-/
lemma IsCondKernel.apply_of_ne_zero [MeasurableSingletonClass α] {x : α}
    (hx : ρ.fst {x} ≠ 0) (s : Set Ω) : ρCond x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have : ρCond x s = ((ρ.fst {x})⁻¹ • ρ).comap (fun (y : Ω) ↦ (x, y)) s := by
    congr 2 with s hs
    simp [IsCondKernel.apply_of_ne_zero_of_measurableSet _ _ hx hs,
      (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]
  simp [this, (measurableEmbedding_prodMk_left x).comap_apply, Set.singleton_prod]
/-
**MeasureTheory.Measure.IsCondKernel.isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure.IsCondKernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableS
pace Ω} (ρ : MeasureTheory.Measure (α × Ω))   (ρCond : ProbabilityTheory.Kernel 
α Ω) [ρ.IsCondKernel ρCond] [MeasureTheory.IsFiniteMeasure ρ]   [MeasurableSingl
etonClass α] {a : α}, ρ.fst {a} ≠ 0 → MeasureTheory.IsProbabilityMeasure (ρCond 
a)
参数：ρ : MeasureTheory.Measure (α × Ω)；ρCond : ProbabilityTheory.Kernel α Ω；ρCond 
a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.IsCondKernel.apply_of_ne_zero`：∀ {α : Type u_1} {Ω
 : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} (ρ : MeasureTheor
y.Measure (α × Ω))   (ρCond : Probability…
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.fst_apply`：fst_apply {s : Set α} (hs : MeasurableS
et s) : ρ.fst s = ρ (Prod.fst ⁻¹' s)
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Measure.fst.instIsFiniteMeasure`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureThe
ory.Measure (α × β)} [MeasureTheory…
-/
lemma IsCondKernel.isProbabilityMeasure [MeasurableSingletonClass α] {a : α} (ha : ρ.fst {a} ≠ 0) :
    IsProbabilityMeasure (ρCond a) := by
  constructor
  rw [IsCondKernel.apply_of_ne_zero _ _ ha, prod_univ, ← Measure.fst_apply
    (measurableSet_singleton _), ENNReal.inv_mul_cancel ha (measure_ne_top _ _)]
/-
**MeasureTheory.Measure.IsCondKernel.isMarkovKernel** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure.IsCondKernel`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableS
pace Ω} (ρ : MeasureTheory.Measure (α × Ω))   (ρCond : ProbabilityTheory.Kernel 
α Ω) [ρ.IsCondKernel ρCond] [MeasureTheory.IsFiniteMeasure ρ]   [MeasurableSingl
etonClass α], (∀ (a : α), ρ.fst {a} ≠ 0) → ProbabilityTheory.IsMarkovKernel ρCon
d
参数：ρ : MeasureTheory.Measure (α × Ω)；ρCond : ProbabilityTheory.Kernel α Ω；∀ (a :
 α), ρ.fst {a} ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsCondKernel.isProbabilityMeasure`：∀ {α : Type u_1
} {Ω : Type u_3} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} (ρ : MeasureT
heory.Measure (α × Ω))   (ρCond : Probability…
-/
lemma IsCondKernel.isMarkovKernel [MeasurableSingletonClass α] (hρ : ∀ a, ρ.fst {a} ≠ 0) :
    IsMarkovKernel ρCond := ⟨fun _ ↦ isProbabilityMeasure _ _ (hρ _)⟩

end MeasureTheory.Measure

/-!
### Disintegration of kernels

This section provides a predicate for a kernel to disintegrate a kernel. It also proves that if `κ`
is an s-finite kernel from a countable `α` such that each measure `κ a` is disintegrated by some
kernel, then `κ` itself is disintegrated by a kernel, namely
`ProbabilityTheory.Kernel.condKernelCountable`.
-/

namespace ProbabilityTheory.Kernel
variable (κ : Kernel α (β × Ω)) (κCond : Kernel (α × β) Ω)

/-! #### Predicate for a kernel to disintegrate a kernel -/

/-- A kernel `κCond` is a conditional kernel for a kernel `κ` if it disintegrates it in the sense
that `κ.fst ⊗ₖ κCond = κ`. -/
/-
**ProbabilityTheory.Kernel.IsCondKernel** 是 Mathlib 中的一个归纳类型，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {Ω : Type u_3} →       {mα : Measu
rableSpace α} →         {mβ : MeasurableSpace β} →           {mΩ : MeasurableSpa
ce Ω} → ProbabilityTheory.Kernel α (β × Ω) → ProbabilityTheory.Kernel (α × β) Ω 
→ Prop
参数：β × Ω；α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel `κCond` is a conditional kernel for a kernel `κ` if it disintegrates it
 in the sense
that `κ.fst ⊗ₖ κCond = κ`.
-/
class IsCondKernel : Prop where
  protected disintegrate : κ.fst ⊗ₖ κCond = κ
/-
**ProbabilityTheory.Kernel.instIsCondKernel_zero** 是 Mathlib 中的一个实例，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：instIsCondKernel_zero (κCond : Kernel (α × β) Ω) : IsCondKernel 0 κCond wh
ere disintegrate
参数：κCond : Kernel (α × β) Ω。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.fst_zero`：fst_zero : fst (0 : Kernel α (β × γ))
 = 0
· 使用引理 `ProbabilityTheory.Kernel.compProd_zero_left`：compProd_zero_left (κ : Ker
nel (α × β) γ) : (0 : Kernel α β) otimesₖ κ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsCondKernel_zero (κCond : Kernel (α × β) Ω) : IsCondKernel 0 κCond where
  disintegrate := by simp
/-
**ProbabilityTheory.Kernel.disintegrate** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：disintegrate [κ.IsCondKernel κCond] : κ.fst otimesₖ κCond = κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsCondKernel.disintegrate`：∀ {α : Type u_1} {β 
: Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {
mΩ : MeasurableSpace Ω} {κ : Probability…
-/
lemma disintegrate [κ.IsCondKernel κCond] : κ.fst ⊗ₖ κCond = κ := IsCondKernel.disintegrate

/-- A conditional kernel is almost everywhere a probability measure. -/
/-
**ProbabilityTheory.Kernel.IsCondKernel.isProbabilityMeasure_ae** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.Kernel.IsCondKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mΩ : MeasurableSpace Ω} (κ : ProbabilityTheory.Kernel 
α (β × Ω)) (κCond : ProbabilityTheory.Kernel (α × β) Ω)   [ProbabilityTheory.IsF
initeKernel κ.fst] [κ.IsCondKernel κCond] (a : α),   ∀ᵐ (b : β) ∂κ.fst a, Measur
eTheory.IsProbabilityMeasure (κCond (a, b))
参数：κ : ProbabilityTheory.Kernel α (β × Ω)；κCond : ProbabilityTheory.Kernel (α × 
β) Ω；a : α；b : β；κCond (a, b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.disintegrate`：disintegrate [κ.IsCondKernel κCon
d] : κ.fst otimesₖ κCond = κ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.fst_compProd_apply`：fst_compProd_apply (κ : Ker
nel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] (x : α) 
{s : Set β} (hs : MeasurableSet s…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.isFiniteKernel_of_isFiniteKernel_fst`：∀ {α : Ty
pe u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {mγ : MeasurableSpace γ} {κ : Probability…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用引理 `MeasureTheory.ae_le_const_iff_forall_gt_measure_zero`：ae_le_const_iff_fo
rall_gt_measure_zero {β} [LinearOrder β] [TopologicalSpace β] [OrderTopology β] 
[FirstCountableTopology β] {μ : Measure α}…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
A conditional kernel is almost everywhere a probability measure.
-/
lemma IsCondKernel.isProbabilityMeasure_ae [IsFiniteKernel κ.fst] [κ.IsCondKernel κCond] (a : α) :
    ∀ᵐ b ∂(κ.fst a), IsProbabilityMeasure (κCond (a, b)) := by
  have h := disintegrate κ κCond
  by_cases h_sfin : IsSFiniteKernel κCond
  swap; · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h_sfin] at h; simp [h.symm]
  suffices ∀ᵐ b ∂(κ.fst a), κCond (a, b) Set.univ = 1 by
    convert! this with b
    exact ⟨fun _ ↦ measure_univ, fun h ↦ ⟨h⟩⟩
  suffices (∀ᵐ b ∂(κ.fst a), κCond (a, b) Set.univ ≤ 1)
      ∧ (∀ᵐ b ∂(κ.fst a), 1 ≤ κCond (a, b) Set.univ) by
    filter_upwards [this.1, this.2] with b h1 h2 using le_antisymm h1 h2
  have h_eq s (hs : MeasurableSet s) :
      ∫⁻ b, s.indicator (fun b ↦ κCond (a, b) Set.univ) b ∂κ.fst a = κ.fst a s := by
    conv_rhs => rw [← h]
    rw [fst_compProd_apply _ _ _ hs]
  have h_meas : Measurable fun b ↦ κCond (a, b) Set.univ :=
    (κCond.measurable_coe MeasurableSet.univ).comp measurable_prodMk_left
  constructor
  · rw [ae_le_const_iff_forall_gt_measure_zero]
    intro r hr
    let s := {b | r ≤ κCond (a, b) Set.univ}
    have hs : MeasurableSet s := h_meas measurableSet_Ici
    have h_2_le : s.indicator (fun _ ↦ r) ≤ s.indicator (fun b ↦ (κCond (a, b)) Set.univ) := by
      intro b
      by_cases hbs : b ∈ s
      · simpa [hbs]
      · simp [hbs]
    have : ∫⁻ b, s.indicator (fun _ ↦ r) b ∂(κ.fst a) ≤ κ.fst a s :=
      (lintegral_mono h_2_le).trans_eq (h_eq s hs)
    rw [lintegral_indicator_const hs] at this
    contrapose! this with h_ne_zero
    conv_lhs => rw [← one_mul (κ.fst a s)]
    gcongr
    finiteness
  · rw [ae_const_le_iff_forall_lt_measure_zero]
    intro r hr
    let s := {b | κCond (a, b) Set.univ ≤ r}
    have hs : MeasurableSet s := h_meas measurableSet_Iic
    have h_2_le : s.indicator (fun b ↦ (κCond (a, b)) Set.univ) ≤ s.indicator (fun _ ↦ r) := by
      intro b
      by_cases hbs : b ∈ s
      · simpa [hbs]
      · simp [hbs]
    have : κ.fst a s ≤ ∫⁻ b, s.indicator (fun _ ↦ r) b ∂(κ.fst a) :=
      (h_eq s hs).symm.trans_le (lintegral_mono h_2_le)
    rw [lintegral_indicator_const hs] at this
    contrapose! this with h_ne_zero
    conv_rhs => rw [← one_mul (κ.fst a s)]
    gcongr
    finiteness


/-! #### Existence of a disintegrating kernel in a countable space -/

section Countable
variable [Countable α] (κCond : α → Kernel β Ω)

/-- Auxiliary definition for `ProbabilityTheory.Kernel.condKernel`.

A conditional kernel for `κ : Kernel α (β × Ω)` where `α` is countable and `Ω` is a measurable
space. -/
/-
**ProbabilityTheory.Kernel.condKernelCountable** 是 Mathlib 中的一个定义，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：condKernelCountable (h_atom : forall x y, x in measurableAtom y -> κCond x
 = κCond y) : Kernel (α × β) Ω where toFun p
参数：h_atom : forall x y, x in measurableAtom y -> κCond x = κCond y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `ProbabilityTheory.Kernel.condKernel`.

A conditional kernel for `κ : Kernel α (β × Ω)` where `α` is countable and `Ω` i
s a measurable
space.
-/
noncomputable def condKernelCountable (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y) :
    Kernel (α × β) Ω where
  toFun p := κCond p.1 p.2
  measurable' := by
    refine measurable_from_prod_countable_right' (fun a ↦ (κCond a).measurable) fun x y hx hy ↦ ?_
    simpa using DFunLike.congr (h_atom _ _ hy) rfl
/-
**ProbabilityTheory.Kernel.condKernelCountable_apply** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：condKernelCountable_apply (h_atom : forall x y, x in measurableAtom y -> κ
Cond x = κCond y) (p : α × β) : condKernelCountable κCond h_atom p = κCond p.1 p
.2
参数：h_atom : forall x y, x in measurableAtom y -> κCond x = κCond y；p : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma condKernelCountable_apply (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y)
    (p : α × β) : condKernelCountable κCond h_atom p = κCond p.1 p.2 := rfl
/-
**ProbabilityTheory.Kernel.condKernelCountable.instIsMarkovKernel** 是 Mathlib 中的
一个定理，位于命名空间 `ProbabilityTheory.Kernel.condKernelCountable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mΩ : MeasurableSpace Ω} [inst : Countable α] (κCond : 
α → ProbabilityTheory.Kernel β Ω)   [∀ (a : α), ProbabilityTheory.IsMarkovKernel
 (κCond a)]   (h_atom : ∀ (x y : α), x ∈ measurableAtom y → κCond x = κCond y), 
  ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.Kernel.condKernelCountable
 κCond h_atom)
参数：κCond : α → ProbabilityTheory.Kernel β Ω；a : α；κCond a；h_atom : ∀ (x y : α), 
x ∈ measurableAtom y → κCond x = κCond y；ProbabilityTheory.Kernel.condKernelCoun
table κCond h_atom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [self : ProbabilityTh…
-/
instance condKernelCountable.instIsMarkovKernel [∀ a, IsMarkovKernel (κCond a)]
     (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y) :
    IsMarkovKernel (condKernelCountable κCond h_atom) where
  isProbabilityMeasure p := (‹∀ a, IsMarkovKernel (κCond a)› p.1).isProbabilityMeasure p.2
/-
**ProbabilityTheory.Kernel.condKernelCountable.instIsCondKernel** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.Kernel.condKernelCountable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mΩ : MeasurableSpace Ω} [inst : Countable α] (κCond : 
α → ProbabilityTheory.Kernel β Ω)   [∀ (a : α), ProbabilityTheory.IsMarkovKernel
 (κCond a)]   (h_atom : ∀ (x y : α), x ∈ measurableAtom y → κCond x = κCond y) (
κ : ProbabilityTheory.Kernel α (β × Ω))   [ProbabilityTheory.IsSFiniteKernel κ] 
[∀ (a : α), (κ a).IsCondKernel (κCond a)],   κ.IsCondKernel (ProbabilityTheory.K
ernel.condKernelCountable κCond h_atom)
参数：κCond : α → ProbabilityTheory.Kernel β Ω；a : α；κCond a；h_atom : ∀ (x y : α), 
x ∈ measurableAtom y → κCond x = κCond y；κ : ProbabilityTheory.Kernel α (β × Ω)；
a : α；κ a；κCond a；ProbabilityTheory.Kernel.condKernelCountable κCond h_atom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.condKernelCountable.instIsMarkovKernel`：∀ {α : 
Type u_1} {β : Type u_2} {Ω : Type u_3} {mα : MeasurableSpace α} {mβ : Measurabl
eSpace β}   {mΩ : MeasurableSpace Ω} [inst : Countabl…
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
instance condKernelCountable.instIsCondKernel [∀ a, IsMarkovKernel (κCond a)]
    (h_atom : ∀ x y, x ∈ measurableAtom y → κCond x = κCond y) (κ : Kernel α (β × Ω))
    [IsSFiniteKernel κ] [∀ a, (κ a).IsCondKernel (κCond a)] :
    κ.IsCondKernel (condKernelCountable κCond h_atom) := by
  constructor
  ext a s hs
  conv_rhs => rw [← (κ a).disintegrate (κCond a)]
  simp_rw [compProd_apply hs, condKernelCountable_apply, Measure.compProd_apply hs]
  congr

end Countable
end ProbabilityTheory.Kernel

