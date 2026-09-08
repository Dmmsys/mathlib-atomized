/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Absolute continuity of the composition of measures and kernels

This file contains some results about the absolute continuity of the composition of measures and
kernels which use an assumption `CountableOrCountablyGenerated α β` on the measurable spaces.

Results that hold without that assumption are in files about the definitions of compositions and
products, like `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` and
`Mathlib/Probability/Kernel/Composition/MeasureComp.lean`.

The assumption ensures the measurability of the sets where two kernels are absolutely continuous
or mutually singular.

## Main statements

* `absolutelyContinuous_compProd_iff'`: `μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a`.

-/

public section

open ProbabilityTheory Filter

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} [IsFiniteKernel κ] [IsFiniteKernel η]
  [MeasurableSpace.CountableOrCountablyGenerated α β]

/-
**MeasureTheory.Measure.MutuallySingular.compProd_of_right** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ η : ProbabilityTheory.Kernel α β}   [ProbabilityTheory.IsFiniteKernel
 κ] [ProbabilityTheory.IsFiniteKernel η]   [MeasurableSpace.CountableOrCountably
Generated α β] (μ ν : MeasureTheory.Measure α),   (∀ᵐ (a : α) ∂μ, (κ a).Mutually
Singular (η a)) → (μ.compProd κ).MutuallySingular (ν.compProd η)
参数：μ ν : MeasureTheory.Measure α；∀ᵐ (a : α) ∂μ, (κ a).MutuallySingular (η a)；μ.c
ompProd κ；ν.compProd η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.measurableSet_mutuallySingularSet`：measurableSe
t_mutuallySingularSet (κ η : Kernel α γ) : MeasurableSet (mutuallySingularSet κ 
η)
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `ProbabilityTheory.Kernel.measure_mutuallySingularSetSlice`：measure_mutua
llySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a 
: α) : η a (mutuallySingularSetSlice κ η a) = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.withDensity_rnDeriv_eq_zero_iff_measure_eq_zero
`：withDensity_rnDeriv_eq_zero_iff_measure_eq_zero (κ η : Kernel α γ) [IsFiniteKe
rnel κ] [IsFiniteKernel η] (a : α) : withDensity η (rnDeriv κ …
· 使用引理 `ProbabilityTheory.Kernel.withDensity_rnDeriv_eq_zero_iff_mutuallySingula
r`：withDensity_rnDeriv_eq_zero_iff_mutuallySingular (κ η : Kernel α γ) [IsFinite
Kernel κ] [IsFiniteKernel η] (a : α) : withDensity η (rnDeriv κ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `MeasureTheory.Measure.compProd_of_not_sfinite`：compProd_of_not_sfinite (
μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) : μ otimesₘ κ = 0
-/
lemma MutuallySingular.compProd_of_right (μ ν : Measure α) (hκη : ∀ᵐ a ∂μ, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  let s := κ.mutuallySingularSet η
  have hs : MeasurableSet s := Kernel.measurableSet_mutuallySingularSet κ η
  symm
  refine ⟨s, hs, ?_⟩
  rw [compProd_apply hs, compProd_apply hs.compl]
  have h_eq a : Prod.mk a ⁻¹' s = Kernel.mutuallySingularSetSlice κ η a := rfl
  have h1 a : η a (Prod.mk a ⁻¹' s) = 0 := by rw [h_eq, Kernel.measure_mutuallySingularSetSlice]
  have h2 : ∀ᵐ a ∂μ, κ a (Prod.mk a ⁻¹' s)ᶜ = 0 := by
    filter_upwards [hκη] with a ha
    rwa [h_eq, ← Kernel.withDensity_rnDeriv_eq_zero_iff_measure_eq_zero κ η a,
      Kernel.withDensity_rnDeriv_eq_zero_iff_mutuallySingular]
  simp [h1, lintegral_congr_ae h2]
/-
**MeasureTheory.Measure.MutuallySingular.compProd_of_right'** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ η : ProbabilityTheory.Kernel α β}   [ProbabilityTheory.IsFiniteKernel
 κ] [ProbabilityTheory.IsFiniteKernel η]   [MeasurableSpace.CountableOrCountably
Generated α β] (μ ν : MeasureTheory.Measure α),   (∀ᵐ (a : α) ∂ν, (κ a).Mutually
Singular (η a)) → (μ.compProd κ).MutuallySingular (ν.compProd η)
参数：μ ν : MeasureTheory.Measure α；∀ᵐ (a : α) ∂ν, (κ a).MutuallySingular (η a)；μ.c
ompProd κ；ν.compProd η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.compProd_of_right`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : Proba
bilityTheory.Kernel α β}   [ProbabilityTheory.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma MutuallySingular.compProd_of_right' (μ ν : Measure α) (hκη : ∀ᵐ a ∂ν, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  refine (MutuallySingular.compProd_of_right _ _ ?_).symm
  simp_rw [MutuallySingular.comm, hκη]
/-
**MeasureTheory.Measure.mutuallySingular_compProd_right_iff** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory.Measure`。
形式化陈述：mutuallySingular_compProd_right_iff [SFinite μ] : μ otimesₘ κ ⟂ₘ μ otimesₘ
 η ↔ forallᵐ a ∂μ, κ a ⟂ₘ η a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.mutuallySingular_of_mutuallySingular_compProd`：mut
uallySingular_of_mutuallySingular_compProd {ξ : Measure α} [SFinite μ] [SFinite 
ν] [IsSFiniteKernel κ] [IsSFiniteKernel η] (h : μ otimesₘ…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `MeasureTheory.Measure.MutuallySingular.compProd_of_right`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : Proba
bilityTheory.Kernel α β}   [ProbabilityTheory.…
-/
lemma mutuallySingular_compProd_right_iff [SFinite μ] :
    μ ⊗ₘ κ ⟂ₘ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ⟂ₘ η a :=
  ⟨fun h ↦ mutuallySingular_of_mutuallySingular_compProd h AbsolutelyContinuous.rfl
    AbsolutelyContinuous.rfl, MutuallySingular.compProd_of_right _ _⟩
/-
**MeasureTheory.Measure.AbsolutelyContinuous.kernel_of_compProd** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ ν : MeasureTheory.Measure α}   {κ η : ProbabilityTheory.Kernel α β} [
ProbabilityTheory.IsFiniteKernel κ] [ProbabilityTheory.IsFiniteKernel η]   [Meas
urableSpace.CountableOrCountablyGenerated α β] [MeasureTheory.SFinite μ],   (μ.c
ompProd κ).AbsolutelyContinuous (ν.compProd η) → ∀ᵐ (a : α) ∂μ, (κ a).Absolutely
Continuous (η a)
参数：μ.compProd κ；ν.compProd η；a : α；κ a；η a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.MutuallySingular.compProd_of_right`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : Proba
bilityTheory.Kernel α β}   [ProbabilityTheory.…
· 使用定理 `ProbabilityTheory.Kernel.instIsFiniteKernelSingularPart`：∀ {α : Type u_1
} {γ : Type u_2} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {κ η : Probab
ilityTheory.Kernel α γ}   [hαγ : MeasurableSp…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `ProbabilityTheory.Kernel.mutuallySingular_singularPart`：mutuallySingular
_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
 singularPart κ η a ⟂ₘ η a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.compProd_eq_zero_iff`：compProd_eq_zero_iff [SFinit
e μ] [IsSFiniteKernel κ] : μ otimesₘ κ = 0 ↔ forallᵐ a ∂μ, κ a = 0
· 使用引理 `MeasureTheory.Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingula
r`：eq_zero_of_absolutelyContinuous_of_mutuallySingular {μ ν : Measure α} (h_ac :
 μ ≪ ν) (h_ms : μ ⟂ₘ ν) : μ = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_left_iff`：add_left_iff {μ
₁ μ₂ ν : Measure α} : μ₁ + μ₂ ≪ ν ↔ μ₁ ≪ ν ∧ μ₂ ≪ ν
· 使用引理 `MeasureTheory.Measure.compProd_add_right`：compProd_add_right (μ : Measur
e α) (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η] : μ otimesₘ (κ +
 η) = μ otimesₘ κ + μ otimesₘ …
· 使用定理 `ProbabilityTheory.Kernel.instIsFiniteKernelWithDensityRnDeriv`：∀ {α : Ty
pe u_1} {γ : Type u_2} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {κ η : 
ProbabilityTheory.Kernel α γ}   [hαγ : MeasurableSp…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`：rnDeriv_add_singularP
art (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] : withDensity η (rn
Deriv κ η) + singularPart κ η = κ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ProbabilityTheory.Kernel.singularPart_eq_zero_iff_absolutelyContinuous`：
singularPart_eq_zero_iff_absolutelyContinuous (κ η : Kernel α γ) [IsFiniteKernel
 κ] [IsFiniteKernel η] (a : α) : singularPart κ η a = 0 ↔ κ …
-/
lemma AbsolutelyContinuous.kernel_of_compProd [SFinite μ] (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    ∀ᵐ a ∂μ, κ a ≪ η a := by
  suffices ∀ᵐ a ∂μ, κ.singularPart η a = 0 by
    filter_upwards [this] with a ha
    rwa [Kernel.singularPart_eq_zero_iff_absolutelyContinuous] at ha
  rw [← κ.rnDeriv_add_singularPart η, compProd_add_right, AbsolutelyContinuous.add_left_iff] at h
  have : μ ⊗ₘ κ.singularPart η ⟂ₘ ν ⊗ₘ η :=
    MutuallySingular.compProd_of_right μ ν (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  refine compProd_eq_zero_iff.mp ?_
  exact eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2 this
/-
**MeasureTheory.Measure.absolutelyContinuous_compProd_iff'** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_compProd_iff' [SFinite μ] [SFinite ν] [forall a, NeZe
ro (κ a)] : μ otimesₘ κ ≪ ν otimesₘ η ↔ μ ≪ ν ∧ forallᵐ a ∂μ, κ a ≪ η a
参数：κ a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_of_compProd`：absolutelyContin
uous_of_compProd [SFinite μ] [IsSFiniteKernel κ] [h_zero : forall a, NeZero (κ a
)] (h : μ otimesₘ κ ≪ ν otimesₘ η) : μ ≪ ν
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.kernel_of_compProd`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : 
MeasureTheory.Measure α}   {κ η : ProbabilityTheory…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureThe
ory.Measure α}   {κ η : ProbabilityTheory…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma absolutelyContinuous_compProd_iff' [SFinite μ] [SFinite ν] [∀ a, NeZero (κ a)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a :=
  ⟨fun h ↦ ⟨absolutelyContinuous_of_compProd h, h.kernel_of_compProd⟩, fun h ↦ h.1.compProd h.2⟩
/-
**MeasureTheory.Measure.absolutelyContinuous_compProd_right_iff** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_compProd_right_iff [SFinite μ] : μ otimesₘ κ ≪ μ otim
esₘ η ↔ forallᵐ a ∂μ, κ a ≪ η a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.kernel_of_compProd`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : 
MeasureTheory.Measure α}   {κ η : ProbabilityTheory…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd_right`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measur
eTheory.Measure α}   {κ η : ProbabilityTheory.K…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma absolutelyContinuous_compProd_right_iff [SFinite μ] :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ≪ η a :=
  ⟨AbsolutelyContinuous.kernel_of_compProd, AbsolutelyContinuous.compProd_right⟩

end MeasureTheory.Measure

