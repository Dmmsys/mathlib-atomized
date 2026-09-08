/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Density
public import Mathlib.Probability.Moments.Variance

/-!
# Law of a random variable

We introduce a predicate `HasLaw X μ P` stating that the random variable `X` has law `μ` under
the measure `P`. This is expressed as `P.map X = μ`. We also require `X` to be `P`-almost-everywhere
measurable. Indeed, if `X` is not almost-everywhere measurable then `P.map X` is defined to be `0`,
so that `HasLaw X 0 P` would be true. The measurability hypothesis ensures nice interactions with
operations on the codomain of `X`.
See for instance `HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`.
-/

public section

open MeasureTheory Measure

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X Y : Ω → 𝓧}
  {μ : Measure 𝓧} {P : Measure Ω}

variable (X μ) in
/-- The predicate `HasLaw X μ P` registers the fact that the random variable `X` has law `μ` under
the measure `P`, in other words that `P.map X = μ`. We also require `X` to be `AEMeasurable`,
to allow for nice interactions with operations on the codomain of `X`. See for instance
`HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`. -/
@[fun_prop]
/-
**ProbabilityTheory.HasLaw** 是 Mathlib 中的一个结构，位于命名空间 `ProbabilityTheory`。
形式化陈述：HasLaw (P : Measure Ω
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate `HasLaw X μ P` registers the fact that the random variable `X` has
 law `μ` under
the measure `P`, in other words that `P.map X = μ`. We also require `X` to be `A
EMeasurable`,
to allow for nice interactions with operations on the codomain of `X`. See for i
nstance
`HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`.
-/
structure HasLaw (P : Measure Ω := by volume_tac) : Prop where
  protected aemeasurable : AEMeasurable X P := by fun_prop
  protected map_eq : P.map X = μ

attribute [fun_prop] HasLaw.aemeasurable
/-
**ProbabilityTheory.HasLaw.measure_eq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
},   ProbabilityTheory.HasLaw X μ P → ∀ {p : 𝓧 → Prop}, MeasurableSet {x | p x} 
→ P {ω | p (X ω)} = μ {x | p x}
参数：X ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HasLaw.measure_eq (hX : HasLaw X μ P) {p : 𝓧 → Prop} (hp : MeasurableSet {x | p x}) :
    P {ω | p (X ω)} = μ {x | p x} := by
  rw [← hX.map_eq, map_apply_of_aemeasurable hX.aemeasurable hp]
  simp
/-
**ProbabilityTheory.HasLaw.measureReal_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
},   ProbabilityTheory.HasLaw X μ P → ∀ {p : 𝓧 → Prop}, MeasurableSet {x | p x} 
→ P.real {ω | p (X ω)} = μ.real {x | p x}
参数：X ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `MeasureTheory.map_measureReal_apply_of_aemeasurable`：map_measureReal_app
ly_of_aemeasurable [MeasurableSpace β] {f : α -> β} (hf : AEMeasurable f μ) {s :
 Set β} (hs : MeasurableSet s) : (μ.map f…
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HasLaw.measureReal_eq (hX : HasLaw X μ P) {p : 𝓧 → Prop} (hp : MeasurableSet {x | p x}) :
    P.real {ω | p (X ω)} = μ.real {x | p x} := by
  rw [← hX.map_eq, map_measureReal_apply_of_aemeasurable hX.aemeasurable hp]
  simp

/-- If there is a random variable `X` with law `μ` such that `f(X)` has law `ν`, then
for any random variable `Y` with law `μ`, `f(Y)` has law `ν`. -/
/-
**ProbabilityTheory.HasLaw.comp_of_hasLaw_comp** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
} {Ω' : Type u_3} {𝓨 : Type u_4} {m' : MeasurableSpace Ω'}   {m𝓨 : MeasurableSpa
ce 𝓨} {P' : MeasureTheory.Measure Ω'} {ν : MeasureTheory.Measure 𝓨} {f : 𝓧 → 𝓨} 
{Y : Ω' → 𝓧},   AEMeasurable f μ →     ProbabilityTheory.HasLaw X μ P →       Pr
obabilityTheory.HasLaw Y μ P' →         ProbabilityTheory.HasLaw (fun ω => f (X 
ω)) ν P → ProbabilityTheory.HasLaw (fun ω => f (Y ω)) ν P'
参数：fun ω => f (X ω)；fun ω => f (Y ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.comp_aemeasurable`：comp_aemeasurable {f : α -> δ} {g : δ ->
 β} (hg : AEMeasurable g (μ.map f)) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ 
f) μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …

--- 原说明 ---
If there is a random variable `X` with law `μ` such that `f(X)` has law `ν`, the
n
for any random variable `Y` with law `μ`, `f(Y)` has law `ν`.
-/
lemma HasLaw.comp_of_hasLaw_comp {Ω' 𝓨 : Type*} {m' : MeasurableSpace Ω'} {m𝓨 : MeasurableSpace 𝓨}
    {P' : Measure Ω'} {ν : Measure 𝓨} {f : 𝓧 → 𝓨} {Y : Ω' → 𝓧} (hf : AEMeasurable f μ)
    (hX : HasLaw X μ P) (hY : HasLaw Y μ P') (h : HasLaw (fun ω ↦ f (X ω)) ν P) :
    HasLaw (fun ω ↦ f (Y ω)) ν P' where
  aemeasurable := (hY.map_eq ▸ hf).comp_aemeasurable hY.aemeasurable
  map_eq := by
    rw [← Function.comp_def,
      ← AEMeasurable.map_map_of_aemeasurable (hY.map_eq ▸ hf) hY.aemeasurable,
      hY.map_eq, ← hX.map_eq, AEMeasurable.map_map_of_aemeasurable (hX.map_eq ▸ hf) hX.aemeasurable,
      Function.comp_def, h.map_eq]
/-
**ProbabilityTheory.HasLaw.congr** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Ha
sLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X Y : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure
 Ω},   ProbabilityTheory.HasLaw X μ P → Y =ᵐ[P] X → ProbabilityTheory.HasLaw Y μ
 P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
-/
lemma HasLaw.congr (hX : HasLaw X μ P) (hY : Y =ᵐ[P] X) : HasLaw Y μ P where
  aemeasurable := hX.aemeasurable.congr hY.symm
  map_eq := by rw [map_congr hY, hX.map_eq]
/-
**ProbabilityTheory.hasLaw_congr** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：hasLaw_congr (hXY : X =ᵐ[P] Y) : HasLaw X μ P ↔ HasLaw Y μ P where mp h
参数：hXY : X =ᵐ[P] Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.HasLaw.congr`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Me
asurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X Y : Ω → 𝓧}   {μ : MeasureTheory.Mea
sure 𝓧} {P : Measure…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
lemma hasLaw_congr (hXY : X =ᵐ[P] Y) : HasLaw X μ P ↔ HasLaw Y μ P where
  mp h := h.congr hXY.symm
  mpr h := h.congr hXY
/-
**ProbabilityTheory._root_.MeasureTheory.MeasurePreserving.hasLaw** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.MeasurePreserving.hasLaw (h : MeasurePreserving X P μ) :
    HasLaw X μ P where
  aemeasurable := h.measurable.aemeasurable
  map_eq := h.map_eq
/-
**ProbabilityTheory.HasLaw.measurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
},   ProbabilityTheory.HasLaw X μ P → Measurable X → MeasureTheory.MeasurePreser
ving X P μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
-/
lemma HasLaw.measurePreserving (h₁ : HasLaw X μ P) (h₂ : Measurable X) :
    MeasurePreserving X P μ where
  measurable := h₂
  map_eq := h₁.map_eq
/-
**ProbabilityTheory.HasLaw.id** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.HasLa
w`。
形式化陈述：∀ {𝓧 : Type u_2} {m𝓧 : MeasurableSpace 𝓧} {μ : MeasureTheory.Measure 𝓧}, P
robabilityTheory.HasLaw id μ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
protected lemma HasLaw.id : HasLaw id μ μ where
  map_eq := map_id
/-
**ProbabilityTheory.HasLaw.ae_iff** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.H
asLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
},   ProbabilityTheory.HasLaw X μ P → ∀ {p : 𝓧 → Prop}, Measurable p → ((∀ᵐ (ω :
 Ω) ∂P, p (X ω)) ↔ ∀ᵐ (x : 𝓧) ∂μ, p x)
参数：(∀ᵐ (ω : Ω) ∂P, p (X ω)) ↔ ∀ᵐ (x : 𝓧) ∂μ, p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `MeasureTheory.ae_map_iff`：ae_map_iff {f : α -> β} (hf : AEMeasurable f μ
) {p : β -> Prop} (hp : MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔
 forallᵐ x ∂μ,…
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma HasLaw.ae_iff (hX : HasLaw X μ P) {p : 𝓧 → Prop} (hp : Measurable p) :
    (∀ᵐ ω ∂P, p (X ω)) ↔ ∀ᵐ x ∂μ, p x := by
  rw [← hX.map_eq, ae_map_iff hX.aemeasurable (measurableSet_setOfPred.2 hp)]
/-
**ProbabilityTheory.HasLaw.isFiniteMeasure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
},   ProbabilityTheory.HasLaw X μ P → (MeasureTheory.IsFiniteMeasure P ↔ Measure
Theory.IsFiniteMeasure μ)
参数：MeasureTheory.IsFiniteMeasure P ↔ MeasureTheory.IsFiniteMeasure μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map_iff`：∀ {α : Type u_1} {β : Typ
e u_2} {m0 : MeasurableSpace α} [mβ : MeasurableSpace β] {μ : MeasureTheory.Meas
ure α}   {f : α → β},   AEMeasurabl…
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem HasLaw.isFiniteMeasure_iff (hX : HasLaw X μ P) :
    IsFiniteMeasure P ↔ IsFiniteMeasure μ := by
  rw [← hX.map_eq, isFiniteMeasure_map_iff hX.aemeasurable]
/-
**ProbabilityTheory.HasLaw.isProbabilityMeasure_iff** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
},   ProbabilityTheory.HasLaw X μ P → (MeasureTheory.IsProbabilityMeasure P ↔ Me
asureTheory.IsProbabilityMeasure μ)
参数：MeasureTheory.IsProbabilityMeasure P ↔ MeasureTheory.IsProbabilityMeasure μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map_iff`：∀ {α : Type u_1} {β 
: Type u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheo
ry.Measure α}   {f : α → β},   AEMeasura…
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem HasLaw.isProbabilityMeasure_iff (hX : HasLaw X μ P) :
    IsProbabilityMeasure P ↔ IsProbabilityMeasure μ := by
  rw [← hX.map_eq, isProbabilityMeasure_map_iff hX.aemeasurable]
/-
**ProbabilityTheory.HasLaw.isFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
} [MeasureTheory.IsFiniteMeasure μ],   ProbabilityTheory.HasLaw X μ P → MeasureT
heory.IsFiniteMeasure P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ProbabilityTheory.HasLaw.isFiniteMeasure_iff`：∀ {Ω : Type u_1} {𝓧 : Type
 u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : Measu
reTheory.Measure 𝓧} {P : MeasureTh…
-/
lemma HasLaw.isFiniteMeasure [IsFiniteMeasure μ] (hX : HasLaw X μ P) : IsFiniteMeasure P :=
  hX.isFiniteMeasure_iff.2 ‹_›
/-
**ProbabilityTheory.HasLaw.isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
} [MeasureTheory.IsProbabilityMeasure μ],   ProbabilityTheory.HasLaw X μ P → Mea
sureTheory.IsProbabilityMeasure P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ProbabilityTheory.HasLaw.isProbabilityMeasure_iff`：∀ {Ω : Type u_1} {𝓧 :
 Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : 
MeasureTheory.Measure 𝓧} {P : MeasureTh…
-/
lemma HasLaw.isProbabilityMeasure [IsProbabilityMeasure μ] (hX : HasLaw X μ P) :
    IsProbabilityMeasure P := hX.isProbabilityMeasure_iff.2 ‹_›

@[fun_prop]
/-
**ProbabilityTheory.HasLaw.comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Has
Law`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
} {𝓨 : Type u_3} {m𝓨 : MeasurableSpace 𝓨}   {ν : MeasureTheory.Measure 𝓨} {Y : 𝓧
 → 𝓨},   ProbabilityTheory.HasLaw Y ν μ → ProbabilityTheory.HasLaw X μ P → Proba
bilityTheory.HasLaw (Y ∘ X) ν P
参数：Y ∘ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.comp_aemeasurable`：comp_aemeasurable {f : α -> δ} {g : δ ->
 β} (hg : AEMeasurable g (μ.map f)) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ 
f) μ
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
-/
lemma HasLaw.comp {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {ν : Measure 𝓨} {Y : 𝓧 → 𝓨}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (Y ∘ X) ν P where
  aemeasurable := (hX.map_eq ▸ hY.aemeasurable).comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [← AEMeasurable.map_map_of_aemeasurable _ hX.aemeasurable, hX.map_eq, hY.map_eq]
    rw [hX.map_eq]; exact hY.aemeasurable

@[fun_prop]
/-
**ProbabilityTheory.HasLaw.fun_comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
} {𝓨 : Type u_3} {m𝓨 : MeasurableSpace 𝓨}   {ν : MeasureTheory.Measure 𝓨} {Y : 𝓧
 → 𝓨},   ProbabilityTheory.HasLaw Y ν μ → ProbabilityTheory.HasLaw X μ P → Proba
bilityTheory.HasLaw (fun ω => Y (X ω)) ν P
参数：fun ω => Y (X ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
-/
lemma HasLaw.fun_comp {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {ν : Measure 𝓨} {Y : 𝓧 → 𝓨}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (fun ω ↦ Y (X ω)) ν P :=
  hY.comp hX
/-
**ProbabilityTheory._root_.MeasureTheory.MeasurePreserving.comp_hasLaw** 是 Mathl
ib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.MeasurePreserving.comp_hasLaw {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
    {ν : Measure 𝓨} {Y : 𝓧 → 𝓨} (hY : MeasurePreserving Y μ ν) (hX : HasLaw X μ P) :
    HasLaw (Y ∘ X) ν P :=
  hY.hasLaw.comp hX
/-
**ProbabilityTheory._root_.MeasureTheory.MeasurePreserving.fun_comp_hasLaw** 是 M
athlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.MeasurePreserving.fun_comp_hasLaw {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
    {ν : Measure 𝓨} {Y : 𝓧 → 𝓨} (hY : MeasurePreserving Y μ ν) (hX : HasLaw X μ P) :
    HasLaw (fun ω ↦ Y (X ω)) ν P :=
  hY.comp_hasLaw hX

@[to_additive]
/-
**ProbabilityTheory.IndepFun.hasLaw_mul** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {M
 : Type u_3} [inst : Monoid M]   {mM : MeasurableSpace M} [MeasurableMul₂ M] {μ 
ν : MeasureTheory.Measure M} [MeasureTheory.SigmaFinite μ]   [MeasureTheory.Sigm
aFinite ν] {X Y : Ω → M},   ProbabilityTheory.HasLaw X μ P →     ProbabilityTheo
ry.HasLaw Y ν P → ProbabilityTheory.IndepFun X Y P → ProbabilityTheory.HasLaw (X
 * Y) (μ.mconv ν) P
参数：X * Y；μ.mconv ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.mul`：AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (f * g) μ
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map₀'`：∀ {Ω : Type u_7} 
{mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : M
onoid M]   [inst_1 : MeasurableSpace M] [Me…
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
-/
lemma IndepFun.hasLaw_mul {M : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
    {μ ν : Measure M} [SigmaFinite μ] [SigmaFinite ν] {X Y : Ω → M}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) (hXY : X ⟂ᵢ[P] Y) :
    HasLaw (X * Y) (μ ∗ₘ ν) P where
  map_eq := by
    rw [hXY.map_mul_eq_map_mconv_map₀' hX.aemeasurable hY.aemeasurable, hX.map_eq, hY.map_eq]
    · rwa [hX.map_eq]
    · rwa [hY.map_eq]

@[to_additive]
/-
**ProbabilityTheory.IndepFun.hasLaw_fun_mul** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {M
 : Type u_3} [inst : Monoid M]   {mM : MeasurableSpace M} [MeasurableMul₂ M] {μ 
ν : MeasureTheory.Measure M} [MeasureTheory.SigmaFinite μ]   [MeasureTheory.Sigm
aFinite ν] {X Y : Ω → M},   ProbabilityTheory.HasLaw X μ P →     ProbabilityTheo
ry.HasLaw Y ν P →       ProbabilityTheory.IndepFun X Y P → ProbabilityTheory.Has
Law (fun ω => X ω * Y ω) (μ.mconv ν) P
参数：fun ω => X ω * Y ω；μ.mconv ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.hasLaw_mul`：∀ {Ω : Type u_1} {mΩ : Measurable
Space Ω} {P : MeasureTheory.Measure Ω} {M : Type u_3} [inst : Monoid M]   {mM : 
MeasurableSpace M} [Measura…
-/
lemma IndepFun.hasLaw_fun_mul {M : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
    {μ ν : Measure M} [SigmaFinite μ] [SigmaFinite ν] {X Y : Ω → M}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) (hXY : X ⟂ᵢ[P] Y) :
    HasLaw (fun ω ↦ X ω * Y ω) (μ ∗ₘ ν) P := hXY.hasLaw_mul hX hY
/-
**ProbabilityTheory.HasLaw.integral_comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {μ : MeasureTheory.Measure 𝓧}   {P : MeasureTheory.Measure Ω} {E : Type 
u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {X : Ω → 𝓧},   Pro
babilityTheory.HasLaw X μ P →     ∀ {f : 𝓧 → E}, MeasureTheory.AEStronglyMeasura
ble f μ → ∫ (x : Ω), (f ∘ X) x ∂P = ∫ (x : 𝓧), f x ∂μ
参数：x : Ω；f ∘ X；x : 𝓧。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
lemma HasLaw.integral_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Ω → 𝓧} (hX : HasLaw X μ P) {f : 𝓧 → E} (hf : AEStronglyMeasurable f μ) :
    P[f ∘ X] = ∫ x, f x ∂μ := by
  rw [← hX.map_eq, integral_map hX.aemeasurable, Function.comp_def]
  rwa [hX.map_eq]
/-
**ProbabilityTheory.HasLaw.lintegral_comp** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {μ : MeasureTheory.Measure 𝓧}   {P : MeasureTheory.Measure Ω} {X : Ω → 𝓧
},   ProbabilityTheory.HasLaw X μ P → ∀ {f : 𝓧 → ENNReal}, AEMeasurable f μ → ∫⁻
 (ω : Ω), f (X ω) ∂P = ∫⁻ (x : 𝓧), f x ∂μ
参数：ω : Ω；X ω；x : 𝓧。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
-/
lemma HasLaw.lintegral_comp {X : Ω → 𝓧} (hX : HasLaw X μ P) {f : 𝓧 → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∫⁻ ω, f (X ω) ∂P = ∫⁻ x, f x ∂μ := by
  rw [← hX.map_eq, lintegral_map' _ hX.aemeasurable]
  rwa [hX.map_eq]
/-
**ProbabilityTheory.HasLaw.integral_eq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_3} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [SecondC
ountableTopology E] {mE : MeasurableSpace E} [OpensMeasurableSpace E]   {μ : Mea
sureTheory.Measure E} {X : Ω → E}, ProbabilityTheory.HasLaw X μ P → ∫ (x : Ω), X
 x ∂P = ∫ (x : E), x ∂μ
参数：x : Ω；x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
· 使用定理 `ProbabilityTheory.HasLaw.integral_comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} 
{mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {μ : MeasureTheory.Measure 𝓧} 
  {P : MeasureTheory.Measure…
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HasLaw.integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    {X : Ω → E} (hX : HasLaw X μ P) : P[X] = ∫ x, x ∂μ := by
  rw [← Function.id_comp X, hX.integral_comp aestronglyMeasurable_id]
  simp
/-
**ProbabilityTheory.HasLaw.covariance_comp** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
},   ProbabilityTheory.HasLaw X μ P →     ∀ {f g : 𝓧 → ℝ},       AEMeasurable f 
μ →         AEMeasurable g μ → ProbabilityTheory.covariance (f ∘ X) (g ∘ X) P = 
ProbabilityTheory.covariance f g μ
参数：f ∘ X；g ∘ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用引理 `ProbabilityTheory.covariance_map`：covariance_map {Z : Ω' -> Ω} (hX : AES
tronglyMeasurable X (μ.map Z)) (hY : AEStronglyMeasurable Y (μ.map Z)) (hZ : AEM
easurable Z μ) : cov[X…
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
-/
lemma HasLaw.covariance_comp (hX : HasLaw X μ P) {f g : 𝓧 → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    cov[f ∘ X, g ∘ X; P] = cov[f, g; μ] := by
  rw [← hX.map_eq, covariance_map]
  · rw [hX.map_eq]
    exact hf.aestronglyMeasurable
  · rw [hX.map_eq]
    exact hg.aestronglyMeasurable
  · exact hX.aemeasurable
/-
**ProbabilityTheory.HasLaw.covariance_fun_comp** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
},   ProbabilityTheory.HasLaw X μ P →     ∀ {f g : 𝓧 → ℝ},       AEMeasurable f 
μ →         AEMeasurable g μ →           ProbabilityTheory.covariance (fun ω => 
f (X ω)) (fun ω => g (X ω)) P = ProbabilityTheory.covariance f g μ
参数：fun ω => f (X ω)；fun ω => g (X ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.covariance_comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2
} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTh
eory.Measure 𝓧} {P : MeasureTh…
-/
lemma HasLaw.covariance_fun_comp (hX : HasLaw X μ P) {f g : 𝓧 → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    cov[fun ω ↦ f (X ω), fun ω ↦ g (X ω); P] = cov[f, g; μ] :=
  hX.covariance_comp hf hg
/-
**ProbabilityTheory.HasLaw.variance_eq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {μ
 : MeasureTheory.Measure ℝ} {X : Ω → ℝ},   ProbabilityTheory.HasLaw X μ P → Prob
abilityTheory.variance X P = ProbabilityTheory.variance id μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用引理 `ProbabilityTheory.variance_map`：variance_map {Ω' : Type*} {mΩ' : Measura
bleSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} (hX : AEMeasurable X (μ.map Y)) (hY 
: AEMeasurable Y μ) …
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
-/
lemma HasLaw.variance_eq {μ : Measure ℝ} {X : Ω → ℝ} (hX : HasLaw X μ P) :
    Var[X; P] = Var[id; μ] := by
  rw [← hX.map_eq, variance_map aemeasurable_id hX.aemeasurable, Function.id_comp]
/-
**ProbabilityTheory.HasPDF.hasLaw** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.H
asPDF`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measure 𝓧} {P : MeasureTheory.Measure Ω
} [h : MeasureTheory.HasPDF X P μ],   ProbabilityTheory.HasLaw X (μ.withDensity 
(MeasureTheory.pdf X P μ)) P
参数：μ.withDensity (MeasureTheory.pdf X P μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasPDF.aemeasurable`：∀ {Ω : Type u_1} {E : Type u_2} [inst
 : MeasurableSpace E] {x : MeasurableSpace Ω} (X : Ω → E)   (ℙ : MeasureTheory.M
easure Ω) (μ : MeasureT…
· 使用定理 `MeasureTheory.map_eq_withDensity_pdf`：map_eq_withDensity_pdf {m : Measur
ableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
-/
lemma HasPDF.hasLaw [h : HasPDF X P μ] : HasLaw X (μ.withDensity (pdf X P μ)) P where
  aemeasurable := h.aemeasurable
  map_eq := map_eq_withDensity_pdf X P μ
/-
**ProbabilityTheory.HasLaw.ae_eq_of_smul_dirac** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {P : MeasureTheory.Measure Ω} {c : ENNReal} [MeasurableSin
gletonClass 𝓧] {x : 𝓧},   ProbabilityTheory.HasLaw X (c • MeasureTheory.Measure.
dirac x) P → X =ᵐ[P] fun x_1 => x
参数：c • MeasureTheory.Measure.dirac x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.ae_of_ae_map`：ae_of_ae_map {f : α -> β} (hf : AEMeasurable
 f μ) {p : β -> Prop} (h : forallᵐ y ∂μ.map f, p y) : forallᵐ x ∂μ, p (f x)
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `MeasureTheory.Measure.ae_smul_measure`：ae_smul_measure {p : α -> Prop} [
SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : forallᵐ x ∂μ, p x) (c 
: R) : forallᵐ x ∂c • μ, p …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HasLaw.ae_eq_of_smul_dirac {c : ℝ≥0∞} [MeasurableSingletonClass 𝓧] {x : 𝓧}
    (hX : HasLaw X (c • .dirac x) P) :
    X =ᵐ[P] (fun _ ↦ x) := by
  apply ae_of_ae_map (p := fun y ↦ y = x) hX.aemeasurable
  rw [hX.map_eq]
  apply Measure.ae_smul_measure (by simp)
/-
**ProbabilityTheory.HasLaw.ae_eq_of_dirac** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableS
pace 𝓧} {X : Ω → 𝓧}   {P : MeasureTheory.Measure Ω} [MeasurableSingletonClass 𝓧]
 {x : 𝓧},   ProbabilityTheory.HasLaw X (MeasureTheory.Measure.dirac x) P → X =ᵐ[
P] fun x_1 => x
参数：MeasureTheory.Measure.dirac x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.ae_eq_of_smul_dirac`：∀ {Ω : Type u_1} {𝓧 : Type
 u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {P : Measu
reTheory.Measure Ω} {c : ENNReal} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma HasLaw.ae_eq_of_dirac [MeasurableSingletonClass 𝓧] {x : 𝓧} (hX : HasLaw X (.dirac x) P) :
    X =ᵐ[P] (fun _ ↦ x) :=
  HasLaw.ae_eq_of_smul_dirac (c := 1) (by simpa)
/-
**ProbabilityTheory.hasLaw_smul_dirac_of_ae_eq** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：hasLaw_smul_dirac_of_ae_eq {x : 𝓧} (hX : X =ᵐ[P] fun _ => x) : HasLaw X ((
P Set.univ) • .dirac x) P where aemeasurable
参数：hX : X =ᵐ[P] fun _ => x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.map_const`：map_const (μ : Measure α) (c : β) : μ.m
ap (fun _ => c) = (μ Set.univ) • dirac c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hasLaw_smul_dirac_of_ae_eq {x : 𝓧} (hX : X =ᵐ[P] fun _ ↦ x) :
    HasLaw X ((P Set.univ) • .dirac x) P where
  aemeasurable := aemeasurable_const.congr hX.symm
  map_eq := by
    rw [map_congr hX]
    simp
/-
**ProbabilityTheory.hasLaw_dirac_of_ae_eq** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：hasLaw_dirac_of_ae_eq [IsProbabilityMeasure P] {x : 𝓧} (hX : X =ᵐ[P] fun _
 => x) : HasLaw X (.dirac x) P
参数：hX : X =ᵐ[P] fun _ => x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `ProbabilityTheory.hasLaw_smul_dirac_of_ae_eq`：hasLaw_smul_dirac_of_ae_eq
 {x : 𝓧} (hX : X =ᵐ[P] fun _ => x) : HasLaw X ((P Set.univ) • .dirac x) P where 
aemeasurable
-/
lemma hasLaw_dirac_of_ae_eq [IsProbabilityMeasure P] {x : 𝓧} (hX : X =ᵐ[P] fun _ ↦ x) :
    HasLaw X (.dirac x) P := by
  simpa using hasLaw_smul_dirac_of_ae_eq hX
/-
**ProbabilityTheory.hasLaw_smul_dirac_iff** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：hasLaw_smul_dirac_iff [MeasurableSingletonClass 𝓧] {x : 𝓧} : HasLaw X ((P 
Set.univ) • .dirac x) P ↔ X =ᵐ[P] (fun _ => x) where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.HasLaw.ae_eq_of_smul_dirac`：∀ {Ω : Type u_1} {𝓧 : Type
 u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {P : Measu
reTheory.Measure Ω} {c : ENNReal} …
· 使用引理 `ProbabilityTheory.hasLaw_smul_dirac_of_ae_eq`：hasLaw_smul_dirac_of_ae_eq
 {x : 𝓧} (hX : X =ᵐ[P] fun _ => x) : HasLaw X ((P Set.univ) • .dirac x) P where 
aemeasurable
-/
lemma hasLaw_smul_dirac_iff [MeasurableSingletonClass 𝓧] {x : 𝓧} :
    HasLaw X ((P Set.univ) • .dirac x) P ↔ X =ᵐ[P] (fun _ ↦ x) where
  mp := HasLaw.ae_eq_of_smul_dirac
  mpr := hasLaw_smul_dirac_of_ae_eq
/-
**ProbabilityTheory.hasLaw_dirac_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：hasLaw_dirac_iff [IsProbabilityMeasure P] [MeasurableSingletonClass 𝓧] {x 
: 𝓧} : HasLaw X (.dirac x) P ↔ X =ᵐ[P] (fun _ => x) where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.HasLaw.ae_eq_of_dirac`：∀ {Ω : Type u_1} {𝓧 : Type u_2}
 {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {P : MeasureThe
ory.Measure Ω} [MeasurableSin…
· 使用引理 `ProbabilityTheory.hasLaw_dirac_of_ae_eq`：hasLaw_dirac_of_ae_eq [IsProbab
ilityMeasure P] {x : 𝓧} (hX : X =ᵐ[P] fun _ => x) : HasLaw X (.dirac x) P
-/
lemma hasLaw_dirac_iff [IsProbabilityMeasure P] [MeasurableSingletonClass 𝓧] {x : 𝓧} :
    HasLaw X (.dirac x) P ↔ X =ᵐ[P] (fun _ ↦ x) where
  mp := HasLaw.ae_eq_of_dirac
  mpr := hasLaw_dirac_of_ae_eq
/-
**ProbabilityTheory.indepFun_iff_hasLaw_prodMk_prod** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：indepFun_iff_hasLaw_prodMk_prod [IsFiniteMeasure P] {𝓨 : Type*} {m𝓨 : Meas
urableSpace 𝓨} {ν : Measure 𝓨} {Y : Ω -> 𝓨} (hX : HasLaw X μ P) (hY : HasLaw Y ν
 P) : X ⟂ᵢ[P] Y ↔ HasLaw (fun ω => (X ω, Y ω)) (μ.prod ν) P where mp h
参数：hX : HasLaw X μ P；hY : HasLaw Y ν P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map`：∀ {Ω : Type u_1} {β
 : Type u_6} {β' : Type u_7} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measur
e Ω} {f : Ω → β}   {g : Ω → β'} {mβ : Mea…
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`：indepFun_iff_ma
p_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsFi
niteMeasure μ] (hf : AEMeasurable f μ) (hg : …
-/
lemma indepFun_iff_hasLaw_prodMk_prod [IsFiniteMeasure P] {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
    {ν : Measure 𝓨} {Y : Ω → 𝓨} (hX : HasLaw X μ P) (hY : HasLaw Y ν P) :
    X ⟂ᵢ[P] Y ↔ HasLaw (fun ω ↦ (X ω, Y ω)) (μ.prod ν) P where
  mp h :=
    { map_eq := by
        rw [h.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), hX.map_eq,
          hY.map_eq] }
  mpr h := by
    rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
      h.map_eq, hX.map_eq, hY.map_eq]

alias ⟨IndepFun.hasLaw_prod, _⟩ := indepFun_iff_hasLaw_prodMk_prod
/-
**ProbabilityTheory.iIndepFun.hasLaw_pi** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_3} [inst : Fintype ι]   {𝓧 : ι → Type u_4} {m𝓧 : (i : ι) → MeasurableS
pace (𝓧 i)} {μ : (i : ι) → MeasureTheory.Measure (𝓧 i)}   {X : (i : ι) → Ω → 𝓧 i
},   (∀ (i : ι), ProbabilityTheory.HasLaw (X i) (μ i) P) →     ProbabilityTheory
.iIndepFun X P → ProbabilityTheory.HasLaw (fun ω i => X i ω) (MeasureTheory.Meas
ure.pi μ) P
参数：i : ι；𝓧 i；i : ι；𝓧 i；i : ι；∀ (i : ι), ProbabilityTheory.HasLaw (X i) (μ i) P；f
un ω i => X i ω；MeasureTheory.Measure.pi μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.iIndepFun.map_fun_eq_pi_map`：∀ {Ω : Type u_1} {ι : Typ
e u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Fintype ι
]   {β : ι → Type u_11} {m : (i : ι…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iIndepFun.hasLaw_pi {ι : Type*} [Fintype ι] {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)}
    {μ : (i : ι) → Measure (𝓧 i)} {X : (i : ι) → Ω → 𝓧 i} (hX : ∀ i, HasLaw (X i) (μ i) P)
    (h : iIndepFun X P) :
    HasLaw (fun ω i ↦ X i ω) (Measure.pi μ) P where
  map_eq := by
    rw [h.map_fun_eq_pi_map (by fun_prop)]
    simp_rw [fun i ↦ (hX i).map_eq]
/-
**ProbabilityTheory.iIndepFun_iff_hasLaw_pi_pi** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：iIndepFun_iff_hasLaw_pi_pi [IsProbabilityMeasure P] {ι : Type*} [Fintype ι
] {𝓧 : ι -> Type*} {m𝓧 : forall i, MeasurableSpace (𝓧 i)} {μ : (i : ι) -> Measur
e (𝓧 i)} {X : (i : ι) -> Ω -> 𝓧 i} (hX : forall i, HasLaw (X i) (μ i) P) : iInde
pFun X P ↔ HasLaw (fun ω i => X i ω) (Measure.pi μ) P where mp h
参数：𝓧 i；i : ι；𝓧 i；i : ι；hX : forall i, HasLaw (X i) (μ i) P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.hasLaw_pi`：∀ {Ω : Type u_1} {mΩ : Measurable
Space Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_3} [inst : Fintype ι]   {𝓧 : 
ι → Type u_4} {m𝓧 : (i : ι)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`：iIndepFun_iff_map_fun
_eq_pi_map [Fintype ι] {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)} {f
 : Π i, Ω -> β i} [IsProbabilityMeasure…
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iIndepFun_iff_hasLaw_pi_pi [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {𝓧 : ι → Type*}
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {μ : (i : ι) → Measure (𝓧 i)}
    {X : (i : ι) → Ω → 𝓧 i} (hX : ∀ i, HasLaw (X i) (μ i) P) :
    iIndepFun X P ↔ HasLaw (fun ω i ↦ X i ω) (Measure.pi μ) P where
  mp h := h.hasLaw_pi hX
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (by fun_prop), h.map_eq]
    simp_rw [fun i ↦ (hX i).map_eq]

end ProbabilityTheory

