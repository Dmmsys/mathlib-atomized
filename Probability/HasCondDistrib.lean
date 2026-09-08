/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/

module

public import Mathlib.Probability.HasLaw

import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# A predicate for having a specified conditional distribution

We introduce a predicate `HasCondDistrib Y X κ P` stating that the conditional distribution of `Y`
given `X` under the measure `P` is equal to the kernel `κ`.
The statement uses `HasLaw` to express that the law of the pair `(X, Y)` under `P` is equal to
`(P.map X) ⊗ₘ κ`, the product of the law of `X` under `P` and the kernel `κ`.
The use of `HasLaw` also implies that `Y` and `X` are a.e. measurable.

## Main definitions

* `HasCondDistrib Y X κ P` : predicate stating that the conditional distribution of `Y` given `X`
  under the measure `P` is equal to the kernel `κ`.

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}
  {P : Measure Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : Kernel 𝓧 𝓨}

/-- Predicate stating that the conditional distribution of `Y` given `X` under the measure `P`
is equal to the kernel `κ`. -/
/-
**ProbabilityTheory.HasCondDistrib** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`
。
形式化陈述：HasCondDistrib (Y : Ω -> 𝓨) (X : Ω -> 𝓧) (κ : Kernel 𝓧 𝓨) (P : Measure Ω) 
: Prop
参数：Y : Ω -> 𝓨；X : Ω -> 𝓧；κ : Kernel 𝓧 𝓨；P : Measure Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate stating that the conditional distribution of `Y` given `X` under the m
easure `P`
is equal to the kernel `κ`.
-/
def HasCondDistrib (Y : Ω → 𝓨) (X : Ω → 𝓧) (κ : Kernel 𝓧 𝓨) (P : Measure Ω) : Prop :=
  HasLaw (fun ω ↦ (X ω, Y ω)) ((P.map X) ⊗ₘ κ) P

@[fun_prop]
/-
**ProbabilityTheory.HasCondDistrib.aemeasurable_fst** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.HasCondDistrib`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m
𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {P : MeasureTheory.Measure Ω} 
{X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : ProbabilityTheory.Kernel 𝓧 𝓨},   ProbabilityTheory.
HasCondDistrib Y X κ P → AEMeasurable X P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
-/
lemma HasCondDistrib.aemeasurable_fst (h : HasCondDistrib Y X κ P) :
    AEMeasurable X P := h.aemeasurable.fst

@[fun_prop]
/-
**ProbabilityTheory.HasCondDistrib.aemeasurable_snd** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.HasCondDistrib`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m
𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {P : MeasureTheory.Measure Ω} 
{X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : ProbabilityTheory.Kernel 𝓧 𝓨},   ProbabilityTheory.
HasCondDistrib Y X κ P → AEMeasurable Y P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `ProbabilityTheory.HasLaw.aemeasurable`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {
mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheor
y.Measure 𝓧} {P : autoParam…
-/
lemma HasCondDistrib.aemeasurable_snd (h : HasCondDistrib Y X κ P) :
    AEMeasurable Y P := h.aemeasurable.snd
/-
**ProbabilityTheory.HasLaw.prodMk_of_hasCondDistrib** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m
𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {P : MeasureTheory.Measure Ω} 
{X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : ProbabilityTheory.Kernel 𝓧 𝓨}   {Q : MeasureTheory.
Measure 𝓧},   ProbabilityTheory.HasLaw X Q P →     ProbabilityTheory.HasCondDist
rib Y X κ P → ProbabilityTheory.HasLaw (fun ω => (X ω, Y ω)) (Q.compProd κ) P
参数：fun ω => (X ω, Y ω)；Q.compProd κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
-/
lemma HasLaw.prodMk_of_hasCondDistrib {Q : Measure 𝓧}
    (h1 : HasLaw X Q P) (h2 : HasCondDistrib Y X κ P) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (Q ⊗ₘ κ) P := by rwa [← h1.map_eq]
/-
**ProbabilityTheory.HasCondDistrib.hasLaw_of_const** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.HasCondDistrib`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m
𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {P : MeasureTheory.Measure Ω} 
{X : Ω → 𝓧} {Y : Ω → 𝓨} [MeasureTheory.IsProbabilityMeasure P]   {Q : MeasureThe
ory.Measure 𝓨} [MeasureTheory.SFinite Q],   ProbabilityTheory.HasCondDistrib Y X
 (ProbabilityTheory.Kernel.const 𝓧 Q) P → ProbabilityTheory.HasLaw Y Q P
参数：ProbabilityTheory.Kernel.const 𝓧 Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasCondDistrib.aemeasurable_snd`：∀ {Ω : Type u_1} {𝓧 :
 Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m
𝓨 : MeasurableSpace 𝓨} {P : MeasureTheo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.const_comp`：const_comp {ν : Measure β} : (Kernel.c
onst α ν) ∘ₘ μ = μ Set.univ • ν
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `ProbabilityTheory.HasCondDistrib.aemeasurable_fst`：∀ {Ω : Type u_1} {𝓧 :
 Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m
𝓨 : MeasurableSpace 𝓨} {P : MeasureTheo…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.snd_map_prodMk₀`：snd_map_prodMk₀ {X : α -> β} {Y :
 α -> γ} {μ : Measure α} (hX : AEMeasurable X μ) : (μ.map fun a => (X a, Y a)).s
nd = μ.map Y
-/
lemma HasCondDistrib.hasLaw_of_const [IsProbabilityMeasure P] {Q : Measure 𝓨} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const 𝓧 Q) P) :
    HasLaw Y Q P where
  map_eq := by
    have h_snd : (P.map (fun ω ↦ (X ω, Y ω))).snd = Q := by
      rw [h.map_eq, Measure.snd_compProd]
      simp [Measure.map_apply_of_aemeasurable h.aemeasurable_fst]
    rwa [Measure.snd_map_prodMk₀ h.aemeasurable_fst] at h_snd

variable [SFinite P] [IsSFiniteKernel κ]
/-
**ProbabilityTheory.HasCondDistrib.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.HasCondDistrib`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {𝓩 : Type u_4} {mΩ : Measur
ableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : Measurabl
eSpace 𝓩} {P : MeasureTheory.Measure Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨}   {κ : Probabili
tyTheory.Kernel 𝓧 𝓨} [MeasureTheory.SFinite P] [ProbabilityTheory.IsSFiniteKerne
l κ],   ProbabilityTheory.HasCondDistrib Y X κ P →     ∀ {f : 𝓨 → 𝓩}, Measurable
 f → ProbabilityTheory.HasCondDistrib (f ∘ Y) X (κ.map f) P
参数：f ∘ Y；κ.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `ProbabilityTheory.HasCondDistrib.aemeasurable_fst`：∀ {Ω : Type u_1} {𝓧 :
 Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m
𝓨 : MeasurableSpace 𝓨} {P : MeasureTheo…
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `ProbabilityTheory.HasCondDistrib.aemeasurable_snd`：∀ {Ω : Type u_1} {𝓧 :
 Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m
𝓨 : MeasurableSpace 𝓨} {P : MeasureTheo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用引理 `MeasureTheory.Measure.compProd_map`：compProd_map [SFinite μ] [IsSFiniteK
ernel κ] {f : β -> γ} (hf : Measurable f) : μ otimesₘ (κ.map f) = (μ otimesₘ κ).
map (Prod.map id f)
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
-/
lemma HasCondDistrib.comp_left (h : HasCondDistrib Y X κ P) {f : 𝓨 → 𝓩} (hf : Measurable f) :
    HasCondDistrib (f ∘ Y) X (κ.map f) P where
  map_eq := calc
    P.map (fun ω ↦ (X ω, f (Y ω)))
    _ = (P.map (fun ω ↦ (X ω, Y ω))).map (Prod.map id f) := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      congr
    _ = (P.map X ⊗ₘ κ).map (Prod.map id f) := by rw [h.map_eq]
    _ = P.map X ⊗ₘ κ.map f := by rw [Measure.compProd_map hf]
/-
**ProbabilityTheory.HasCondDistrib.fst** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.HasCondDistrib`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {𝓩 : Type u_4} {mΩ : Measur
ableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : Measurabl
eSpace 𝓩} {P : MeasureTheory.Measure Ω} {X : Ω → 𝓧} [MeasureTheory.SFinite P]   
{Y : Ω → 𝓨 × 𝓩} {κ : ProbabilityTheory.Kernel 𝓧 (𝓨 × 𝓩)} [ProbabilityTheory.IsSF
initeKernel κ],   ProbabilityTheory.HasCondDistrib Y X κ P → ProbabilityTheory.H
asCondDistrib (fun ω => (Y ω).1) X κ.fst P
参数：𝓨 × 𝓩；fun ω => (Y ω).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_eq`：fst_eq (κ : Kernel α (β × γ)) : fst κ =
 map κ Prod.fst
· 使用定理 `ProbabilityTheory.HasCondDistrib.comp_left`：∀ {Ω : Type u_1} {𝓧 : Type u
_2} {𝓨 : Type u_3} {𝓩 : Type u_4} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace
 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
lemma HasCondDistrib.fst {Y : Ω → 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)} [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ (Y ω).1) X κ.fst P := by
  rw [Kernel.fst_eq]
  exact h.comp_left measurable_fst
/-
**ProbabilityTheory.HasCondDistrib.snd** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.HasCondDistrib`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {𝓩 : Type u_4} {mΩ : Measur
ableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : Measurabl
eSpace 𝓩} {P : MeasureTheory.Measure Ω} {X : Ω → 𝓧} [MeasureTheory.SFinite P]   
{Y : Ω → 𝓨 × 𝓩} {κ : ProbabilityTheory.Kernel 𝓧 (𝓨 × 𝓩)} [ProbabilityTheory.IsSF
initeKernel κ],   ProbabilityTheory.HasCondDistrib Y X κ P → ProbabilityTheory.H
asCondDistrib (fun ω => (Y ω).2) X κ.snd P
参数：𝓨 × 𝓩；fun ω => (Y ω).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.snd_eq`：snd_eq (κ : Kernel α (β × γ)) : snd κ =
 map κ Prod.snd
· 使用定理 `ProbabilityTheory.HasCondDistrib.comp_left`：∀ {Ω : Type u_1} {𝓧 : Type u
_2} {𝓨 : Type u_3} {𝓩 : Type u_4} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace
 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
lemma HasCondDistrib.snd {Y : Ω → 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)} [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ (Y ω).2) X κ.snd P := by
  rw [Kernel.snd_eq]
  exact h.comp_left measurable_snd
/-
**ProbabilityTheory.HasCondDistrib.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.HasCondDistrib`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {𝓩 : Type u_4} {mΩ : Measur
ableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : Measurabl
eSpace 𝓩} {P : MeasureTheory.Measure Ω} {Y : Ω → 𝓨}   {κ : ProbabilityTheory.Ker
nel 𝓧 𝓨} [MeasureTheory.SFinite P] [ProbabilityTheory.IsSFiniteKernel κ] {f : 𝓩 
→ 𝓧}   {hf : Measurable f} {Z : Ω → 𝓩},   ProbabilityTheory.HasCondDistrib Y Z (
κ.comap f hf) P → ProbabilityTheory.HasCondDistrib Y (f ∘ Z) κ P
参数：κ.comap f hf；f ∘ Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `ProbabilityTheory.HasCondDistrib.aemeasurable_fst`：∀ {Ω : Type u_1} {𝓧 :
 Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m
𝓨 : MeasurableSpace 𝓨} {P : MeasureTheo…
· 使用定理 `ProbabilityTheory.HasCondDistrib.aemeasurable_snd`：∀ {Ω : Type u_1} {𝓧 :
 Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m
𝓨 : MeasurableSpace 𝓨} {P : MeasureTheo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
· 使用定理 `measurableSet_preimage`：measurableSet_preimage {t : Set β} (hf : Measura
ble f) (ht : MeasurableSet t) : MeasurableSet (f ⁻¹' t)
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`：measurable_kerne
l_prodMk_left [IsSFiniteKernel κ] {t : Set (α × β)} (ht : MeasurableSet t) : Mea
surable fun a => κ a (Prod.mk a ⁻¹' t)
-/
lemma HasCondDistrib.comp_right {f : 𝓩 → 𝓧}
    {hf : Measurable f} {Z : Ω → 𝓩} (h : HasCondDistrib Y Z (κ.comap f hf) P) :
    HasCondDistrib Y (f ∘ Z) κ P where
  map_eq := calc
    P.map (fun a ↦ ((f ∘ Z) a, Y a))
    _ = (P.map (fun a ↦ (Z a, Y a))).map (Prod.map f id) := by
        rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
        rfl
    _ = (P.map Z ⊗ₘ κ.comap f hf).map (Prod.map f id) := by rw [h.map_eq]
    _ = (P.map Z).map f ⊗ₘ κ := by
        ext s hs
        rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply (by measurability),
          Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
        rfl
    _ = P.map (f ∘ Z) ⊗ₘ κ := by
        rw [AEMeasurable.map_map_of_aemeasurable hf.aemeasurable (by fun_prop)]
/-
**ProbabilityTheory.HasCondDistrib.measurableEquiv_comp_right** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.HasCondDistrib`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {𝓩 : Type u_4} {mΩ : Measur
ableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : Measurabl
eSpace 𝓩} {P : MeasureTheory.Measure Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨}   {κ : Probabili
tyTheory.Kernel 𝓧 𝓨} [MeasureTheory.SFinite P] [ProbabilityTheory.IsSFiniteKerne
l κ],   ProbabilityTheory.HasCondDistrib Y X κ P →     ∀ (f : 𝓧 ≃ᵐ 𝓩), Probabili
tyTheory.HasCondDistrib Y (⇑f ∘ X) (κ.comap ⇑f.symm ⋯) P
参数：f : 𝓧 ≃ᵐ 𝓩；⇑f ∘ X；κ.comap ⇑f.symm ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasCondDistrib.comp_right`：∀ {Ω : Type u_1} {𝓧 : Type 
u_2} {𝓨 : Type u_3} {𝓩 : Type u_4} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpac
e 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {…
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableEquiv.symm_comp_self`：symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e
 = id
· 使用定理 `ProbabilityTheory.Kernel.comap.congr_simp`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Meas
urableSpace γ} (κ κ_1 : Probabi…
· 使用引理 `ProbabilityTheory.Kernel.comap_id`：comap_id (κ : Kernel α β) : comap κ i
d measurable_id = κ
-/
lemma HasCondDistrib.measurableEquiv_comp_right (h : HasCondDistrib Y X κ P) (f : 𝓧 ≃ᵐ 𝓩) :
    HasCondDistrib Y (f ∘ X) (κ.comap f.symm f.symm.measurable) P := by
  apply HasCondDistrib.comp_right (hf := f.measurable)
  simpa [← Kernel.comap_comp_right]
/-
**ProbabilityTheory.HasCondDistrib.of_compProd** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.HasCondDistrib`。
形式化陈述：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {𝓩 : Type u_4} {mΩ : Measur
ableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : Measurabl
eSpace 𝓩} {P : MeasureTheory.Measure Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨}   {κ : Probabili
tyTheory.Kernel 𝓧 𝓨} [MeasureTheory.SFinite P] [ProbabilityTheory.IsSFiniteKerne
l κ] {Z : Ω → 𝓩}   {η : ProbabilityTheory.Kernel (𝓧 × 𝓨) 𝓩} [ProbabilityTheory.I
sMarkovKernel η],   ProbabilityTheory.HasCondDistrib (fun a => (Y a, Z a)) X (κ.
compProd η) P →     ProbabilityTheory.HasCondDistrib Z (fun a => (X a, Y a)) η P
参数：𝓧 × 𝓨；fun a => (Y a, Z a)；κ.compProd η；fun a => (X a, Y a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `ProbabilityTheory.HasCondDistrib.aemeasurable_snd`：∀ {Ω : Type u_1} {𝓧 :
 Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m
𝓨 : MeasurableSpace 𝓨} {P : MeasureTheo…
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `ProbabilityTheory.HasCondDistrib.aemeasurable_fst`：∀ {Ω : Type u_1} {𝓧 :
 Type u_2} {𝓨 : Type u_3} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   {m
𝓨 : MeasurableSpace 𝓨} {P : MeasureTheo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用引理 `MeasureTheory.Measure.compProd_assoc`：compProd_assoc {γ : Type*} {mγ : M
easurableSpace γ} {η : Kernel (α × β) γ} : (μ otimesₘ (κ otimesₖ η)).map Measura
bleEquiv.prodAssoc.symm = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.HasCondDistrib.fst`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {𝓨
 : Type u_3} {𝓩 : Type u_4} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}   
{m𝓨 : MeasurableSpace 𝓨} {…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.compProd`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} (κ : Probability…
· 使用引理 `ProbabilityTheory.Kernel.fst_compProd`：fst_compProd (κ : Kernel α β) (η 
: Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] : fst (κ otimesₖ η) =
 κ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HasCondDistrib.of_compProd {Z : Ω → 𝓩} {η : Kernel (𝓧 × 𝓨) 𝓩} [IsMarkovKernel η]
    (h : HasCondDistrib (fun a ↦ (Y a, Z a)) X (κ ⊗ₖ η) P) :
    HasCondDistrib Z (fun a ↦ (X a, Y a)) η P := by
  have hZ : AEMeasurable Z P := h.aemeasurable_snd.snd
  have hY : AEMeasurable Y P := h.aemeasurable_snd.fst
  refine ⟨by fun_prop, ?_⟩
  calc P.map (fun a ↦ ((X a, Y a), Z a))
  _ = (P.map X ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm := by
      rw [← h.map_eq, AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      rfl
  _ = P.map X ⊗ₘ κ ⊗ₘ η := Measure.compProd_assoc
  _ = P.map (fun a ↦ (X a, Y a)) ⊗ₘ η := by simp [h.fst.map_eq]

end ProbabilityTheory

