/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi

/-!
# Results about identically distributed random variables and independence

## Main statements

* `IdentDistrib.prodMk`: if `X` and `Y` are independent random variables on `Ω`, `Z` and `W` are
  independent random variables on `Ω'`, such that `X` and `Z` are identically distributed
  and `Y` and `W` are identically distributed, then the pairs `(X, Y)` and `(Z, W)` are
  identically distributed.
* `IdentDistrib.pi`: if `(X i)` and `(Y i)` are families of independent random variables indexed by
  a countable type `ι`, such that for each `i`, `X i` and `Y i` are identically distributed, then
  the products `X` and `Y` are identically distributed.

-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω Ω' ι E F : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {mE : MeasurableSpace E} {mF : MeasurableSpace F}
    {μ : Measure Ω} {ν : Measure Ω'}

/-- If `X` and `Y` are independent random variables on `Ω`, `Z` and `W` are independent random
variables on `Ω'`, such that `X` and `Z` are identically distributed and `Y` and `W` are identically
distributed, then the pairs `(X, Y)`  and `(Z, W)` are identically distributed. -/
/-
**ProbabilityTheory.IdentDistrib.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.IdentDistrib`。
形式化陈述：∀ {Ω : Type u_1} {Ω' : Type u_2} {E : Type u_4} {F : Type u_5} {mΩ : Measu
rableSpace Ω} {mΩ' : MeasurableSpace Ω'}   {mE : MeasurableSpace E} {mF : Measur
ableSpace F} {μ : MeasureTheory.Measure Ω} {ν : MeasureTheory.Measure Ω'}   [Mea
sureTheory.IsFiniteMeasure μ] {X : Ω → E} {Y : Ω → F} {Z : Ω' → E} {W : Ω' → F},
   ProbabilityTheory.IdentDistrib X Z μ ν →     ProbabilityTheory.IdentDistrib Y
 W μ ν →       ProbabilityTheory.IndepFun X Y μ →         ProbabilityTheory.Inde
pFun Z W ν →           ProbabilityTheory.IdentDistrib (fun ω => (X ω, Y ω)) (fun
 ω' => (Z ω', W ω')) μ ν
参数：fun ω => (X ω, Y ω)；fun ω' => (Z ω', W ω')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_of_map`：∀ {α : Type u_1} {β : Type
 u_2} {m0 : MeasurableSpace α} [mβ : MeasurableSpace β] {μ : MeasureTheory.Measu
re α}   {f : α → β},   AEMeasurabl…
· 使用定理 `ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map`：∀ {Ω : Type u_1} {β
 : Type u_6} {β' : Type u_7} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measur
e Ω} {f : Ω → β}   {g : Ω → β'} {mβ : Mea…

--- 原说明 ---
If `X` and `Y` are independent random variables on `Ω`, `Z` and `W` are independ
ent random
variables on `Ω'`, such that `X` and `Z` are identically distributed and `Y` and
 `W` are identically
distributed, then the pairs `(X, Y)`  and `(Z, W)` are identically distributed.
-/
lemma IdentDistrib.prodMk [IsFiniteMeasure μ]
    {X : Ω → E} {Y : Ω → F} {Z : Ω' → E} {W : Ω' → F}
    (hXZ : IdentDistrib X Z μ ν) (hYW : IdentDistrib Y W μ ν)
    (hXY : X ⟂ᵢ[μ] Y) (hZW : Z ⟂ᵢ[ν] W) :
    IdentDistrib (fun ω ↦ (X ω, Y ω)) (fun ω' ↦ (Z ω', W ω')) μ ν where
  aemeasurable_fst := hXZ.aemeasurable_fst.prodMk hYW.aemeasurable_fst
  aemeasurable_snd := hXZ.aemeasurable_snd.prodMk hYW.aemeasurable_snd
  map_eq := by
    have : IsFiniteMeasure ν := by
      have : IsFiniteMeasure (ν.map Z) := by rw [← hXZ.map_eq]; infer_instance
      exact Measure.isFiniteMeasure_of_map hXZ.aemeasurable_snd
    rw [hXY.map_prod_eq_prod_map_map hXZ.aemeasurable_fst hYW.aemeasurable_fst,
      hZW.map_prod_eq_prod_map_map hXZ.aemeasurable_snd hYW.aemeasurable_snd,
      hXZ.map_eq, hYW.map_eq]

/-- If `(X i)` and `(Y i)` are families of independent random variables indexed by a countable
type `ι`, such that for each `i`, `X i` and `Y i` are identically distributed, then the products
`X` and `Y` are identically distributed. -/
/-
**ProbabilityTheory.IdentDistrib.pi** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.IdentDistrib`。
形式化陈述：∀ {Ω : Type u_1} {Ω' : Type u_2} {ι : Type u_3} {mΩ : MeasurableSpace Ω} {
mΩ' : MeasurableSpace Ω'}   {μ : MeasureTheory.Measure Ω} {ν : MeasureTheory.Mea
sure Ω'} [Countable ι] {E : ι → Type u_6}   {mE : (i : ι) → MeasurableSpace (E i
)} {X : (i : ι) → Ω → E i} {Y : (i : ι) → Ω' → E i},   (∀ (i : ι), ProbabilityTh
eory.IdentDistrib (X i) (Y i) μ ν) →     ProbabilityTheory.iIndepFun X μ →      
 ProbabilityTheory.iIndepFun Y ν → ProbabilityTheory.IdentDistrib (fun ω x => X 
x ω) (fun ω x => Y x ω) μ ν
参数：i : ι；E i；i : ι；i : ι；∀ (i : ι), ProbabilityTheory.IdentDistrib (X i) (Y i) μ
 ν；fun ω x => X x ω；fun ω x => Y x ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map₀'`：iIndepFun_i
ff_map_fun_eq_infinitePi_map₀' [IsProbabilityMeasure P] [Countable ι] (mX : fora
ll i, AEMeasurable (X i) P) : iIndepFun X P ↔ P.m…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…

--- 原说明 ---
If `(X i)` and `(Y i)` are families of independent random variables indexed by a
 countable
type `ι`, such that for each `i`, `X i` and `Y i` are identically distributed, t
hen the products
`X` and `Y` are identically distributed.
-/
lemma IdentDistrib.pi [Countable ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {X : (i : ι) → Ω → E i} {Y : (i : ι) → Ω' → E i}
    (h : ∀ i, IdentDistrib (X i) (Y i) μ ν) (hX_ind : iIndepFun X μ) (hY_ind : iIndepFun Y ν) :
    IdentDistrib (fun ω ↦ (X · ω)) (fun ω ↦ (Y · ω)) μ ν where
  aemeasurable_fst := aemeasurable_pi_lambda _ fun i ↦ (h i).aemeasurable_fst
  aemeasurable_snd := aemeasurable_pi_lambda _ fun i ↦ (h i).aemeasurable_snd
  map_eq := by
    have : IsProbabilityMeasure μ := hX_ind.isProbabilityMeasure
    have : IsProbabilityMeasure ν := hY_ind.isProbabilityMeasure
    rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun i ↦ (h i).aemeasurable_fst)).mp hX_ind,
      (iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun i ↦ (h i).aemeasurable_snd)).mp hY_ind]
    congr with i
    rw [(h i).map_eq]

end ProbabilityTheory

