/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Existence of Random Variables

This file contains lemmas that state the existence of random variables with given distributions
and a given dependency structure (currently only mutual independence is considered).
-/

public section

open MeasureTheory Measure

namespace ProbabilityTheory

universe u v

/-
**ProbabilityTheory._root_.MeasureTheory.Measure.exists_hasLaw** 是 Mathlib 中的一个引
理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.Measure.exists_hasLaw {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
    (μ : Measure 𝓧) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : Ω → 𝓧,
      Measurable X ∧ HasLaw X μ P :=
  ⟨𝓧, m𝓧, μ, id, measurable_id, .id⟩
/-
**ProbabilityTheory.exists_hasLaw_indepFun** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：exists_hasLaw_indepFun {ι : Type v} (𝓧 : ι -> Type u) {m𝓧 : forall i, Meas
urableSpace (𝓧 i)} (μ : (i : ι) -> Measure (𝓧 i)) [hμ : forall i, IsProbabilityM
easure (μ i)] : exists Ω : Type (max u v), exists _ : MeasurableSpace Ω, exists 
P : Measure Ω, exists X : (i : ι) -> Ω -> (𝓧 i), (forall i, Measurable (X i)) ∧ 
(forall i, HasLaw (X i) (μ i) P) ∧ iIndepFun X P ∧ IsProbabilityMeasure P
参数：𝓧 : ι -> Type u；𝓧 i；μ : (i : ι) -> Measure (𝓧 i)；μ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `MeasureTheory.MeasurePreserving.hasLaw`：∀ {Ω : Type u_1} {𝓧 : Type u_2} 
{mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheo
ry.Measure 𝓧} {P : MeasureTh…
· 使用定理 `measurePreserving_eval_infinitePi`：∀ {ι : Type u_1} {X : ι → Type u_2} {
mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) → MeasureTheory.Measure (X i)
)   [hμ : ∀ (i : ι), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map`：iIndepFun_iff
_map_fun_eq_infinitePi_map [IsProbabilityMeasure P] (mX : forall i, Measurable (
X i)) : iIndepFun X P ↔ P.map (fun ω i => X i ω…
· 使用定理 `MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi`：∀ {ι : T
ype u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) 
→ MeasureTheory.Measure (X i))   [hμ : ∀ (i : ι), Me…
· 使用定理 `MeasureTheory.Measure.map_id'`：map_id' : map (fun x => x) μ = μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
lemma exists_hasLaw_indepFun {ι : Type v} (𝓧 : ι → Type u)
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} (μ : (i : ι) → Measure (𝓧 i))
    [hμ : ∀ i, IsProbabilityMeasure (μ i)] :
    ∃ Ω : Type (max u v), ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : (i : ι) → Ω → (𝓧 i),
      (∀ i, Measurable (X i)) ∧ (∀ i, HasLaw (X i) (μ i) P)
        ∧ iIndepFun X P ∧ IsProbabilityMeasure P := by
  use Π i, (𝓧 i), .pi, infinitePi μ, fun i ↦ Function.eval i
  refine ⟨by fun_prop, fun i ↦ MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi _ _),
    ?_, by infer_instance⟩
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop), map_id']
  congr
  funext i
  exact ((measurePreserving_eval_infinitePi μ i).map_eq).symm
/-
**ProbabilityTheory.exists_iid** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：exists_iid (ι : Type v) {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧} (μ : Measure
 𝓧) [IsProbabilityMeasure μ] : exists Ω : Type (max u v), exists _ : MeasurableS
pace Ω, exists P : Measure Ω, exists X : ι -> Ω -> 𝓧, (forall i, Measurable (X i
)) ∧ (forall i, HasLaw (X i) μ P) ∧ iIndepFun X P ∧ IsProbabilityMeasure P
参数：ι : Type v；μ : Measure 𝓧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.exists_hasLaw_indepFun`：exists_hasLaw_indepFun {ι : Ty
pe v} (𝓧 : ι -> Type u) {m𝓧 : forall i, MeasurableSpace (𝓧 i)} (μ : (i : ι) -> M
easure (𝓧 i)) [hμ : forall i, …
-/
lemma exists_iid (ι : Type v) {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] :
    ∃ Ω : Type (max u v), ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : ι → Ω → 𝓧,
      (∀ i, Measurable (X i)) ∧ (∀ i, HasLaw (X i) μ P) ∧ iIndepFun X P ∧ IsProbabilityMeasure P :=
  exists_hasLaw_indepFun (fun _ ↦ 𝓧) (fun _ ↦ μ)

end ProbabilityTheory

