/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Lua Viana Reis
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Birkhoff sum and average for quasi-measure-preserving maps

Given a map `f` and measure `μ`, under the assumption of `QuasiMeasurePreserving f μ μ` we prove:

- `birkhoffSum_ae_eq_of_ae_eq`: if observables  `φ` and `ψ` are `μ`-a.e. equal then the
  corresponding `birkhoffSum f` are `μ`-a.e. equal.

- `birkhoffAverage_ae_eq_of_ae_eq`: if observables `φ` and `ψ` are `μ`-a.e. equal then the
  corresponding `birkhoffAverage R f` are `μ`-a.e. equal.

-/

public section

namespace MeasureTheory.Measure.QuasiMeasurePreserving

open Filter

variable {α M : Type*} [MeasurableSpace α] [AddCommMonoid M]
variable {f : α → α} {μ : Measure α} {φ ψ : α → M}

/-- If observables  `φ` and `ψ` are `μ`-a.e. equal then the corresponding `birkhoffSum` are
`μ`-a.e. equal. -/
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：birkhoffSum_ae_eq_of_ae_eq (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[
μ] ψ) n : birkhoffSum f φ n =ᵐ[μ] birkhoffSum f ψ n
参数：hf : QuasiMeasurePreserving f μ μ；hφ : φ =ᵐ[μ] ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.ae`：ae (h : QuasiMeasurePre
serving f μa μb) {p : β -> Prop} (hg : forallᵐ x ∂μb, p x) : forallᵐ x ∂μa, p (f
 x)
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.iterate`：∀ {α : Type u_1} {
mα : MeasurableSpace α} {μa : MeasureTheory.Measure α} {f : α → α},   MeasureThe
ory.Measure.QuasiMeasurePreserving f μa μa…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
If observables  `φ` and `ψ` are `μ`-a.e. equal then the corresponding `birkhoffS
um` are
`μ`-a.e. equal.
-/
theorem birkhoffSum_ae_eq_of_ae_eq (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] ψ) n :
    birkhoffSum f φ n =ᵐ[μ] birkhoffSum f ψ n := by
  apply Eventually.mono _ (fun _ => Finset.sum_congr rfl)
  apply ae_all_iff.mpr (fun i => ?_)
  exact (hf.iterate i).ae (hφ.mono (fun _ h _ => h))

/-- If observables `φ` and `ψ` are `μ`-a.e. equal then the corresponding `birkhoffAverage` are
`μ`-a.e. equal. -/
/-
**MeasureTheory.Measure.QuasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.QuasiMeasurePreserving`。
形式化陈述：birkhoffAverage_ae_eq_of_ae_eq (R : Type*) [DivisionSemiring R] [Module R 
M] (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] ψ) n : birkhoffAverage R f 
φ n =ᵐ[μ] birkhoffAverage R f ψ n
参数：R : Type*；hf : QuasiMeasurePreserving f μ μ；hφ : φ =ᵐ[μ] ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.const_smul`：∀ {α : Type u} {β : Type v} {γ : Type u_
2} [inst : SMul γ β] {f g : α → β} {l : Filter α},   f =ᶠ[l] g → ∀ (c : γ), c • 
f =ᶠ[l] c • g
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq`
：birkhoffSum_ae_eq_of_ae_eq (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] ψ)
 n : birkhoffSum f φ n =ᵐ[μ] birkhoffSum f ψ n

--- 原说明 ---
If observables `φ` and `ψ` are `μ`-a.e. equal then the corresponding `birkhoffAv
erage` are
`μ`-a.e. equal.
-/
theorem birkhoffAverage_ae_eq_of_ae_eq (R : Type*) [DivisionSemiring R] [Module R M]
    (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] ψ) n :
    birkhoffAverage R f φ n =ᵐ[μ] birkhoffAverage R f ψ n :=
  EventuallyEq.const_smul (birkhoffSum_ae_eq_of_ae_eq hf hφ n) (n : R)⁻¹

end MeasureTheory.Measure.QuasiMeasurePreserving

