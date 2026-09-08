/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Jonas Bayer
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.IdentDistrib

/-!
# Finite-dimensional distributions of a stochastic process

For a stochastic process `X : T → Ω → 𝓧` and a finite measure `P` on `Ω`, the law of the process is
`P.map (fun ω ↦ (X · ω))`, and its finite-dimensional distributions are
`P.map (fun ω ↦ I.restrict (X · ω))` for `I : Finset T`.

We show that two stochastic processes have the same laws if and only if they have the same
finite-dimensional distributions.

## Main statements

* `map_eq_iff_forall_finset_map_restrict_eq`: two processes have the same law if and only if
  their finite-dimensional distributions are equal.
* `identDistrib_iff_forall_finset_identDistrib`: same statement, but stated in terms of
  `IdentDistrib`.
* `map_restrict_eq_of_forall_ae_eq`: if two processes are modifications of each other, then
  their finite-dimensional distributions are equal.
* `map_eq_of_forall_ae_eq`: if two processes are modifications of each other, then they have the
  same law.

-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {T Ω : Type*} {𝓧 : T → Type*} {mΩ : MeasurableSpace Ω} {mα : ∀ t, MeasurableSpace (𝓧 t)}
  {X Y : (t : T) → Ω → 𝓧 t} {P : Measure Ω}

/-- The finite-dimensional distributions of a stochastic process are a projective measure family. -/
/-
**ProbabilityTheory.isProjectiveMeasureFamily_map_restrict** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory`。
形式化陈述：isProjectiveMeasureFamily_map_restrict (hX : forall t, AEMeasurable (X t) 
P) : IsProjectiveMeasureFamily (fun I => P.map (fun ω => I.restrict (X · ω)))
参数：hX : forall t, AEMeasurable (X t) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The finite-dimensional distributions of a stochastic process are a projective me
asure family.
-/
lemma isProjectiveMeasureFamily_map_restrict (hX : ∀ t, AEMeasurable (X t) P) :
    IsProjectiveMeasureFamily (fun I ↦ P.map (fun ω ↦ I.restrict (X · ω))) := by
  intro I J hJI
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict₂ _).aemeasurable]
  · simp [Finset.restrict_def, Finset.restrict₂_def, Function.comp_def]
  · exact aemeasurable_pi_lambda _ fun _ ↦ hX _

/-- The projective limit of the finite-dimensional distributions of a stochastic process is the law
of the process. -/
/-
**ProbabilityTheory.isProjectiveLimit_map** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：isProjectiveLimit_map (hX : AEMeasurable (fun ω => (X · ω)) P) : IsProject
iveLimit (P.map (fun ω => (X · ω))) (fun I => P.map (fun ω => I.restrict (X · ω)
))
参数：hX : AEMeasurable (fun ω => (X · ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)

--- 原说明 ---
The projective limit of the finite-dimensional distributions of a stochastic pro
cess is the law
of the process.
-/
lemma isProjectiveLimit_map (hX : AEMeasurable (fun ω ↦ (X · ω)) P) :
    IsProjectiveLimit (P.map (fun ω ↦ (X · ω))) (fun I ↦ P.map (fun ω ↦ I.restrict (X · ω))) := by
  intro I
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable hX,
    Function.comp_def]

/-- Two stochastic processes have same law iff they have the same
finite-dimensional distributions. -/
/-
**ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：map_eq_iff_forall_finset_map_restrict_eq [IsFiniteMeasure P] (hX : AEMeasu
rable (fun ω => (X · ω)) P) (hY : AEMeasurable (fun ω => (Y · ω)) P) : P.map (fu
n ω => (X · ω)) = P.map (fun ω => (Y · ω)) ↔ forall I : Finset T, P.map (fun ω =
> I.restrict (X · ω)) = P.map (fun ω => I.restrict (Y · ω))
参数：hX : AEMeasurable (fun ω => (X · ω)) P；hY : AEMeasurable (fun ω => (Y · ω)) P
。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用引理 `ProbabilityTheory.isProjectiveLimit_map`：isProjectiveLimit_map (hX : AEM
easurable (fun ω => (X · ω)) P) : IsProjectiveLimit (P.map (fun ω => (X · ω))) (
fun I => P.map (fun ω => I.re…
· 使用定理 `MeasureTheory.IsProjectiveLimit.unique`：unique [forall i, IsFiniteMeasur
e (P i)] (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) : μ = ν
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Two stochastic processes have same law iff they have the same
finite-dimensional distributions.
-/
lemma map_eq_iff_forall_finset_map_restrict_eq [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω ↦ (X · ω)) P) (hY : AEMeasurable (fun ω ↦ (Y · ω)) P) :
    P.map (fun ω ↦ (X · ω)) = P.map (fun ω ↦ (Y · ω))
    ↔ ∀ I : Finset T, P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)) := by
  refine ⟨fun h I ↦ ?_, fun h ↦ ?_⟩
  · have hX' : P.map (fun ω ↦ I.restrict (X · ω)) = (P.map (fun ω ↦ (X · ω))).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX, Function.comp_def]
    have hY' : P.map (fun ω ↦ I.restrict (Y · ω)) = (P.map (fun ω ↦ (Y · ω))).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hY, Function.comp_def]
    rw [hX', hY', h]
  · have hX' := isProjectiveLimit_map hX
    simp_rw [h] at hX'
    exact hX'.unique (isProjectiveLimit_map hY)

/-- Two stochastic processes are identically distributed iff they have the same
finite-dimensional distributions. -/
/-
**ProbabilityTheory.identDistrib_iff_forall_finset_identDistrib** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：identDistrib_iff_forall_finset_identDistrib [IsFiniteMeasure P] (hX : AEMe
asurable (fun ω => (X · ω)) P) (hY : AEMeasurable (fun ω => (Y · ω)) P) : IdentD
istrib (fun ω => (X · ω)) (fun ω => (Y · ω)) P P ↔ forall I : Finset T, IdentDis
trib (fun ω => I.restrict (X · ω)) (fun ω => I.restrict (Y · ω)) P P
参数：hX : AEMeasurable (fun ω => (X · ω)) P；hY : AEMeasurable (fun ω => (Y · ω)) P
。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq`：map_eq_iff_f
orall_finset_map_restrict_eq [IsFiniteMeasure P] (hX : AEMeasurable (fun ω => (X
 · ω)) P) (hY : AEMeasurable (fun ω => (Y · ω)) …
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Two stochastic processes are identically distributed iff they have the same
finite-dimensional distributions.
-/
lemma identDistrib_iff_forall_finset_identDistrib [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω ↦ (X · ω)) P) (hY : AEMeasurable (fun ω ↦ (Y · ω)) P) :
    IdentDistrib (fun ω ↦ (X · ω)) (fun ω ↦ (Y · ω)) P P
      ↔ ∀ I : Finset T,
        IdentDistrib (fun ω ↦ I.restrict (X · ω)) (fun ω ↦ I.restrict (Y · ω)) P P := by
  refine ⟨fun h I ↦ ⟨?_, ?_, ?_⟩, fun h ↦ ⟨hX, hY, ?_⟩⟩
  · exact (Finset.measurable_restrict _).comp_aemeasurable hX
  · exact (Finset.measurable_restrict _).comp_aemeasurable hY
  · exact (map_eq_iff_forall_finset_map_restrict_eq hX hY).mp h.map_eq I
  · exact (map_eq_iff_forall_finset_map_restrict_eq hX hY).mpr (fun I ↦ (h I).map_eq)

/-- If two processes are modifications of each other, then they have the same finite-dimensional
distributions. -/
/-
**ProbabilityTheory.map_restrict_eq_of_forall_ae_eq** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：map_restrict_eq_of_forall_ae_eq (h : forall t, X t =ᵐ[P] Y t) (I : Finset 
T) : P.map (fun ω => I.restrict (X · ω)) = P.map (fun ω => I.restrict (Y · ω))
参数：h : forall t, X t =ᵐ[P] Y t；I : Finset T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
If two processes are modifications of each other, then they have the same finite
-dimensional
distributions.
-/
lemma map_restrict_eq_of_forall_ae_eq (h : ∀ t, X t =ᵐ[P] Y t) (I : Finset T) :
    P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)) := by
  have h' : ∀ᵐ ω ∂P, ∀ (i : I), X i ω = Y i ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun i ↦ h i
  refine Measure.map_congr ?_
  filter_upwards [h'] with ω h using funext h

/-- If two processes are modifications of each other, then they have the same distribution. -/
/-
**ProbabilityTheory.map_eq_of_forall_ae_eq** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：map_eq_of_forall_ae_eq [IsFiniteMeasure P] (hX : AEMeasurable (fun ω => (X
 · ω)) P) (hY : AEMeasurable (fun ω => (Y · ω)) P) (h : forall t, X t =ᵐ[P] Y t)
 : P.map (fun ω => (X · ω)) = P.map (fun ω => (Y · ω))
参数：hX : AEMeasurable (fun ω => (X · ω)) P；hY : AEMeasurable (fun ω => (Y · ω)) P
；h : forall t, X t =ᵐ[P] Y t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq`：map_eq_iff_f
orall_finset_map_restrict_eq [IsFiniteMeasure P] (hX : AEMeasurable (fun ω => (X
 · ω)) P) (hY : AEMeasurable (fun ω => (Y · ω)) …
· 使用引理 `ProbabilityTheory.map_restrict_eq_of_forall_ae_eq`：map_restrict_eq_of_fo
rall_ae_eq (h : forall t, X t =ᵐ[P] Y t) (I : Finset T) : P.map (fun ω => I.rest
rict (X · ω)) = P.map (fun ω => I.restr…

--- 原说明 ---
If two processes are modifications of each other, then they have the same distri
bution.
-/
lemma map_eq_of_forall_ae_eq [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω ↦ (X · ω)) P) (hY : AEMeasurable (fun ω ↦ (Y · ω)) P)
    (h : ∀ t, X t =ᵐ[P] Y t) :
    P.map (fun ω ↦ (X · ω)) = P.map (fun ω ↦ (Y · ω)) := by
  rw [map_eq_iff_forall_finset_map_restrict_eq hX hY]
  exact fun I ↦ map_restrict_eq_of_forall_ae_eq h I

end ProbabilityTheory

