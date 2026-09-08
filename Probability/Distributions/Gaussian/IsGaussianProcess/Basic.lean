/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Gaussian processes

This file contains basic properties of Gaussian processes. In particular,
in `IsGaussianProcess.of_isGaussianProcess`, we show that if a stochastic
process `Y : S → Ω → F` is such that for each `s : S`, `Y s` can be written as a linear map
applied to finitely many values of a certain Gaussian process,
then `Y` is itself a Gaussian process.

## Main statement

* `IsGaussianProcess.of_isGaussianProcess`: If a stochastic process `Y : S → Ω → F` is such that
  for each `s : S`, `Y s` can be written as a linear map applied to finitely many values
  of a certain Gaussian process, then `Y` is itself a Gaussian process.

## Tags

Gaussian process
-/

public section

open MeasureTheory Finset

namespace ProbabilityTheory.IsGaussianProcess

variable {S T Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

section Basic

/-! ### Basic facts -/

variable [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-
**ProbabilityTheory.IsGaussianProcess.isProbabilityMeasure** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：isProbabilityMeasure (hX : IsGaussianProcess X P) : IsProbabilityMeasure P
参数：hX : IsGaussianProcess X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isProbabilityMeasure`：∀ {Ω : Type u_1} 
{E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : To
pologicalSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`：∀ {Ω : Type u_1} {E 
: Type u_2} {T : Type u_3} {mΩ : MeasurableSpace Ω} [inst : MeasurableSpace E]  
 [inst_1 : TopologicalSpace E] [inst_2 :…
-/
lemma isProbabilityMeasure (hX : IsGaussianProcess X P) :
    IsProbabilityMeasure P :=
  hX.hasGaussianLaw Classical.ofNonempty |>.isProbabilityMeasure
/-
**ProbabilityTheory.IsGaussianProcess.aemeasurable** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.IsGaussianProcess`。
形式化陈述：aemeasurable (hX : IsGaussianProcess X P) (t : T) : AEMeasurable (X t) P
参数：hX : IsGaussianProcess X P；t : T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.eval`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : Measure
Theory.Measure α} {δ : Type u_6} {X : δ → Type u_7}   {mX : (a : δ) → Measurable
Space (…
· 使用定理 `AEMeasurable.of_map_ne_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {f : α → β}   {μ : MeasureTheory.Measure 
α}, MeasureTheory…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …
· 使用定理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`：∀ {Ω : Type u_1} {E 
: Type u_2} {T : Type u_3} {mΩ : MeasurableSpace Ω} [inst : MeasurableSpace E]  
 [inst_1 : TopologicalSpace E] [inst_2 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma aemeasurable (hX : IsGaussianProcess X P) (t : T) : AEMeasurable (X t) P :=
  AEMeasurable.of_map_ne_zero
    (hX.hasGaussianLaw {t}).isGaussian_map.toIsProbabilityMeasure.ne_zero |>.eval ⟨t, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- A modification of a Gaussian process is a Gaussian process. -/
/-
**ProbabilityTheory.IsGaussianProcess.congr** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.IsGaussianProcess`。
形式化陈述：congr (hX : IsGaussianProcess X P) (hXY : forall t, X t =ᵐ[P] Y t) : IsGau
ssianProcess Y P where hasGaussianLaw I
参数：hX : IsGaussianProcess X P；hXY : forall t, X t =ᵐ[P] Y t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.map_restrict_eq_of_forall_ae_eq`：map_restrict_eq_of_fo
rall_ae_eq (h : forall t, X t =ᵐ[P] Y t) (I : Finset T) : P.map (fun ω => I.rest
rict (X · ω)) = P.map (fun ω => I.restr…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …
· 使用定理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`：∀ {Ω : Type u_1} {E 
: Type u_2} {T : Type u_3} {mΩ : MeasurableSpace Ω} [inst : MeasurableSpace E]  
 [inst_1 : TopologicalSpace E] [inst_2 :…

--- 原说明 ---
A modification of a Gaussian process is a Gaussian process.
-/
lemma congr (hX : IsGaussianProcess X P) (hXY : ∀ t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    constructor
    rw [map_restrict_eq_of_forall_ae_eq fun t ↦ (hXY t).symm]
    exact (hX.hasGaussianLaw I).isGaussian_map

end Basic

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

section Maps

/-! ### Gaussian Marginals -/

variable [NormedSpace ℝ E]

/-
**ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_eval** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：hasGaussianLaw_eval (hX : IsGaussianProcess X P) (t : T) : HasGaussianLaw 
(X t) P
参数：hX : IsGaussianProcess X P；t : T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`：∀ {Ω : Type u_1} {E 
: Type u_2} {T : Type u_3} {mΩ : MeasurableSpace Ω} [inst : MeasurableSpace E]  
 [inst_1 : TopologicalSpace E] [inst_2 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hasGaussianLaw_eval (hX : IsGaussianProcess X P) (t : T) : HasGaussianLaw (X t) P := by
  -- removing `by exact` fails
  exact (hX.hasGaussianLaw {t}).map (.proj ⟨t, by simp⟩)

variable [SecondCountableTopology E]
/-
**ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_prodMk** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：hasGaussianLaw_prodMk (hX : IsGaussianProcess X P) {s t : T} : HasGaussian
Law (fun ω => (X s ω, X t ω)) P
参数：hX : IsGaussianProcess X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.prodMk`：prodMk [Finite ι] (hX : HasGaus
sianLaw (fun ω => (X · ω)) P) (i j : ι) : HasGaussianLaw (fun ω => (X i ω, X j ω
)) P
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`：∀ {Ω : Type u_1} {E 
: Type u_2} {T : Type u_3} {mΩ : MeasurableSpace Ω} [inst : MeasurableSpace E]  
 [inst_1 : TopologicalSpace E] [inst_2 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma hasGaussianLaw_prodMk (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (fun ω ↦ (X s ω, X t ω)) P := by
  classical
  exact (hX.hasGaussianLaw {s, t}).prodMk ⟨s, by simp⟩ ⟨t, by simp⟩
/-
**ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_add** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：hasGaussianLaw_add (hX : IsGaussianProcess X P) {s t : T} : HasGaussianLaw
 (X s + X t) P
参数：hX : IsGaussianProcess X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.add`：add (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw (X + Y) P
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_prodMk`：hasGaussianLa
w_prodMk (hX : IsGaussianProcess X P) {s t : T} : HasGaussianLaw (fun ω => (X s 
ω, X t ω)) P
-/
lemma hasGaussianLaw_add (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (X s + X t) P := hX.hasGaussianLaw_prodMk.add
/-
**ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_fun_add** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：hasGaussianLaw_fun_add (hX : IsGaussianProcess X P) {s t : T} : HasGaussia
nLaw (fun ω => X s ω + X t ω) P
参数：hX : IsGaussianProcess X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_add`：hasGaussianLaw_a
dd (hX : IsGaussianProcess X P) {s t : T} : HasGaussianLaw (X s + X t) P
-/
lemma hasGaussianLaw_fun_add (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (fun ω ↦ X s ω + X t ω) P := hX.hasGaussianLaw_add
/-
**ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_sub** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：hasGaussianLaw_sub (hX : IsGaussianProcess X P) {s t : T} : HasGaussianLaw
 (X s - X t) P
参数：hX : IsGaussianProcess X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.sub`：sub (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw (X - Y) P
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_prodMk`：hasGaussianLa
w_prodMk (hX : IsGaussianProcess X P) {s t : T} : HasGaussianLaw (fun ω => (X s 
ω, X t ω)) P
-/
lemma hasGaussianLaw_sub (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (X s - X t) P := hX.hasGaussianLaw_prodMk.sub
/-
**ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_fun_sub** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：hasGaussianLaw_fun_sub (hX : IsGaussianProcess X P) {s t : T} : HasGaussia
nLaw (fun ω => X s ω - X t ω) P
参数：hX : IsGaussianProcess X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_sub`：hasGaussianLaw_s
ub (hX : IsGaussianProcess X P) {s t : T} : HasGaussianLaw (X s - X t) P
-/
lemma hasGaussianLaw_fun_sub (hX : IsGaussianProcess X P) {s t : T} :
    HasGaussianLaw (fun ω ↦ X s ω - X t ω) P := hX.hasGaussianLaw_sub
/-
**ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_sum** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：hasGaussianLaw_sum (hX : IsGaussianProcess X P) {I : Finset T} : HasGaussi
anLaw (∑ i in I, X i) P
参数：hX : IsGaussianProcess X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.HasGaussianLaw.sum`：sum {E : Type*} [NormedAddCommGrou
p E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTop
ology E] {X : ι -> Ω -> E}…
· 使用定理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`：∀ {Ω : Type u_1} {E 
: Type u_2} {T : Type u_3} {mΩ : MeasurableSpace Ω} [inst : MeasurableSpace E]  
 [inst_1 : TopologicalSpace E] [inst_2 :…
-/
lemma hasGaussianLaw_sum (hX : IsGaussianProcess X P) {I : Finset T} :
    HasGaussianLaw (∑ i ∈ I, X i) P := by
  convert! (hX.hasGaussianLaw I).sum
  simp [I.sum_attach X]
/-
**ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_fun_sum** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：hasGaussianLaw_fun_sum (hX : IsGaussianProcess X P) {I : Finset T} : HasGa
ussianLaw (fun ω => ∑ i in I, X i ω) P
参数：hX : IsGaussianProcess X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_sum`：hasGaussianLaw_s
um (hX : IsGaussianProcess X P) {I : Finset T} : HasGaussianLaw (∑ i in I, X i) 
P
-/
lemma hasGaussianLaw_fun_sum (hX : IsGaussianProcess X P) {I : Finset T} :
    HasGaussianLaw (fun ω ↦ ∑ i ∈ I, X i ω) P := by
  convert! hX.hasGaussianLaw_sum (I := I)
  simp

/-- The increments of a Gaussian process are Gaussian. -/
/-
**ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_increments** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：hasGaussianLaw_increments (hX : IsGaussianProcess X P) {n : Nat} {t : Fin 
(n + 1) -> T} : HasGaussianLaw (fun ω (i : Fin n) => X (t i.succ) ω - X (t i.cas
tSucc) ω) P
参数：hX : IsGaussianProcess X P；n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `_private.Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Ba
sic.0.ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_increments._abel_1_1`：∀
 {T : Type u_2} {E : Type u_1} [inst : NormedAddCommGroup E] {n : ℕ} {t : Fin (n
 + 1) → T}   (x y : ↥(Finset.image t Finset.univ) → E) (x_1…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
The increments of a Gaussian process are Gaussian.
-/
lemma hasGaussianLaw_increments (hX : IsGaussianProcess X P) {n : ℕ} {t : Fin (n + 1) → T} :
    HasGaussianLaw (fun ω (i : Fin n) ↦ X (t i.succ) ω - X (t i.castSucc) ω) P := by
  classical
  let L : ((univ.image t) → E) →L[ℝ] Fin n → E :=
    { toFun x i := x ⟨t i.succ, by simp⟩ - x ⟨t i.castSucc, by simp⟩
      map_add' x y := by ext; simp; abel
      map_smul' m x := by ext; simp; module }
  exact (hX.hasGaussianLaw _).map L

end Maps

section Transformations

/-! ### Operations that preserve Gaussianity -/

variable [NormedSpace ℝ E] [SecondCountableTopology E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [SecondCountableTopology F] {Y : S → Ω → F}

/-- If a stochastic process `Y` is such that for each `s`, `Y s` can be written as a linear
combination of finitely many values of a Gaussian process, then `Y` is a Gaussian process. -/
/-
**ProbabilityTheory.IsGaussianProcess.of_isGaussianProcess** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：of_isGaussianProcess (hX : IsGaussianProcess X P) (h : forall s, exists I 
: Finset T, exists L : (I -> E) ->L[Real] F, forall ω, Y s ω = L (I.restrict (X 
· ω))) : IsGaussianProcess Y P where hasGaussianLaw I
参数：hX : IsGaussianProcess X P；h : forall s, exists I : Finset T, exists L : (I -
> E) ->L[Real] F, forall ω, Y s ω = L (I.restrict (X · ω))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`：∀ {Ω : Type u_1} {E 
: Type u_2} {T : Type u_3} {mΩ : MeasurableSpace Ω} [inst : MeasurableSpace E]  
 [inst_1 : TopologicalSpace E] [inst_2 :…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If a stochastic process `Y` is such that for each `s`, `Y s` can be written as a
 linear
combination of finitely many values of a Gaussian process, then `Y` is a Gaussia
n process.
-/
lemma of_isGaussianProcess (hX : IsGaussianProcess X P)
    (h : ∀ s, ∃ I : Finset T, ∃ L : (I → E) →L[ℝ] F, ∀ ω, Y s ω = L (I.restrict (X · ω))) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    choose J L hL using h
    classical
    let K : (I.biUnion J → E) →L[ℝ] I → F :=
      { toFun x s := L s (fun t ↦ x ⟨t.1, mem_biUnion.2 ⟨s.1, s.2, t.2⟩⟩)
        map_add' x y := by ext; simp [← Pi.add_def]
        map_smul' c x := by ext; simp [← Pi.smul_def] }
    have : (fun ω ↦ I.restrict (Y · ω)) = K ∘ (fun ω ↦ (I.biUnion J).restrict (X · ω)) := by
      ext; simp [K, hL, Finset.restrict_def]
    rw [this]
    exact (hX.hasGaussianLaw _).map _
/-
**ProbabilityTheory.IsGaussianProcess.comp_right** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.IsGaussianProcess`。
形式化陈述：comp_right (h : IsGaussianProcess X P) (f : S -> T) : IsGaussianProcess (X
 ∘ f) P
参数：h : IsGaussianProcess X P；f : S -> T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.of_isGaussianProcess`：of_isGaussianP
rocess (hX : IsGaussianProcess X P) (h : forall s, exists I : Finset T, exists L
 : (I -> E) ->L[Real] F, forall ω, Y s ω = L (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
lemma comp_right (h : IsGaussianProcess X P) (f : S → T) : IsGaussianProcess (X ∘ f) P :=
  h.of_isGaussianProcess fun s ↦ ⟨{f s},
    { toFun x := x ⟨f s, by simp⟩
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩
/-
**ProbabilityTheory.IsGaussianProcess.comp_left** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.IsGaussianProcess`。
形式化陈述：comp_left (L : T -> E ->L[Real] F) (h : IsGaussianProcess X P) : IsGaussia
nProcess (fun t ω => L t (X t ω)) P
参数：L : T -> E ->L[Real] F；h : IsGaussianProcess X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.of_isGaussianProcess`：of_isGaussianP
rocess (hX : IsGaussianProcess X P) (h : forall s, exists I : Finset T, exists L
 : (I -> E) ->L[Real] F, forall ω, Y s ω = L (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
lemma comp_left (L : T → E →L[ℝ] F) (h : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω ↦ L t (X t ω)) P :=
  h.of_isGaussianProcess fun t ↦ ⟨{t},
    { toFun x := L t (x ⟨t, by simp⟩),
      map_add' := by simp
      map_smul' := by simp },
    by simp⟩
/-
**ProbabilityTheory.IsGaussianProcess.smul** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.IsGaussianProcess`。
形式化陈述：smul (c : T -> Real) (hX : IsGaussianProcess X P) : IsGaussianProcess (fun
 t ω => c t • (X t ω)) P
参数：c : T -> Real；hX : IsGaussianProcess X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.comp_left`：comp_left (L : T -> E ->L
[Real] F) (h : IsGaussianProcess X P) : IsGaussianProcess (fun t ω => L t (X t ω
)) P
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma smul (c : T → ℝ) (hX : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω ↦ c t • (X t ω)) P :=
  hX.comp_left (fun t ↦ .lsmul ℝ ℝ (c t))
/-
**ProbabilityTheory.IsGaussianProcess.shift** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.IsGaussianProcess`。
形式化陈述：shift [Add T] (h : IsGaussianProcess X P) (t₀ : T) : IsGaussianProcess (fu
n t ω => X (t₀ + t) ω - X t₀ ω) P
参数：h : IsGaussianProcess X P；t₀ : T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.of_isGaussianProcess`：of_isGaussianP
rocess (hX : IsGaussianProcess X P) (h : forall s, exists I : Finset T, exists L
 : (I -> E) ->L[Real] F, forall ω, Y s ω = L (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `_private.Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Ba
sic.0.ProbabilityTheory.IsGaussianProcess.shift._abel_1_1`：∀ {T : Type u_2} {E :
 Type u_1} [inst : NormedAddCommGroup E] [inst_1 : Add T] (t₀ t : T) (x y : ↥{t₀
, t₀ + t} → E),   x ⟨t₀ + t, ⋯⟩ + y ⟨t₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
（共 52 条，此处仅展示前 30 条）
-/
lemma shift [Add T] (h : IsGaussianProcess X P) (t₀ : T) :
    IsGaussianProcess (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) P := by
  classical
  exact h.of_isGaussianProcess fun t ↦ ⟨{t₀, t₀ + t},
    { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
      map_add' x y := by simp; abel
      map_smul' c x := by simp; module },
    by simp⟩
/-
**ProbabilityTheory.IsGaussianProcess.restrict** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.IsGaussianProcess`。
形式化陈述：restrict (h : IsGaussianProcess X P) (s : Set T) : IsGaussianProcess (fun 
t : s => X t) P
参数：h : IsGaussianProcess X P；s : Set T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.comp_right`：comp_right (h : IsGaussi
anProcess X P) (f : S -> T) : IsGaussianProcess (X ∘ f) P
-/
lemma restrict (h : IsGaussianProcess X P) (s : Set T) :
    IsGaussianProcess (fun t : s ↦ X t) P :=
  h.comp_right Subtype.val

end Transformations

end ProbabilityTheory.IsGaussianProcess

