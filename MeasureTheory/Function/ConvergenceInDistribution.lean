/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.IdentDistrib

/-!
# Convergence in distribution

We introduce a definition of convergence in distribution of random variables: this is the
weak convergence of the laws of the random variables. In Mathlib terms this is a `Tendsto` in the
`ProbabilityMeasure` type.

We also state results relating convergence in probability (`TendstoInMeasure`)
and convergence in distribution.

## Main definitions

* `TendstoInDistribution X l Z μ`: the sequence of random variables `X n` converges in
  distribution to the random variable `Z` along the filter `l` with respect to the probability
  measure `μ`.

## Main statements

* `TendstoInDistribution.continuous_comp`: **Continuous mapping theorem**.
  If `X n` tends to `Z` in distribution and `g` is continuous, then `g ∘ X n` tends to `g ∘ Z`
  in distribution.
* `tendstoInDistribution_of_tendstoInMeasure_sub`: the main technical tool for the next results.
  Let `X, Y` be two sequences of measurable functions such that `X n` converges in distribution
  to `Z`, and `Y n - X n` converges in probability to `0`.
  Then `Y n` converges in distribution to `Z`.
* `TendstoInMeasure.tendstoInDistribution`: convergence in probability implies convergence in
  distribution.
* `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`: **Slutsky's theorem**.
  If `X n` converges in distribution to `Z`, and `Y n` converges in probability to a constant `c`,
  then the pair `(X n, Y n)` converges in distribution to `(Z, c)`.

-/

public section

open Filter ProbabilityTheory
open scoped Topology

namespace MeasureTheory

variable {ι E Ω' Ω'' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {m'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
  {mE : MeasurableSpace E} {X Y : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι}

section TendstoInDistribution

variable [TopologicalSpace E]

/-- Convergence in distribution of random variables.
This is the weak convergence of the laws of the random variables: `Tendsto` in the
`ProbabilityMeasure` type. -/
/-
**MeasureTheory.TendstoInDistribution** 是 Mathlib 中的一个结构，位于命名空间 `MeasureTheory`。
形式化陈述：TendstoInDistribution [OpensMeasurableSpace E] (X : (i : ι) -> Ω i -> E) (
l : Filter ι) (Z : Ω' -> E) (μ : (i : ι) -> Measure (Ω i)) [forall i, IsProbabil
ityMeasure (μ i)] (μ' : Measure Ω'
参数：X : (i : ι) -> Ω i -> E；l : Filter ι；Z : Ω' -> E；μ : (i : ι) -> Measure (Ω i)
；μ i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convergence in distribution of random variables.
This is the weak convergence of the laws of the random variables: `Tendsto` in t
he
`ProbabilityMeasure` type.
-/
structure TendstoInDistribution [OpensMeasurableSpace E] (X : (i : ι) → Ω i → E) (l : Filter ι)
    (Z : Ω' → E) (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (μ' : Measure Ω' := by volume_tac) [IsProbabilityMeasure μ'] : Prop where
  forall_aemeasurable : ∀ i, AEMeasurable (X i) (μ i)
  aemeasurable_limit : AEMeasurable Z μ' := by fun_prop
  tendsto : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (forall_aemeasurable n)⟩) l
      (𝓝 ⟨μ'.map Z, Measure.isProbabilityMeasure_map aemeasurable_limit⟩)
/-
**MeasureTheory.tendstoInDistribution_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：tendstoInDistribution_const [OpensMeasurableSpace E] (hZ : AEMeasurable Z 
μ') : TendstoInDistribution (fun _ => Z) l Z (fun _ => μ') μ' where forall_aemea
surable
参数：hZ : AEMeasurable Z μ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
-/
lemma tendstoInDistribution_const [OpensMeasurableSpace E] (hZ : AEMeasurable Z μ') :
    TendstoInDistribution (fun _ ↦ Z) l Z (fun _ ↦ μ') μ' where
  forall_aemeasurable := fun _ ↦ by fun_prop
  tendsto := tendsto_const_nhds

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.tendstoInDistribution_of_identDistrib** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：tendstoInDistribution_of_identDistrib [OpensMeasurableSpace E] (i : ι) (hX
 : forall j, IdentDistrib (X i) (X j) (μ i) (μ j)) (hZ : IdentDistrib (X i) Z (μ
 i) μ') : TendstoInDistribution X l Z μ μ' where forall_aemeasurable j
参数：i : ι；hX : forall j, IdentDistrib (X i) (X j) (μ i) (μ j)；hZ : IdentDistrib (
X i) Z (μ i) μ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma tendstoInDistribution_of_identDistrib [OpensMeasurableSpace E] (i : ι)
    (hX : ∀ j, IdentDistrib (X i) (X j) (μ i) (μ j)) (hZ : IdentDistrib (X i) Z (μ i) μ') :
    TendstoInDistribution X l Z μ μ' where
  forall_aemeasurable j := (hX j).aemeasurable_snd
  aemeasurable_limit := hZ.aemeasurable_snd
  tendsto := by
    convert! tendsto_const_nhds with j
    exact (hX j).map_eq.symm.trans hZ.map_eq

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.TendstoInDistribution.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.TendstoInDistribution`。
形式化陈述：∀ {ι : Type u_1} {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i
 : ι) → MeasurableSpace (Ω i)}   {μ : (i : ι) → MeasureTheory.Measure (Ω i)} [in
st : ∀ (i : ι), MeasureTheory.IsProbabilityMeasure (μ i)]   {m' : MeasurableSpac
e Ω'} {μ' : MeasureTheory.Measure Ω'} [inst_1 : MeasureTheory.IsProbabilityMeasu
re μ']   {mE : MeasurableSpace E} {X Y : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Fi
lter ι} [inst_2 : TopologicalSpace E]   [inst_3 : OpensMeasurableSpace E] {T : Ω
' → E},   (∀ (i : ι), X i =ᵐ[μ i] Y i) →     Z =ᵐ[μ'] T → MeasureTheory.TendstoI
nDistribution X l Z μ μ' → MeasureTheory.TendstoInDistribution Y l T μ μ'
参数：i : ι；Ω i；i : ι；Ω i；i : ι；μ i；i : ι；∀ (i : ι), X i =ᵐ[μ i] Y i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `MeasureTheory.TendstoInDistribution.forall_aemeasurable`：∀ {ι : Type u_1
} {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpa
ce (Ω i)}   {m' : MeasurableSpace Ω'} {mE : M…
· 使用定理 `MeasureTheory.TendstoInDistribution.aemeasurable_limit`：∀ {ι : Type u_1}
 {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpac
e (Ω i)}   {m' : MeasurableSpace Ω'} {mE : M…
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `MeasureTheory.TendstoInDistribution.tendsto`：∀ {ι : Type u_1} {E : Type 
u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpace (Ω i)}   
{m' : MeasurableSpace Ω'} {mE : M…
-/
protected lemma TendstoInDistribution.congr [OpensMeasurableSpace E] {T : Ω' → E}
    (hXY : ∀ i, X i =ᵐ[μ i] Y i) (hZT : Z =ᵐ[μ'] T) (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution Y l T μ μ' where
  forall_aemeasurable i := (h.forall_aemeasurable i).congr (hXY i)
  aemeasurable_limit := h.aemeasurable_limit.congr hZT
  tendsto := by
    convert! h.tendsto using 2 with n
    · simpa using Measure.map_congr (hXY n).symm
    · rw! [Measure.map_congr hZT]
      rfl

@[simp]
/-
**MeasureTheory.tendstoInDistribution_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：tendstoInDistribution_of_isEmpty [IsEmpty E] : TendstoInDistribution X l Z
 μ μ' where forall_aemeasurable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `MeasurableSingletonClass.toDiscreteMeasurableSpace`：∀ {α : Type u_1} [in
st : MeasurableSpace α] [MeasurableSingletonClass α] [Countable α], DiscreteMeas
urableSpace α
· 使用定理 `Subsingleton.measurableSingletonClass`：∀ {α : Type u_1} [inst : Measurab
leSpace α] [Subsingleton α], MeasurableSingletonClass α
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_of_subsingleton_codomain`：measurable_of_subsingleton_codomain
 [Subsingleton β] (f : α -> β) : Measurable f
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma tendstoInDistribution_of_isEmpty [IsEmpty E] :
    TendstoInDistribution X l Z μ μ' where
  forall_aemeasurable := fun _ ↦ (measurable_of_subsingleton_codomain _).aemeasurable
  aemeasurable_limit := (measurable_of_subsingleton_codomain _).aemeasurable
  tendsto := by
    simp only [Subsingleton.elim _ (0 : Measure E)]
    exact tendsto_const_nhds

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.tendstoInDistribution_unique** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：tendstoInDistribution_unique [HasOuterApproxClosed E] [BorelSpace E] (X : 
(i : ι) -> Ω i -> E) {Z : Ω' -> E} {W : Ω'' -> E} [l.NeBot] (h1 : TendstoInDistr
ibution X l Z μ μ') (h2 : TendstoInDistribution X l W μ μ'') : μ'.map Z = μ''.ma
p W
参数：X : (i : ι) -> Ω i -> E；h1 : TendstoInDistribution X l Z μ μ'；h2 : TendstoInD
istribution X l W μ μ''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `MeasureTheory.TendstoInDistribution.aemeasurable_limit`：∀ {ι : Type u_1}
 {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpac
e (Ω i)}   {m' : MeasurableSpace Ω'} {mE : M…
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `MeasureTheory.TendstoInDistribution.forall_aemeasurable`：∀ {ι : Type u_1
} {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpa
ce (Ω i)}   {m' : MeasurableSpace Ω'} {mE : M…
· 使用定理 `MeasureTheory.TendstoInDistribution.tendsto`：∀ {ι : Type u_1} {E : Type 
u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpace (Ω i)}   
{m' : MeasurableSpace Ω'} {mE : M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
lemma tendstoInDistribution_unique [HasOuterApproxClosed E] [BorelSpace E]
    (X : (i : ι) → Ω i → E) {Z : Ω' → E} {W : Ω'' → E} [l.NeBot]
    (h1 : TendstoInDistribution X l Z μ μ') (h2 : TendstoInDistribution X l W μ μ'') :
    μ'.map Z = μ''.map W := by
  have h_eq := tendsto_nhds_unique h1.tendsto h2.tendsto
  rw [Subtype.ext_iff] at h_eq
  simpa using h_eq

set_option backward.isDefEq.respectTransparency.types false in
/-- **Continuous mapping theorem**: if `X n` tends to `Z` in distribution and `g` is continuous,
then `g ∘ X n` tends to `g ∘ Z` in distribution. -/
/-
**MeasureTheory.TendstoInDistribution.continuous_comp** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.TendstoInDistribution`。
形式化陈述：∀ {ι : Type u_1} {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i
 : ι) → MeasurableSpace (Ω i)}   {μ : (i : ι) → MeasureTheory.Measure (Ω i)} [in
st : ∀ (i : ι), MeasureTheory.IsProbabilityMeasure (μ i)]   {m' : MeasurableSpac
e Ω'} {μ' : MeasureTheory.Measure Ω'} [inst_1 : MeasureTheory.IsProbabilityMeasu
re μ']   {mE : MeasurableSpace E} {X : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filt
er ι} [inst_2 : TopologicalSpace E]   {F : Type u_6} [inst_3 : OpensMeasurableSp
ace E] [inst_4 : TopologicalSpace F] [inst_5 : MeasurableSpace F]   [inst_6 : Bo
relSpace F] {g : E → F},   Continuous g →     MeasureTheory.TendstoInDistributio
n X l Z μ μ' →       MeasureTheory.TendstoInDistribution (fun n => g ∘ X n) l (g
 ∘ Z) μ μ'
参数：i : ι；Ω i；i : ι；Ω i；i : ι；μ i；i : ι；fun n => g ∘ X n；g ∘ Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `MeasureTheory.TendstoInDistribution.forall_aemeasurable`：∀ {ι : Type u_1
} {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpa
ce (Ω i)}   {m' : MeasurableSpace Ω'} {mE : M…
· 使用定理 `MeasureTheory.TendstoInDistribution.aemeasurable_limit`：∀ {ι : Type u_1}
 {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpac
e (Ω i)}   {m' : MeasurableSpace Ω'} {mE : M…
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用引理 `MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`：t
endsto_map_of_tendsto_of_continuous {ι : Type*} {L : Filter ι} (νs : ι -> Probab
ilityMeasure Ω) (ν : ProbabilityMeasure Ω) (lim : Tendsto ν…
· 使用定理 `MeasureTheory.TendstoInDistribution.tendsto`：∀ {ι : Type u_1} {E : Type 
u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpace (Ω i)}   
{m' : MeasurableSpace Ω'} {mE : M…

--- 原说明 ---
**Continuous mapping theorem**: if `X n` tends to `Z` in distribution and `g` is
 continuous,
then `g ∘ X n` tends to `g ∘ Z` in distribution.
-/
theorem TendstoInDistribution.continuous_comp {F : Type*} [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E → F} (hg : Continuous g)
    (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n ↦ g ∘ X n) l (g ∘ Z) μ μ' where
  forall_aemeasurable := fun n ↦ hg.measurable.comp_aemeasurable (h.forall_aemeasurable n)
  aemeasurable_limit := hg.measurable.comp_aemeasurable h.aemeasurable_limit
  tendsto := by
    convert! ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h.tendsto hg
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk, Subtype.mk.injEq]
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (h.forall_aemeasurable _)]
    · simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
      congr
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h.aemeasurable_limit]

set_option backward.isDefEq.respectTransparency.types false in
/-- Almost sure convergence implies convergence in distribution. -/
/-
**MeasureTheory.tendstoInDistribution_of_ae_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：tendstoInDistribution_of_ae_tendsto [l.IsCountablyGenerated] [OpensMeasura
bleSpace E] {X : ι -> Ω' -> E} (hX₁ : forall i, AEMeasurable (X i) μ') (hZ : AEM
easurable Z μ') (hX₂ : forallᵐ ω ∂μ', Tendsto (fun i => X i ω) l (𝓝 (Z ω))) : Te
ndstoInDistribution X l Z (fun _ => μ') μ' where forall_aemeasurable
参数：hX₁ : forall i, AEMeasurable (X i) μ'；hZ : AEMeasurable Z μ'；hX₂ : forallᵐ ω 
∂μ', Tendsto (fun i => X i ω) l (𝓝 (Z ω))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…
· 使用定理 `AEMeasurable.coe_nnreal_ennreal`：AEMeasurable.coe_nnreal_ennreal {f : α 
-> Real>=0} {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => (f 
x : Real>=0∞)) μ
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `BoundedContinuousMapClass.toContinuousMapClass`：∀ {F : Type u_2} {α : ou
tParam (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst
_1 : PseudoMetricSpace β} {inst_2 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence'`：tendst
o_lintegral_filter_of_dominated_convergence' {ι} {l : Filter ι} [l.IsCountablyGe
nerated] {F : ι -> α -> Real>=0∞} {f : α -> Real>=0∞} …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `BoundedContinuousFunction.apply_le_edist_zero`：apply_le_edist_zero (f : 
X ->ᵇ Real>=0) (x : X) : f x <= edist 0 f
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f

--- 原说明 ---
Almost sure convergence implies convergence in distribution.
-/
theorem tendstoInDistribution_of_ae_tendsto [l.IsCountablyGenerated]
    [OpensMeasurableSpace E] {X : ι → Ω' → E}
    (hX₁ : ∀ i, AEMeasurable (X i) μ') (hZ : AEMeasurable Z μ')
    (hX₂ : ∀ᵐ ω ∂μ', Tendsto (fun i ↦ X i ω) l (𝓝 (Z ω))) :
    TendstoInDistribution X l Z (fun _ ↦ μ') μ' where
  forall_aemeasurable := hX₁
  aemeasurable_limit := hZ
  tendsto := by
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto, ProbabilityMeasure.coe_mk]
    intro f
    rw [lintegral_map' (by fun_prop) hZ]
    conv in ∫⁻ _, _ ∂_ => rw [lintegral_map' (by fun_prop) (hX₁ i)]
    apply tendsto_lintegral_filter_of_dominated_convergence' (bound := fun _ ↦ edist 0 f)
    · exact .of_forall (by fun_prop)
    · simp [f.apply_le_edist_zero]
    · simp
    filter_upwards [hX₂] with ω hω
    simpa [Function.comp_def] using f.continuous.tendsto (Z ω) |>.comp hω

end TendstoInDistribution

/-- Convergence in probability (`TendstoInMeasure`) implies convergence in distribution
(`TendstoInDistribution`). -/
/-
**MeasureTheory.TendstoInMeasure.tendstoInDistribution** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.TendstoInMeasure`。
形式化陈述：∀ {ι : Type u_1} {E : Type u_2} {Ω' : Type u_3} {m' : MeasurableSpace Ω'} 
{μ' : MeasureTheory.Measure Ω'}   [inst : MeasureTheory.IsProbabilityMeasure μ']
 {mE : MeasurableSpace E} {Z : Ω' → E} {l : Filter ι}   [inst_1 : PseudoEMetricS
pace E] [inst_2 : BorelSpace E] [l.IsCountablyGenerated] [l.NeBot] {X : ι → Ω' →
 E},   MeasureTheory.TendstoInMeasure μ' X l Z →     (∀ (i : ι), AEMeasurable (X
 i) μ') → MeasureTheory.TendstoInDistribution X l Z (fun x => μ') μ'
参数：∀ (i : ι), AEMeasurable (X i) μ'；fun x => μ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.TendstoInMeasure.aemeasurable`：∀ {α : Type u_1} {ι : Type 
u_2} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [ins
t : PseudoEMetricSpace E] [inst_1…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.tendsto_of_subseq_tendsto`：tendsto_of_subseq_tendsto {ι : Type*} 
{x : ι -> α} {f : Filter α} {l : Filter ι} [l.IsCountablyGenerated] (hxy : foral
l ns : Nat -> ι, Tends…
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae'`：∀ {α : Type u_1} 
{ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure
 α}   [inst : PseudoEMetricSpace E] {u : Fi…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `MeasureTheory.TendstoInMeasure.comp`：comp {v : Filter κ} {ns : κ -> ι} (
hg : TendstoInMeasure μ f l g) (hns : Tendsto ns v l) : TendstoInMeasure μ (f ∘ 
ns) v g
· 使用定理 `MeasureTheory.TendstoInDistribution.tendsto`：∀ {ι : Type u_1} {E : Type 
u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpace (Ω i)}   
{m' : MeasurableSpace Ω'} {mE : M…
· 使用定理 `MeasureTheory.tendstoInDistribution_of_ae_tendsto`：tendstoInDistribution
_of_ae_tendsto [l.IsCountablyGenerated] [OpensMeasurableSpace E] {X : ι -> Ω' ->
 E} (hX₁ : forall i, AEMeasurable (X i)…

--- 原说明 ---
Convergence in probability (`TendstoInMeasure`) implies convergence in distribut
ion
(`TendstoInDistribution`).
-/
theorem TendstoInMeasure.tendstoInDistribution [PseudoEMetricSpace E] [BorelSpace E]
    [l.IsCountablyGenerated] [l.NeBot] {X : ι → Ω' → E}
    (h : TendstoInMeasure μ' X l Z) (hX : ∀ i, AEMeasurable (X i) μ') :
    TendstoInDistribution X l Z (fun _ ↦ μ') μ' := by
  have hZ := h.aemeasurable hX
  refine ⟨hX, hZ, ?_⟩
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns ↦ ?_)
  obtain ⟨ms, hms1, hms2⟩ := h.comp hns |>.exists_seq_tendsto_ae'
  refine ⟨ms, TendstoInDistribution.tendsto ?_⟩
  exact tendstoInDistribution_of_ae_tendsto (by fun_prop) hZ hms2

variable [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `X, Y` be two sequences of measurable functions such that `X n` converges in distribution
to `Z`, and `Y n - X n` converges in probability to `0`.
Then `Y n` converges in distribution to `Z`. -/
/-
**MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory`。
形式化陈述：tendstoInDistribution_of_tendstoInMeasure_sub {X : ι -> Ω'' -> E} [l.IsCou
ntablyGenerated] (Y : ι -> Ω'' -> E) (Z : Ω' -> E) (hXZ : TendstoInDistribution 
X l Z (fun _ => μ'') μ') (hXY : TendstoInMeasure μ'' (Y - X) l 0) (hY : forall i
, AEMeasurable (Y i) μ'') : TendstoInDistribution Y l Z (fun _ => μ'') μ'
参数：Y : ι -> Ω'' -> E；Z : Ω' -> E；hXZ : TendstoInDistribution X l Z (fun _ => μ''
) μ'；hXY : TendstoInMeasure μ'' (Y - X) l 0；hY : forall i, AEMeasurable (Y i) μ'
'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.TendstoInDistribution.aemeasurable_limit`：∀ {ι : Type u_1}
 {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpac
e (Ω i)}   {m' : MeasurableSpace Ω'} {mE : M…
· 使用定理 `MeasureTheory.TendstoInDistribution.forall_aemeasurable`：∀ {ι : Type u_1
} {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpa
ce (Ω i)}   {m' : MeasurableSpace Ω'} {mE : M…
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `MeasurableSingletonClass.toDiscreteMeasurableSpace`：∀ {α : Type u_1} [in
st : MeasurableSpace α] [MeasurableSingletonClass α] [Countable α], DiscreteMeas
urableSpace α
· 使用定理 `Subsingleton.measurableSingletonClass`：∀ {α : Type u_1} [inst : Measurab
leSpace α] [Subsingleton α], MeasurableSingletonClass α
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `abs_sub_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrd
er G] [IsOrderedAddMonoid G] (a b c : G),   |a - c| ≤ |a - b| + |b - c|
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 168 条，此处仅展示前 30 条）

--- 原说明 ---
Let `X, Y` be two sequences of measurable functions such that `X n` converges in
 distribution
to `Z`, and `Y n - X n` converges in probability to `0`.
Then `Y n` converges in distribution to `Z`.
-/
lemma tendstoInDistribution_of_tendstoInMeasure_sub {X : ι → Ω'' → E}
    [l.IsCountablyGenerated] (Y : ι → Ω'' → E) (Z : Ω' → E)
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ') (hXY : TendstoInMeasure μ'' (Y - X) l 0)
    (hY : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution Y l Z (fun _ ↦ μ'') μ' := by
  have hZ : AEMeasurable Z μ' := hXZ.aemeasurable_limit
  have hX : ∀ i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨hY, hZ, ?_⟩
  -- We show convergence in distribution by verifying the convergence of integrals of any bounded
  -- Lipschitz function `F`
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ ω, F ω ∂(μ''.map (Y n))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  -- If `F` is 0-Lipschitz, then it is constant, and all integrals are equal to that constant
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ''.map (Y n)) := Measure.isProbabilityMeasure_map (hY n)
    have : IsProbabilityMeasure (μ'.map Z) := Measure.isProbabilityMeasure_map hZ
    simpa using! tendsto_const_nhds
  -- now `F` is `L`-Lipschitz with `L > 0`
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l, |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  -- We cut the difference into three pieces, two of which are small by the convergence assumptions
  have h_le n : |∫ ω, F ω ∂(μ''.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)|
      ≤ L * (ε / 2) + M * μ''.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂(μ''.map (Y n))) (∫ ω, F ω ∂(μ''.map (X n)))
      (∫ ω, F ω ∂(μ'.map Z))).trans ?_
    gcongr
    -- `⊢ |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map (X n))|`
    -- `    ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}`
    -- We prove integrability of the functions involved to be able to manipulate the integrals.
    have h_int_Y : Integrable (fun x ↦ F (Y n x)) μ'' := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (X n x)) μ'' := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (Y n a) - F (X n a)‖) μ'' := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_Y.sub h_int_X
    -- Now we prove the inequality
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ a, F (Y n a) - F (X n a) ∂μ''‖
    _ ≤ ∫ a, ‖F (Y n a) - F (X n a)‖ ∂μ'' := norm_integral_le_integral_norm _
    -- Either `‖Y n x - X n x‖` is smaller than `ε / 2`, or it is not
    _ = ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂μ''
        + ∫ a in {x | ε / 2 ≤ ‖Y n x - X n x‖}, ‖F (Y n a) - F (X n a)‖ ∂μ'' := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
    -- If it is smaller, we use the Lipschitz property of `F`
    -- If not, we use the boundedness of `F`.
    _ ≤ ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, L * (ε / 2) ∂μ''
        + ∫ a in {x | ε / 2 ≤ ‖Y n x - X n x‖}, M ∂μ'' := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · exact fun x hx ↦ hF_lip.norm_sub_le_of_le hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        convert!
          hF_bounded _
            _
              -- The goal is now a simple computation

    -- The goal is now a simple computation
    _ = L * (ε / 2) * μ''.real {x | ‖Y n x - X n x‖ < ε / 2}
        + M * μ''.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * μ''.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} := by
      rw [mul_assoc]
      gcongr
      grw [measureReal_le_one, mul_one]
  -- We finally show that the right-hand side tends to `L * ε / 2`, which is smaller than `L * ε`
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * μ''.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * μ''.real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ ω, F ω ∂(μ''.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_measureReal_norm, Pi.zero_apply, sub_zero] at hXY
      exact hXY (ε / 2) (by positivity)
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using! hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- Convergence in probability (`TendstoInMeasure`) implies convergence in distribution
(`TendstoInDistribution`). -/
/-
**MeasureTheory.TendstoInMeasure.tendstoInDistribution_of_aemeasurable** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.TendstoInMeasure`。
形式化陈述：∀ {ι : Type u_1} {E : Type u_2} {Ω' : Type u_3} {m' : MeasurableSpace Ω'} 
{μ' : MeasureTheory.Measure Ω'}   [inst : MeasureTheory.IsProbabilityMeasure μ']
 {mE : MeasurableSpace E} {Z : Ω' → E} {l : Filter ι}   [inst_1 : SeminormedAddC
ommGroup E] [SecondCountableTopology E] [inst_3 : BorelSpace E] [l.IsCountablyGe
nerated]   {X : ι → Ω' → E},   MeasureTheory.TendstoInMeasure μ' X l Z →     (∀ 
(i : ι), AEMeasurable (X i) μ') → AEMeasurable Z μ' → MeasureTheory.TendstoInDis
tribution X l Z (fun x => μ') μ'
参数：∀ (i : ι), AEMeasurable (X i) μ'；fun x => μ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`：tendstoInDi
stribution_of_tendstoInMeasure_sub {X : ι -> Ω'' -> E} [l.IsCountablyGenerated] 
(Y : ι -> Ω'' -> E) (Z : Ω' -> E) (hXZ : TendstoI…
· 使用引理 `MeasureTheory.tendstoInDistribution_const`：tendstoInDistribution_const [
OpensMeasurableSpace E] (hZ : AEMeasurable Z μ') : TendstoInDistribution (fun _ 
=> Z) l Z (fun _ => μ') μ' wher…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a

--- 原说明 ---
Convergence in probability (`TendstoInMeasure`) implies convergence in distribut
ion
(`TendstoInDistribution`).
-/
lemma TendstoInMeasure.tendstoInDistribution_of_aemeasurable [l.IsCountablyGenerated]
    {X : ι → Ω' → E} (h : TendstoInMeasure μ' X l Z) (hX : ∀ i, AEMeasurable (X i) μ')
    (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z (fun _ ↦ μ') μ' :=
  tendstoInDistribution_of_tendstoInMeasure_sub X Z (tendstoInDistribution_const hZ)
    (by simpa [tendstoInMeasure_iff_norm] using h) hX

set_option backward.isDefEq.respectTransparency.types false in
/-- **Slutsky's theorem**: if `X n` converges in distribution to `Z`, and `Y n` converges in
probability to a constant `c`, then the pair `(X n, Y n)` converges in distribution to `(Z, c)`. -/
/-
**MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.TendstoInDistribution`。
形式化陈述：∀ {ι : Type u_1} {E : Type u_2} {Ω' : Type u_3} {Ω'' : Type u_4} {m' : Mea
surableSpace Ω'}   {μ' : MeasureTheory.Measure Ω'} [inst : MeasureTheory.IsProba
bilityMeasure μ'] {m'' : MeasurableSpace Ω''}   {μ'' : MeasureTheory.Measure Ω''
} [inst_1 : MeasureTheory.IsProbabilityMeasure μ''] {mE : MeasurableSpace E}   {
l : Filter ι} [inst_2 : SeminormedAddCommGroup E] [SecondCountableTopology E] [i
nst_4 : BorelSpace E] {E' : Type u_6}   {mE' : MeasurableSpace E'} [inst_5 : Sem
inormedAddCommGroup E'] [inst_6 : SecondCountableTopology E']   [inst_7 : BorelS
pace E'] [l.IsCountablyGenerated] (X : ι → Ω'' → E) (Y : ι → Ω'' → E') (Z : Ω' →
 E) {c : E'},   MeasureTheory.TendstoInDistribution X l Z (fun x => μ'') μ' →   
  (MeasureTheory.TendstoInMeasure μ'' Y l fun x => c) →       (∀ (i : ι), AEMeas
urable (Y i) μ'') →         MeasureTheory.TendstoInDistribution (fun n ω => (X n
 ω, Y n ω)) l (fun ω => (Z ω, c)) (fun x => μ'') μ'
参数：X : ι → Ω'' → E；Y : ι → Ω'' → E'；Z : Ω' → E；fun x => μ''；MeasureTheory.Tendst
oInMeasure μ'' Y l fun x => c；∀ (i : ι), AEMeasurable (Y i) μ''；fun n ω => (X n 
ω, Y n ω)；fun ω => (Z ω, c)；fun x => μ''。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.TendstoInDistribution.forall_aemeasurable`：∀ {ι : Type u_1
} {E : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpa
ce (Ω i)}   {m' : MeasurableSpace Ω'} {mE : M…
· 使用引理 `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`：tendstoInDi
stribution_of_tendstoInMeasure_sub {X : ι -> Ω'' -> E} [l.IsCountablyGenerated] 
(Y : ι -> Ω'' -> E) (Z : Ω' -> E) (hXZ : TendstoI…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `MeasureTheory.TendstoInDistribution.continuous_comp`：∀ {ι : Type u_1} {E
 : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpace (
Ω i)}   {μ : (i : ι) → MeasureTheory.Meas…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ

--- 原说明 ---
**Slutsky's theorem**: if `X n` converges in distribution to `Z`, and `Y n` conv
erges in
probability to a constant `c`, then the pair `(X n, Y n)` converges in distribut
ion to `(Z, c)`.
-/
theorem TendstoInDistribution.prodMk_of_tendstoInMeasure_const
    {E' : Type*} {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E'] [SecondCountableTopology E']
    [BorelSpace E']
    [l.IsCountablyGenerated] (X : ι → Ω'' → E) (Y : ι → Ω'' → E') (Z : Ω' → E)
    {c : E'} (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY : TendstoInMeasure μ'' Y l (fun _ ↦ c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ω ↦ (X n ω, Y n ω)) l (fun ω ↦ (Z ω, c)) (fun _ ↦ μ'') μ' := by
  have hX : ∀ i, AEMeasurable (X i) μ'' := hXZ.forall_aemeasurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub (X := fun n ω ↦ (X n ω, c))
    (fun n ω ↦ (X n ω, Y n ω)) (fun ω ↦ (Z ω, c)) ?_ ?_ (fun i ↦ (hX i).prodMk (hY_meas i))
  · exact hXZ.continuous_comp (g := fun x ↦ (x, c)) (by fun_prop)
  · suffices TendstoInMeasure μ'' (fun n ω ↦ ((0 : E), Y n ω - c)) l 0 by
      convert! this with n ω
      simp
    simpa [tendstoInMeasure_iff_norm] using hY

/-- **Slutsky's theorem** for a continuous function: if `X n` converges in distribution to `Z`,
`Y n` converges in probability to a constant `c`, and `g` is a continuous function, then
`g (X n, Y n)` converges in distribution to `g (Z, c)`. -/
/-
**MeasureTheory.TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure
_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.TendstoInDistribution`。
形式化陈述：∀ {ι : Type u_1} {E : Type u_2} {Ω' : Type u_3} {Ω'' : Type u_4} {m' : Mea
surableSpace Ω'}   {μ' : MeasureTheory.Measure Ω'} [inst : MeasureTheory.IsProba
bilityMeasure μ'] {m'' : MeasurableSpace Ω''}   {μ'' : MeasureTheory.Measure Ω''
} [inst_1 : MeasureTheory.IsProbabilityMeasure μ''] {mE : MeasurableSpace E}   {
Z : Ω' → E} {l : Filter ι} [inst_2 : SeminormedAddCommGroup E] [SecondCountableT
opology E] [inst_4 : BorelSpace E]   {E' : Type u_6} {F : Type u_7} {mE' : Measu
rableSpace E'} [inst_5 : SeminormedAddCommGroup E']   [SecondCountableTopology E
'] [BorelSpace E'] [inst_8 : TopologicalSpace F] [inst_9 : MeasurableSpace F]   
[inst_10 : BorelSpace F] {g : E × E' → F},   Continuous g →     ∀ [l.IsCountably
Generated] {X : ι → Ω'' → E} {Y : ι → Ω'' → E'} {c : E'},       MeasureTheory.Te
ndstoInDistribution X l Z (fun x => μ'') μ' →         (MeasureTheory.TendstoInMe
asure μ'' Y l fun x => c) →           (∀ (i : ι), AEMeasurable (Y i) μ'') →     
        MeasureTheory.TendstoInDistribution (fun n ω => g (X n ω, Y n ω)) l (fun
 ω => g (Z ω, c)) (fun x => μ'') μ'
参数：fun x => μ''；MeasureTheory.TendstoInMeasure μ'' Y l fun x => c；∀ (i : ι), AEM
easurable (Y i) μ''；fun n ω => g (X n ω, Y n ω)；fun ω => g (Z ω, c)；fun x => μ''
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.TendstoInDistribution.continuous_comp`：∀ {ι : Type u_1} {E
 : Type u_2} {Ω' : Type u_3} {Ω : ι → Type u_5} {m : (i : ι) → MeasurableSpace (
Ω i)}   {μ : (i : ι) → MeasureTheory.Meas…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const`：∀ 
{ι : Type u_1} {E : Type u_2} {Ω' : Type u_3} {Ω'' : Type u_4} {m' : MeasurableS
pace Ω'}   {μ' : MeasureTheory.Measure Ω'} [inst : Measure…

--- 原说明 ---
**Slutsky's theorem** for a continuous function: if `X n` converges in distribut
ion to `Z`,
`Y n` converges in probability to a constant `c`, and `g` is a continuous functi
on, then
`g (X n, Y n)` converges in distribution to `g (Z, c)`.
-/
theorem TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const {E' F : Type*}
    {mE' : MeasurableSpace E'} [SeminormedAddCommGroup E'] [SecondCountableTopology E']
    [BorelSpace E']
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E × E' → F} (hg : Continuous g)
    [l.IsCountablyGenerated] {X : ι → Ω'' → E} {Y : ι → Ω'' → E'}
    {c : E'} (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY_tendsto : TendstoInMeasure μ'' Y l (fun _ ↦ c))
    (hY : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ω ↦ g (X n ω, Y n ω)) l (fun ω ↦ g (Z ω, c)) (fun _ ↦ μ'') μ' := by
  refine TendstoInDistribution.continuous_comp hg ?_
  exact hXZ.prodMk_of_tendstoInMeasure_const X Y Z hY_tendsto hY
/-
**MeasureTheory.TendstoInDistribution.add_of_tendstoInMeasure_const** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.TendstoInDistribution`。
形式化陈述：∀ {ι : Type u_1} {E : Type u_2} {Ω' : Type u_3} {Ω'' : Type u_4} {m' : Mea
surableSpace Ω'}   {μ' : MeasureTheory.Measure Ω'} [inst : MeasureTheory.IsProba
bilityMeasure μ'] {m'' : MeasurableSpace Ω''}   {μ'' : MeasureTheory.Measure Ω''
} [inst_1 : MeasureTheory.IsProbabilityMeasure μ''] {mE : MeasurableSpace E}   {
Z : Ω' → E} {l : Filter ι} [inst_2 : SeminormedAddCommGroup E] [SecondCountableT
opology E] [inst_4 : BorelSpace E]   {X Y : ι → Ω'' → E} [l.IsCountablyGenerated
] {c : E},   MeasureTheory.TendstoInDistribution X l Z (fun x => μ'') μ' →     (
MeasureTheory.TendstoInMeasure μ'' Y l fun x => c) →       (∀ (i : ι), AEMeasura
ble (Y i) μ'') →         MeasureTheory.TendstoInDistribution (fun n => X n + Y n
) l (fun ω => Z ω + c) (fun x => μ'') μ'
参数：fun x => μ''；MeasureTheory.TendstoInMeasure μ'' Y l fun x => c；∀ (i : ι), AEM
easurable (Y i) μ''；fun n => X n + Y n；fun ω => Z ω + c；fun x => μ''。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.TendstoInDistribution.continuous_comp_prodMk_of_tendstoInM
easure_const`：∀ {ι : Type u_1} {E : Type u_2} {Ω' : Type u_3} {Ω'' : Type u_4} {
m' : MeasurableSpace Ω'}   {μ' : MeasureTheory.Measure Ω'} [inst : Measure…
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma TendstoInDistribution.add_of_tendstoInMeasure_const {X Y : ι → Ω'' → E}
    [l.IsCountablyGenerated] {c : E} (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY_tendsto : TendstoInMeasure μ'' Y l (fun _ ↦ c)) (hY : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ↦ X n + Y n) l (fun ω ↦ Z ω + c) (fun _ ↦ μ'') μ' :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun (x : E × E) ↦ x.1 + x.2) (by fun_prop) hY_tendsto hY

end MeasureTheory

