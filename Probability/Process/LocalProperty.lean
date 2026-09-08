/-
Copyright (c) 2026 Rémy Degenne, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.Probability.Process.Stopping

/-! # Local properties of processes

This file defines local and stable properties of stochastic processes with respect to a filtration.
This is notably useful for local martingales.

## Main definitions

* `IsPreLocalizingSequence`: A pre-localizing sequence is a sequence of stopping
  times which tends almost surely to infinity.
* `IsLocalizingSequence`: A localizing sequence is a pre-localizing sequence
  which is almost surely non-decreasing.
* `Locally`: A stochastic process `X` is said to satisfy a property `p` locally
  with respect to a filtration `𝓕` if there exists a localizing sequence `(τ n)` such that for all
  `n`, the stopped process `X^{τ n} I_{τ n > ⊥}` satisfies `p`.
* `IsStable`: A property of stochastic processes is said to be stable if it is
  preserved under taking the stopped process `X^{τ} I_{τ > ⊥}` by a stopping time `τ`.

## Main results

* `IsStable.isStable_locally`: If a property `p` is stable, then the property
  "satisfies `p` locally" is also stable.
* `IsPreLocalizingSequence.isLocalizingSequence_biInf`: Given a
  pre-localizing sequence `(τ n)`, the sequence `⊓ j ≥ n, τ j` is a localizing sequence.
* `IsStable.locally_of_isPreLocalizingSequence`: If a property `p` is stable, then
  to prove that `X` satisfies `p` locally, one can replace the localizing sequence in the definition
  of "locally" by a pre-localizing sequence.
* `IsStable.locally_locally`: For stable properties, locally is idempotent.
* `IsStable.locally_induction`: If `q` is a stable property, and `p` implies
  locally `q`, then locally `p` implies locally `q`.

### Tags

localizing sequence, local property, stable property
-/

@[expose] public section

open MeasureTheory Filter Filtration
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A pre-localizing sequence is a sequence of stopping times that tends almost surely to
infinity. -/
/-
**ProbabilityTheory.IsPreLocalizingSequence** 是 Mathlib 中的一个结构，位于命名空间 `Probabili
tyTheory`。
形式化陈述：IsPreLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι
] (𝓕 : Filtration ι mΩ) (τ : Nat -> Ω -> WithTop ι) (P : Measure Ω
参数：𝓕 : Filtration ι mΩ；τ : Nat -> Ω -> WithTop ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pre-localizing sequence is a sequence of stopping times that tends almost sure
ly to
infinity.
-/
structure IsPreLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι) (P : Measure Ω := by volume_tac) :
    Prop where
  isStoppingTime : ∀ n, IsStoppingTime 𝓕 (τ n)
  tendsto_top : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)

/-- A localizing sequence is a sequence of stopping times that is almost surely increasing and
tends almost surely to infinity. -/
/-
**ProbabilityTheory.IsLocalizingSequence** 是 Mathlib 中的一个结构，位于命名空间 `ProbabilityT
heory`。
形式化陈述：IsLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι] (
𝓕 : Filtration ι mΩ) (τ : Nat -> Ω -> WithTop ι) (P : Measure Ω
参数：𝓕 : Filtration ι mΩ；τ : Nat -> Ω -> WithTop ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A localizing sequence is a sequence of stopping times that is almost surely incr
easing and
tends almost surely to infinity.
-/
structure IsLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι)
    (P : Measure Ω := by volume_tac) extends IsPreLocalizingSequence 𝓕 τ P where
  mono : ∀ᵐ ω ∂P, Monotone (τ · ω)
/-
**ProbabilityTheory.isLocalizingSequence_const_top** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：isLocalizingSequence_const_top [Preorder ι] [TopologicalSpace ι] [OrderTop
ology ι] (𝓕 : Filtration ι mΩ) (P : Measure Ω) : IsLocalizingSequence 𝓕 (fun _ _
 => ⊤) P where isStoppingTime n
参数：𝓕 : Filtration ι mΩ；P : Measure Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma isLocalizingSequence_const_top [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) : IsLocalizingSequence 𝓕 (fun _ _ ↦ ⊤) P where
  isStoppingTime n := by simp [IsStoppingTime]
  mono := ae_of_all _ fun _ _ _ _ ↦ by simp
  tendsto_top := ae_of_all _ fun _ ↦ tendsto_const_nhds

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

/-
**ProbabilityTheory.IsLocalizingSequence.min** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.IsLocalizingSequence`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} [inst : LinearOrder ι]   {𝓕 : MeasureTheory.Filtration ι mΩ} [inst_
1 : TopologicalSpace ι] [inst_2 : OrderTopology ι]   {τ σ : ℕ → Ω → WithTop ι}, 
  ProbabilityTheory.IsLocalizingSequence 𝓕 τ P →     ProbabilityTheory.IsLocaliz
ingSequence 𝓕 σ P → ProbabilityTheory.IsLocalizingSequence 𝓕 (τ ⊓ σ) P
参数：τ ⊓ σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `ProbabilityTheory.IsPreLocalizingSequence.isStoppingTime`：∀ {ι : Type u_
1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 : Topolog
icalSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
· 使用定理 `ProbabilityTheory.IsLocalizingSequence.toIsPreLocalizingSequence`：∀ {ι :
 Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 :
 TopologicalSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsPreLocalizingSequence.tendsto_top`：∀ {ι : Type u_1} 
{Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 : Topologica
lSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.min`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace
 α] [inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   {b : Filter
 β} {a₁ …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `ProbabilityTheory.IsLocalizingSequence.mono`：∀ {ι : Type u_1} {Ω : Type 
u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 : TopologicalSpace ι] 
  [inst_2 : OrderTopology ι] {𝓕 :…
· 使用定理 `Monotone.min`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : 
LinearOrder β] {f g : α → β},   Monotone f → Monotone g → Monotone fun x => min 
(f…
-/
protected lemma IsLocalizingSequence.min [TopologicalSpace ι] [OrderTopology ι]
    {τ σ : ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : IsLocalizingSequence 𝓕 σ P) :
    IsLocalizingSequence 𝓕 (min τ σ) P where
  isStoppingTime n := (hτ.isStoppingTime n).min (hσ.isStoppingTime n)
  mono := by filter_upwards [hτ.mono, hσ.mono] with ω hτω hσω using hτω.min hσω
  tendsto_top := by
    filter_upwards [hτ.tendsto_top, hσ.tendsto_top] with ω hτω hσω using hτω.min hσω

variable [OrderBot ι]

/-- A stochastic process `X` is said to satisfy a property `p` locally with respect to a
filtration `𝓕` if there exists a localizing sequence `(τ_n)` such that for all `n`, the stopped
process `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfies `p`. -/
/-
**ProbabilityTheory.Locally** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：Locally [TopologicalSpace ι] [OrderTopology ι] [Zero E] (p : (ι -> Ω -> E)
 -> Prop) (𝓕 : Filtration ι mΩ) (X : ι -> Ω -> E) (P : Measure Ω
参数：p : (ι -> Ω -> E) -> Prop；𝓕 : Filtration ι mΩ；X : ι -> Ω -> E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A stochastic process `X` is said to satisfy a property `p` locally with respect 
to a
filtration `𝓕` if there exists a localizing sequence `(τ_n)` such that for all `
n`, the stopped
process `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfies `p`.
-/
def Locally [TopologicalSpace ι] [OrderTopology ι] [Zero E]
    (p : (ι → Ω → E) → Prop) (𝓕 : Filtration ι mΩ)
    (X : ι → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∃ τ : ℕ → Ω → WithTop ι, IsLocalizingSequence 𝓕 τ P ∧
    ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))

namespace Locally

variable [TopologicalSpace ι] [OrderTopology ι]

/-- A localizing sequence, witness of the local property of the stochastic process. -/
noncomputable
/-
**ProbabilityTheory.Locally.localSeq** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y.Locally`。
形式化陈述：localSeq [Zero E] (hX : Locally p 𝓕 X P) : Nat -> Ω -> WithTop ι
参数：hX : Locally p 𝓕 X P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def localSeq [Zero E] (hX : Locally p 𝓕 X P) :
    ℕ → Ω → WithTop ι :=
  hX.choose
/-
**ProbabilityTheory.Locally.isLocalizingSequence_localSeq** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Locally`。
形式化陈述：isLocalizingSequence_localSeq [Zero E] (hX : Locally p 𝓕 X P) : IsLocalizi
ngSequence 𝓕 hX.localSeq P
参数：hX : Locally p 𝓕 X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma isLocalizingSequence_localSeq [Zero E] (hX : Locally p 𝓕 X P) :
    IsLocalizingSequence 𝓕 hX.localSeq P :=
  hX.choose_spec.1
/-
**ProbabilityTheory.Locally.stoppedProcess_localSeq** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.Locally`。
形式化陈述：stoppedProcess_localSeq [Zero E] (hX : Locally p 𝓕 X P) (n : Nat) : p (sto
ppedProcess (fun i => {ω | ⊥ < hX.localSeq n ω}.indicator (X i)) (hX.localSeq n)
)
参数：hX : Locally p 𝓕 X P；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma stoppedProcess_localSeq [Zero E] (hX : Locally p 𝓕 X P) (n : ℕ) :
    p (stoppedProcess (fun i ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X i)) (hX.localSeq n)) :=
  hX.choose_spec.2 n
/-
**ProbabilityTheory.Locally.of_prop** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
.Locally`。
形式化陈述：of_prop [Zero E] (hp : p X) : Locally p 𝓕 X P
参数：hp : p X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.isLocalizingSequence_const_top`：isLocalizingSequence_c
onst_top [Preorder ι] [TopologicalSpace ι] [OrderTopology ι] (𝓕 : Filtration ι m
Ω) (P : Measure Ω) : IsLocalizingSeque…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WithTop.nontrivial`：∀ {α : Type u_1} [Nonempty α], Nontrivial (WithTop α
)
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `Set.indicator_univ`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f :
 α → M), Set.univ.indicator f = f
· 使用定理 `MeasureTheory.stoppedProcess_const_top`：∀ {Ω : Type u_1} {β : Type u_2} 
{ι : Type u_3} [inst : Nonempty ι] {u : ι → Ω → β} [inst_1 : LinearOrder ι],   (
MeasureTheory.stoppedProcess…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma of_prop [Zero E] (hp : p X) : Locally p 𝓕 X P :=
  ⟨fun n _ ↦ ⊤, isLocalizingSequence_const_top _ _, by simpa⟩
/-
**ProbabilityTheory.Locally.mono** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Lo
cally`。
形式化陈述：mono [Zero E] (hpq : forall X, p X -> q X) (hpX : Locally p 𝓕 X P) : Local
ly q 𝓕 X P
参数：hpq : forall X, p X -> q X；hpX : Locally p 𝓕 X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Locally.isLocalizingSequence_localSeq`：isLocalizingSeq
uence_localSeq [Zero E] (hX : Locally p 𝓕 X P) : IsLocalizingSequence 𝓕 hX.local
Seq P
· 使用引理 `ProbabilityTheory.Locally.stoppedProcess_localSeq`：stoppedProcess_localS
eq [Zero E] (hX : Locally p 𝓕 X P) (n : Nat) : p (stoppedProcess (fun i => {ω | 
⊥ < hX.localSeq n ω}.indicator (X i)) (…
-/
lemma mono [Zero E] (hpq : ∀ X, p X → q X) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  ⟨hpX.localSeq, hpX.isLocalizingSequence_localSeq, fun n ↦ hpq _ <| hpX.stoppedProcess_localSeq n⟩
/-
**ProbabilityTheory.Locally.of_and** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.
Locally`。
形式化陈述：of_and [Zero E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P) : Locally p 𝓕 X 
P ∧ Locally q 𝓕 X P
参数：hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Locally.mono`：mono [Zero E] (hpq : forall X, p X -> q 
X) (hpX : Locally p 𝓕 X P) : Locally q 𝓕 X P
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma of_and [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally p 𝓕 X P ∧ Locally q 𝓕 X P :=
  ⟨hX.mono <| fun _ ↦ And.left, hX.mono <| fun _ ↦ And.right⟩
/-
**ProbabilityTheory.Locally.left** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Lo
cally`。
形式化陈述：left [Zero E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P) : Locally p 𝓕 X P
参数：hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `ProbabilityTheory.Locally.of_and`：of_and [Zero E] (hX : Locally (fun Y =
> p Y ∧ q Y) 𝓕 X P) : Locally p 𝓕 X P ∧ Locally q 𝓕 X P
-/
lemma left [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally p 𝓕 X P :=
  hX.of_and.left
/-
**ProbabilityTheory.Locally.right** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.L
ocally`。
形式化陈述：right [Zero E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P) : Locally q 𝓕 X P
参数：hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `ProbabilityTheory.Locally.of_and`：of_and [Zero E] (hX : Locally (fun Y =
> p Y ∧ q Y) 𝓕 X P) : Locally p 𝓕 X P ∧ Locally q 𝓕 X P
-/
lemma right [Zero E] (hX : Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P) :
    Locally q 𝓕 X P :=
  hX.of_and.right

end Locally

variable [Zero E]

/-- A property of stochastic processes is said to be stable if it is preserved under taking
the stopped process by a stopping time. -/
/-
**ProbabilityTheory.IsStable** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：IsStable (𝓕 : Filtration ι mΩ) (p : (ι -> Ω -> E) -> Prop) : Prop
参数：𝓕 : Filtration ι mΩ；p : (ι -> Ω -> E) -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of stochastic processes is said to be stable if it is preserved under
 taking
the stopped process by a stopping time.
-/
def IsStable
    (𝓕 : Filtration ι mΩ) (p : (ι → Ω → E) → Prop) : Prop :=
  ∀ X : ι → Ω → E, p X → ∀ τ : Ω → WithTop ι, IsStoppingTime 𝓕 τ →
    p (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ)
/-
**ProbabilityTheory.IsStable.and** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.Is
Stable`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} [i
nst : LinearOrder ι]   {𝓕 : MeasureTheory.Filtration ι mΩ} {p q : (ι → Ω → E) → 
Prop} [inst_1 : OrderBot ι] [inst_2 : Zero E],   ProbabilityTheory.IsStable 𝓕 p 
→ ProbabilityTheory.IsStable 𝓕 q → ProbabilityTheory.IsStable 𝓕 fun X => p X ∧ q
 X
参数：ι → Ω → E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma IsStable.and (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q) :
    IsStable 𝓕 (fun X ↦ p X ∧ q X) :=
  fun _ hX τ hτ ↦ ⟨hp _ hX.left τ hτ, hq _ hX.right τ hτ⟩

variable [TopologicalSpace ι] [OrderTopology ι]
/-
**ProbabilityTheory.IsStable.locally** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.IsStable`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω}   [inst : LinearOrder ι] {𝓕 : MeasureTheory.Filtrati
on ι mΩ} {p : (ι → Ω → E) → Prop} [inst_1 : OrderBot ι]   [inst_2 : Zero E] [ins
t_3 : TopologicalSpace ι] [inst_4 : OrderTopology ι],   ProbabilityTheory.IsStab
le 𝓕 p → ProbabilityTheory.IsStable 𝓕 fun Y => ProbabilityTheory.Locally p 𝓕 Y P
参数：ι → Ω → E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Locally.isLocalizingSequence_localSeq`：isLocalizingSeq
uence_localSeq [Zero E] (hX : Locally p 𝓕 X P) : IsLocalizingSequence 𝓕 hX.local
Seq P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 (s t : Set α) (f : α → M),   s.indicator (t.indicator f) = (s ∩ t).indicator f
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.stoppedProcess_stoppedProcess`：stoppedProcess_stoppedProce
ss : stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (σ ⊓ τ)
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.stoppedProcess_indicator_comm'`：stoppedProcess_indicator_c
omm' [Zero β] {s : Set Ω} : stoppedProcess (fun i => s.indicator (u i)) τ = fun 
i => s.indicator (stoppedProcess u…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用引理 `ProbabilityTheory.Locally.stoppedProcess_localSeq`：stoppedProcess_localS
eq [Zero E] (hX : Locally p 𝓕 X P) (n : Nat) : p (stoppedProcess (fun i => {ω | 
⊥ < hX.localSeq n ω}.indicator (X i)) (…
-/
lemma IsStable.locally (hp : IsStable 𝓕 p) :
    IsStable 𝓕 (fun Y ↦ Locally p 𝓕 Y P) := by
  refine fun X hX τ hτ ↦ ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  simp_rw [← stoppedProcess_indicator_comm', Set.indicator_indicator, Set.inter_comm,
    ← Set.indicator_indicator, stoppedProcess_stoppedProcess, inf_comm,
    stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess]
  exact hp _ (hX.stoppedProcess_localSeq n) τ hτ
/-
**ProbabilityTheory.IsStable.locally_and_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.IsStable`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω}   [inst : LinearOrder ι] {𝓕 : MeasureTheory.Filtrati
on ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}   [inst_1 : OrderBot ι] [ins
t_2 : Zero E] [inst_3 : TopologicalSpace ι] [inst_4 : OrderTopology ι],   Probab
ilityTheory.IsStable 𝓕 p →     ProbabilityTheory.IsStable 𝓕 q →       (Probabili
tyTheory.Locally (fun Y => p Y ∧ q Y) 𝓕 X P ↔         ProbabilityTheory.Locally 
p 𝓕 X P ∧ ProbabilityTheory.Locally q 𝓕 X P)
参数：ι → Ω → E；ProbabilityTheory.Locally (fun Y => p Y ∧ q Y) 𝓕 X P ↔         Prob
abilityTheory.Locally p 𝓕 X P ∧ ProbabilityTheory.Locally q 𝓕 X P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Locally.of_and`：of_and [Zero E] (hX : Locally (fun Y =
> p Y ∧ q Y) 𝓕 X P) : Locally p 𝓕 X P ∧ Locally q 𝓕 X P
· 使用定理 `ProbabilityTheory.IsLocalizingSequence.min`：∀ {ι : Type u_1} {Ω : Type u
_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : LinearOrder ι
]   {𝓕 : MeasureTheory.Filtratio…
· 使用引理 `ProbabilityTheory.Locally.isLocalizingSequence_localSeq`：isLocalizingSeq
uence_localSeq [Zero E] (hX : Locally p 𝓕 X P) : IsLocalizingSequence 𝓕 hX.local
Seq P
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `MeasureTheory.stoppedProcess_indicator_comm`：stoppedProcess_indicator_co
mm [Zero β] {s : Set Ω} (i : ι) : stoppedProcess (fun i => s.indicator (u i)) τ 
i = s.indicator (stoppedProcess u…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.stoppedProcess.congr_simp`：∀ {Ω : Type u_1} {β : Type u_2}
 {ι : Type u_3} [inst : Nonempty ι] [inst_1 : LinearOrder ι] (u u_1 : ι → Ω → β)
,   u = u_1 →     ∀ (τ τ_1 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `MeasureTheory.stoppedProcess_stoppedProcess`：stoppedProcess_stoppedProce
ss : stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (σ ⊓ τ)
· 使用定理 `Set.ofPred_and`：ofPred_and {p q : α -> Prop} : { a | p a ∧ q a } = { a |
 p a } inter { a | q a }
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `ProbabilityTheory.Locally.stoppedProcess_localSeq`：stoppedProcess_localS
eq [Zero E] (hX : Locally p 𝓕 X P) (n : Nat) : p (stoppedProcess (fun i => {ω | 
⊥ < hX.localSeq n ω}.indicator (X i)) (…
· 使用定理 `ProbabilityTheory.IsPreLocalizingSequence.isStoppingTime`：∀ {ι : Type u_
1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 : Topolog
icalSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
· 使用定理 `ProbabilityTheory.IsLocalizingSequence.toIsPreLocalizingSequence`：∀ {ι :
 Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 :
 TopologicalSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
-/
lemma IsStable.locally_and_iff (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q) :
    Locally (fun Y ↦ p Y ∧ q Y) 𝓕 X P ↔ Locally p 𝓕 X P ∧ Locally q 𝓕 X P := by
  refine ⟨Locally.of_and, fun ⟨hpX, hqX⟩ ↦
    ⟨_, hpX.isLocalizingSequence_localSeq.min hqX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩⟩
  suffices ∀ (p q : (ι → Ω → E) → Prop) (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
      (hpX : Locally p 𝓕 X P) (hqX : Locally q 𝓕 X P),
      p (stoppedProcess (fun i ↦ {ω | ⊥ < (hpX.localSeq ⊓ hqX.localSeq) n ω}.indicator (X i))
      ((hpX.localSeq ⊓ hqX.localSeq) n)) by
    refine ⟨this p q hp hq hpX hqX, ?_⟩
    simp_rw [inf_comm hpX.localSeq]
    exact this q p hq hp hqX hpX
  intro p q hp hq hpX hqX
  convert!
    hp _ (hpX.stoppedProcess_localSeq n) _ <|
      hqX.isLocalizingSequence_localSeq.isStoppingTime n using 1
  ext i ω
  simp_rw [stoppedProcess_indicator_comm, Pi.inf_apply, lt_inf_iff, inf_comm (hpX.localSeq n)]
  rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm, Set.ofPred_and,
    Set.inter_comm]
  simp_rw [← Set.indicator_indicator]
  rfl

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}

/-
**ProbabilityTheory.IsPreLocalizingSequence.isLocalizingSequence_biInf** 是 Mathl
ib 中的一个定理，位于命名空间 `ProbabilityTheory.IsPreLocalizingSequence`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω}   [inst : ConditionallyCompleteLinearOrderBot ι] [inst_1 : Topologi
calSpace ι] [inst_2 : OrderTopology ι]   {𝓕 : MeasureTheory.Filtration ι mΩ} [De
nselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]   {τ : ℕ → Ω → WithTop
 ι} [𝓕.IsRightContinuous],   ProbabilityTheory.IsPreLocalizingSequence 𝓕 τ P →  
   ProbabilityTheory.IsLocalizingSequence 𝓕 (fun i ω => ⨅ j, ⨅ (_ : j ≥ i), τ j 
ω) P
参数：fun i ω => ⨅ j, ⨅ (_ : j ≥ i), τ j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsStoppingTime.biInf`：∀ {Ω : Type u_1} {ι : Type u_3} {m :
 MeasurableSpace Ω} [inst : ConditionallyCompleteLinearOrderBot ι]   [inst_1 : T
opologicalSpace ι] [Orde…
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.IsPreLocalizingSequence.isStoppingTime`：∀ {ι : Type u_
1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 : Topolog
icalSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsPreLocalizingSequence.tendsto_top`：∀ {ι : Type u_1} 
{Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 : Topologica
lSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.liminf_eq`：Filter.Tendsto.liminf_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : liminf u f = a
· 使用定理 `TopologicalSpace.instOrderTopologyWithTop`：∀ {ι : Type u_1} [inst : Preo
rder ι] [inst_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι], OrderTopology 
(WithTop ι)
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.liminf_eq_iSup_iInf_of_nat`：liminf_eq_iSup_iInf_of_nat {u : Nat -
> α} : liminf u atTop = ⨆ n : Nat, ⨅ i >= n, u i
· 使用定理 `tendsto_atTop_iSup`：tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f
 atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `iInf_le_iInf_of_subset`：∀ {α : Type u_1} {β : Type u_2} [inst : Complete
Lattice α] {f : β → α} {s t : Set β},   s ⊆ t → ⨅ x ∈ t, f x ≤ ⨅ x ∈ s, f x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma IsPreLocalizingSequence.isLocalizingSequence_biInf
    [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
    {τ : ℕ → Ω → WithTop ι} [IsRightContinuous 𝓕] (hτ : IsPreLocalizingSequence 𝓕 τ P) :
    IsLocalizingSequence 𝓕 (fun i ω ↦ ⨅ j ≥ i, τ j ω) P where
  isStoppingTime n := IsStoppingTime.biInf (Set.to_countable {j | j ≥ n})
    (fun j _ ↦ hτ.isStoppingTime j)
  mono := ae_of_all _ <| fun ω n m hnm ↦ iInf_le_iInf_of_subset <| fun k hk ↦ hnm.trans hk
  tendsto_top := by
    filter_upwards [hτ.tendsto_top] with ω hω
    replace hω := hω.liminf_eq
    rw [liminf_eq_iSup_iInf_of_nat] at hω
    rw [← hω]
    refine tendsto_atTop_iSup fun n m hnm ↦ ?_
    simp [iInf_le_iff]
    grind

/-- A process `X` satisfies a stable property `p` locally if there exists a pre-localizing
sequence `τ` for which the stopped processes of `fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)` satisfy
`p`. -/
/-
**ProbabilityTheory.IsStable.locally_of_isPreLocalizingSequence** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.IsStable`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω}   [inst : ConditionallyCompleteLinearOrderBot ι] [in
st_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι]   {𝓕 : MeasureTheory.Filtr
ation ι mΩ} {X : ι → Ω → E} {p : (ι → Ω → E) → Prop} [inst_3 : Zero E] [DenselyO
rdered ι]   [FirstCountableTopology ι] [NoMaxOrder ι] {τ : ℕ → Ω → WithTop ι},  
 ProbabilityTheory.IsStable 𝓕 p →     ∀ [𝓕.IsRightContinuous],       Probability
Theory.IsPreLocalizingSequence 𝓕 τ P →         (∀ (n : ℕ), p (MeasureTheory.stop
pedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))) →           Probab
ilityTheory.Locally p 𝓕 X P
参数：ι → Ω → E；∀ (n : ℕ), p (MeasureTheory.stoppedProcess (fun i => {ω | ⊥ < τ n ω
}.indicator (X i)) (τ n))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `ProbabilityTheory.IsPreLocalizingSequence.isLocalizingSequence_biInf`：∀ 
{ι : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measur
e Ω}   [inst : ConditionallyCompleteLinearOrderBot ι] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.stoppedProcess_indicator_comm'`：stoppedProcess_indicator_c
omm' [Zero β] {s : Set Ω} : stoppedProcess (fun i => s.indicator (u i)) τ = fun 
i => s.indicator (stoppedProcess u…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.stoppedProcess_stoppedProcess_of_le_right`：stoppedProcess_
stoppedProcess_of_le_right (h : σ <= τ) : stoppedProcess (stoppedProcess u τ) σ 
= stoppedProcess u σ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 (s t : Set α) (f : α → M),   s.indicator (t.indicator f) = (s ∩ t).indicator f
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ProbabilityTheory.IsPreLocalizingSequence.isStoppingTime`：∀ {ι : Type u_
1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 : Topolog
icalSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
· 使用定理 `ProbabilityTheory.IsLocalizingSequence.toIsPreLocalizingSequence`：∀ {ι :
 Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 :
 TopologicalSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…

--- 原说明 ---
A process `X` satisfies a stable property `p` locally if there exists a pre-loca
lizing
sequence `τ` for which the stopped processes of `fun i ↦ {ω | ⊥ < τ n ω}.indicat
or (X i)` satisfy
`p`.
-/
lemma IsStable.locally_of_isPreLocalizingSequence
    [Zero E] [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι] {τ : ℕ → Ω → WithTop ι}
    (hp : IsStable 𝓕 p) [IsRightContinuous 𝓕] (hτ : IsPreLocalizingSequence 𝓕 τ P)
    (hpτ : ∀ n, p (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))) :
    Locally p 𝓕 X P := by
  refine ⟨_, hτ.isLocalizingSequence_biInf, fun n ↦ ?_⟩
  rw [stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess_of_le_right
    (τ := fun ω ↦ τ n ω) (fun _ ↦ (iInf_le _ n).trans <| iInf_le _ le_rfl),
    ← stoppedProcess_indicator_comm']
  convert!
    hp _ (hpτ n) (fun ω ↦ ⨅ j ≥ n, τ j ω) <| hτ.isLocalizingSequence_biInf.isStoppingTime n using 2
  ext i ω
  rw [stoppedProcess_indicator_comm', Set.indicator_indicator]
  congr with ω
  exact ⟨fun h ↦ ⟨h, lt_of_lt_of_le h <| (iInf_le _ n).trans (iInf_le _ le_rfl)⟩, fun h ↦ h.1⟩

section

variable [SecondCountableTopology ι] [IsFiniteMeasure P]

/-
**ProbabilityTheory.isPreLocalizingSequence_of_isLocalizingSequence_aux'** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isPreLocalizingSequence_of_isLocalizingSequence_aux'
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ T : ℕ → ι, Tendsto T atTop atTop ∧
      ∀ n, ∃ k, P {ω | σ n k ω < min (τ n ω) (T n)} ≤ (1 / 2) ^ n := by
  obtain ⟨T, -, hT⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
  refine ⟨T, hT, fun n ↦ ?_⟩
  by_contra! hn
  suffices (1 / 2) ^ n ≤ P (⋂ k : ℕ, {ω | σ n k ω < min (τ n ω) (T n)}) by
    refine (by simp : ¬ (1 / 2 : ℝ≥0∞) ^ n ≤ 0) <| this.trans <| nonpos_iff_eq_zero.2 ?_
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [(hσ n).tendsto_top] with ω hTop hmem
    simp_rw [WithTop.tendsto_nhds_top_iff, eventually_atTop] at hTop
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hmem
    obtain ⟨N, hN⟩ := hTop (T n)
    specialize hN N le_rfl
    specialize hmem N
    grind
  rw [measure_iInter_of_ae_antitone, le_iInf_iff]
  · exact fun k ↦ (hn k).le
  · filter_upwards [(hσ n).mono] with ω hω
    intros i j hij
    specialize hω hij
    simp [Set.ofPred] at *
    grind
  · refine fun i ↦ .nullMeasurableSet ?_
    simp_rw [lt_inf_iff, Set.ofPred_and]
    exact MeasurableSet.inter
      (measurableSet_lt ((hσ n).isStoppingTime i).measurable' (hτ.isStoppingTime n).measurable')
        <| measurableSet_lt ((hσ n).isStoppingTime i).measurable' measurable_const
  · exact ⟨0, measure_ne_top P _⟩

/-- Auxiliary definition for `isPreLocalizingSequence_of_isLocalizingSequence` which constructs a
strictly increasing sequence from a given sequence. -/
/-
**ProbabilityTheory.mkStrictMonoAux** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `isPreLocalizingSequence_of_isLocalizingSequence` which
 constructs a
strictly increasing sequence from a given sequence.
-/
private def mkStrictMonoAux (x : ℕ → ℕ) : ℕ → ℕ
  | 0 => x 0
  | n + 1 => max (x (n + 1)) (mkStrictMonoAux x n) + 1
/-
**ProbabilityTheory.mkStrictMonoAux_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mkStrictMonoAux_strictMono (x : ℕ → ℕ) : StrictMono (mkStrictMonoAux x) :=
  strictMono_nat_of_lt_succ <| fun n ↦ by grind [mkStrictMonoAux]
/-
**ProbabilityTheory.le_mkStrictMonoAux** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma le_mkStrictMonoAux (x : ℕ → ℕ) : ∀ n, x n ≤ mkStrictMonoAux x n
  | 0 => by simp [mkStrictMonoAux]
  | n + 1 => by grind [mkStrictMonoAux]
/-
**ProbabilityTheory.isPreLocalizingSequence_of_isLocalizingSequence_aux** 是 Math
lib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isPreLocalizingSequence_of_isLocalizingSequence_aux
    {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ (nk : ℕ → ℕ) (T : ℕ → ι), StrictMono nk ∧ Tendsto T atTop atTop ∧
      ∀ n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} ≤ (1 / 2) ^ n := by
  obtain ⟨T, hT, h⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux' hτ hσ
  choose nk hnk using h
  refine ⟨mkStrictMonoAux nk, T, mkStrictMonoAux_strictMono nk, hT,
    fun n ↦ le_trans (EventuallyLE.measure_le ?_) (hnk n)⟩
  filter_upwards [(hσ n).mono] with ω hω
  specialize hω (le_mkStrictMonoAux nk n)
  simp [Set.ofPred]
  grind
/-
**ProbabilityTheory.IsLocalizingSequence.isPrelocalizingSequence_inf_extraction*
* 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.IsLocalizingSequence`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω}   [inst : ConditionallyCompleteLinearOrderBot ι] [inst_1 : Topologi
calSpace ι] [inst_2 : OrderTopology ι]   {𝓕 : MeasureTheory.Filtration ι mΩ} [Se
condCountableTopology ι] [MeasureTheory.IsFiniteMeasure P] [NoMaxOrder ι]   {τ :
 ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι},   ProbabilityTheory.IsLocalizin
gSequence 𝓕 τ P →     (∀ (n : ℕ), ProbabilityTheory.IsLocalizingSequence 𝓕 (σ n)
 P) →       ∃ nk, StrictMono nk ∧ ProbabilityTheory.IsPreLocalizingSequence 𝓕 (f
un i ω => min (τ i ω) (σ i (nk i) ω)) P
参数：∀ (n : ℕ), ProbabilityTheory.IsLocalizingSequence 𝓕 (σ n) P；fun i ω => min (τ
 i ω) (σ i (nk i) ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.Probability.Process.LocalProperty.0.ProbabilityTheory.i
sPreLocalizingSequence_of_isLocalizingSequence_aux`：∀ {ι : Type u_1} {Ω : Type u
_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω}   [inst : Conditional
lyCompleteLinearOrderBot ι] [ins…
· 使用定理 `MeasureTheory.IsStoppingTime.min`：∀ {Ω : Type u_1} {ι : Type u_3} {m : M
easurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtration ι m}   {τ
 π : Ω → WithTop ι},  …
· 使用定理 `ProbabilityTheory.IsPreLocalizingSequence.isStoppingTime`：∀ {ι : Type u_
1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 : Topolog
icalSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
· 使用定理 `ProbabilityTheory.IsLocalizingSequence.toIsPreLocalizingSequence`：∀ {ι :
 Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 :
 TopologicalSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Summable.tsum_mono`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter
 ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [ins
t_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `tsum_geometric_lt_top`：tsum_geometric_lt_top {r : Real>=0∞} : ∑' n, r ^ 
n < ∞ ↔ r < 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsPreLocalizingSequence.tendsto_top`：∀ {ι : Type u_1} 
{Ω : Type u_2} {mΩ : MeasurableSpace Ω} [inst : Preorder ι] [inst_1 : Topologica
lSpace ι]   [inst_2 : OrderTopology ι] {𝓕 :…
· 使用定理 `MeasureTheory.ae_eventually_notMem`：ae_eventually_notMem {s : Nat -> Set
 α} (hs : (∑' i, μ (s i)) != ∞) : forallᵐ x ∂μ, forallᶠ n in atTop, x ∉ s n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 43 条，此处仅展示前 30 条）
-/
lemma IsLocalizingSequence.isPrelocalizingSequence_inf_extraction
    [NoMaxOrder ι] {τ : ℕ → Ω → WithTop ι} {σ : ℕ → ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : ∀ n, IsLocalizingSequence 𝓕 (σ n) P) :
    ∃ nk : ℕ → ℕ, StrictMono nk ∧
      IsPreLocalizingSequence 𝓕 (fun i ω ↦ (τ i ω) ⊓ (σ i (nk i) ω)) P := by
  obtain ⟨nk, T, hnk, hT, hP⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux hτ hσ
  refine ⟨nk, hnk, fun n ↦ (hτ.isStoppingTime n).min ((hσ _).isStoppingTime _), ?_⟩
  have : ∑' n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} < ∞ :=
    lt_of_le_of_lt (ENNReal.summable.tsum_mono ENNReal.summable hP)
      (tsum_geometric_lt_top.2 <| by simp)
  filter_upwards [ae_eventually_notMem this.ne, hτ.tendsto_top] with ω hω hωτ
  exact hωτ.min <| tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hωτ.min <| WithTop.tendsto_coe_atTop.comp hT) tendsto_const_nhds (by grind) (by simp)

variable [DenselyOrdered ι] [NoMaxOrder ι] [Zero E]

/-- A stable property holding locally is idempotent. -/
@[simp]
/-
**ProbabilityTheory.IsStable.locally_locally_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.IsStable`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω}   [inst : ConditionallyCompleteLinearOrderBot ι] [in
st_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι]   {𝓕 : MeasureTheory.Filtr
ation ι mΩ} {X : ι → Ω → E} {p : (ι → Ω → E) → Prop} [SecondCountableTopology ι]
   [MeasureTheory.IsFiniteMeasure P] [DenselyOrdered ι] [NoMaxOrder ι] [inst_7 :
 Zero E] [𝓕.IsRightContinuous],   ProbabilityTheory.IsStable 𝓕 p →     (Probabil
ityTheory.Locally (fun Y => ProbabilityTheory.Locally p 𝓕 Y P) 𝓕 X P ↔ Probabili
tyTheory.Locally p 𝓕 X P)
参数：ι → Ω → E；ProbabilityTheory.Locally (fun Y => ProbabilityTheory.Locally p 𝓕 Y
 P) 𝓕 X P ↔ ProbabilityTheory.Locally p 𝓕 X P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `ProbabilityTheory.IsLocalizingSequence.isPrelocalizingSequence_inf_extra
ction`：∀ {ι : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheo
ry.Measure Ω}   [inst : ConditionallyCompleteLinearOrderBot ι] [ins…
· 使用引理 `ProbabilityTheory.Locally.isLocalizingSequence_localSeq`：isLocalizingSeq
uence_localSeq [Zero E] (hX : Locally p 𝓕 X P) : IsLocalizingSequence 𝓕 hX.local
Seq P
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ProbabilityTheory.IsStable.locally_of_isPreLocalizingSequence`：∀ {ι : Ty
pe u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω}   [inst : ConditionallyCompleteLinearO…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_firstCountableTopology`：∀ (α
 : Type u) [t : TopologicalSpace α] [SecondCountableTopology α], FirstCountableT
opology α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.stoppedProcess_indicator_comm'`：stoppedProcess_indicator_c
omm' [Zero β] {s : Set Ω} : stoppedProcess (fun i => s.indicator (u i)) τ = fun 
i => s.indicator (stoppedProcess u…
· 使用定理 `MeasureTheory.stoppedProcess_stoppedProcess`：stoppedProcess_stoppedProce
ss : stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (σ ⊓ τ)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.indicator_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 (s t : Set α) (f : α → M),   s.indicator (t.indicator f) = (s ∩ t).indicator f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `ProbabilityTheory.Locally.stoppedProcess_localSeq`：stoppedProcess_localS
eq [Zero E] (hX : Locally p 𝓕 X P) (n : Nat) : p (stoppedProcess (fun i => {ω | 
⊥ < hX.localSeq n ω}.indicator (X i)) (…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `ProbabilityTheory.Locally.of_prop`：of_prop [Zero E] (hp : p X) : Locally
 p 𝓕 X P

--- 原说明 ---
A stable property holding locally is idempotent.
-/
lemma IsStable.locally_locally_iff [IsRightContinuous 𝓕] (hp : IsStable 𝓕 p) :
    Locally (fun Y ↦ Locally p 𝓕 Y P) 𝓕 X P ↔ Locally p 𝓕 X P := by
  refine ⟨fun hL ↦ ?_, fun hL ↦ ⟨hL.localSeq, hL.isLocalizingSequence_localSeq,
    fun n ↦ .of_prop <| hL.stoppedProcess_localSeq n⟩⟩
  choose τ hτ₁ hτ₂ using hL.stoppedProcess_localSeq
  obtain ⟨nk, hnk, hpre⟩ :=
    hL.isLocalizingSequence_localSeq.isPrelocalizingSequence_inf_extraction hτ₁
  refine locally_of_isPreLocalizingSequence hp hpre <| fun n ↦ ?_
  convert! hτ₂ n (nk n) using 1 with
  ext i ω
  rw [stoppedProcess_indicator_comm', stoppedProcess_indicator_comm',
    stoppedProcess_stoppedProcess, stoppedProcess_indicator_comm']
  simp only [lt_inf_iff, Set.indicator_indicator]
  congr 1
  · ext; grind
  · simp_rw [inf_comm]
    rfl

/-- If `q` is a stable property and `p` implies `q` locally, then `p` locally implies
`q` locally. -/
/-
**ProbabilityTheory.IsStable.locally_induction** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.IsStable`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω}   [inst : ConditionallyCompleteLinearOrderBot ι] [in
st_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι]   {𝓕 : MeasureTheory.Filtr
ation ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop} [SecondCountableTopology 
ι]   [MeasureTheory.IsFiniteMeasure P] [DenselyOrdered ι] [NoMaxOrder ι] [inst_7
 : Zero E] [𝓕.IsRightContinuous],   ProbabilityTheory.IsStable 𝓕 q →     (∀ (Y :
 ι → Ω → E), p Y → ProbabilityTheory.Locally q 𝓕 Y P) →       ProbabilityTheory.
Locally p 𝓕 X P → ProbabilityTheory.Locally q 𝓕 X P
参数：ι → Ω → E；∀ (Y : ι → Ω → E), p Y → ProbabilityTheory.Locally q 𝓕 Y P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ProbabilityTheory.IsStable.locally_locally_iff`：∀ {ι : Type u_1} {Ω : Ty
pe u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω}   
[inst : ConditionallyCompleteLinearO…
· 使用引理 `ProbabilityTheory.Locally.mono`：mono [Zero E] (hpq : forall X, p X -> q 
X) (hpX : Locally p 𝓕 X P) : Locally q 𝓕 X P

--- 原说明 ---
If `q` is a stable property and `p` implies `q` locally, then `p` locally implie
s
`q` locally.
-/
lemma IsStable.locally_induction [IsRightContinuous 𝓕]
    (hq : IsStable 𝓕 q) (hpq : ∀ Y, p Y → Locally q 𝓕 Y P) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  hq.locally_locally_iff.1 <| hpX.mono hpq

/-- If `p, q, r` are stable properties and `r` and `p` implies locally `q`, then `r` locally
and `p` locally imply `q` locally. -/
/-
**ProbabilityTheory.IsStable.locally_induction** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.IsStable`。
形式化陈述：∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω}   [inst : ConditionallyCompleteLinearOrderBot ι] [in
st_1 : TopologicalSpace ι] [inst_2 : OrderTopology ι]   {𝓕 : MeasureTheory.Filtr
ation ι mΩ} {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop} [SecondCountableTopology 
ι]   [MeasureTheory.IsFiniteMeasure P] [DenselyOrdered ι] [NoMaxOrder ι] [inst_7
 : Zero E] [𝓕.IsRightContinuous],   ProbabilityTheory.IsStable 𝓕 q →     (∀ (Y :
 ι → Ω → E), p Y → ProbabilityTheory.Locally q 𝓕 Y P) →       ProbabilityTheory.
Locally p 𝓕 X P → ProbabilityTheory.Locally q 𝓕 X P
参数：ι → Ω → E；∀ (Y : ι → Ω → E), p Y → ProbabilityTheory.Locally q 𝓕 Y P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ProbabilityTheory.IsStable.locally_locally_iff`：∀ {ι : Type u_1} {Ω : Ty
pe u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω}   
[inst : ConditionallyCompleteLinearO…
· 使用引理 `ProbabilityTheory.Locally.mono`：mono [Zero E] (hpq : forall X, p X -> q 
X) (hpX : Locally p 𝓕 X P) : Locally q 𝓕 X P

--- 原说明 ---
If `p, q, r` are stable properties and `r` and `p` implies locally `q`, then `r`
 locally
and `p` locally imply `q` locally.
-/
lemma IsStable.locally_induction₂ {r : (ι → Ω → E) → Prop} [IsRightContinuous 𝓕]
    (hrpq : ∀ Y, r Y → p Y → Locally q 𝓕 Y P)
    (hr : IsStable 𝓕 r) (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
    (hrX : Locally r 𝓕 X P) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
  hq.locally_induction (p := fun Y ↦ r Y ∧ p Y) (and_imp.2 <| hrpq ·) <|
    (hr.locally_and_iff hp).2 ⟨hrX, hpX⟩

end

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory

