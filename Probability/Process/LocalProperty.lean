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

/--
Definition of `IsPreLocalizingSequence` / `IsPreLocalizingSequence` 的定义

English:
structure IsPreLocalizingSequence
  parameters: [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
  axioms and operations (2):
    - isStoppingTime : forall n, IsStoppingTime 𝓕 (τ n)
    - tendsto_top : forallᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)

中文:
结构 是PreLocalizingSequence
  参数: [预序 ι] [拓扑空间 ι] [Order拓扑 ι]
  公理与运算 (2 个):
    - isStoppingTime : 对任意 n, IsStoppingTime 𝓕 (τ n)
    - tendsto_top : 对任意ᵐ ω ∂P, 收敛 (τ · ω) atTop (𝓝 ⊤)

Depends on / 依赖: IsStoppingTime, Tendsto, isStoppingTime, tendsto_top, volume_tac
-/
structure IsPreLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : Nat -> Ω -> WithTop ι) (P : Measure Ω := by volume_tac) :
    Prop where
  isStoppingTime : forall n, IsStoppingTime 𝓕 (τ n)
  tendsto_top : forallᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)

/--
Definition of `IsLocalizingSequence` / `IsLocalizingSequence` 的定义

English:
structure IsLocalizingSequence
  parameters: [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
  extends: IsPreLocalizingSequence 𝓕 τ P
  axioms and operations (1):
    - mono : forallᵐ ω ∂P, Monotone (τ · ω)

中文:
结构 是LocalizingSequence
  参数: [预序 ι] [拓扑空间 ι] [Order拓扑 ι]
  继承: 是PreLocalizingSequence 𝓕 τ P
  公理与运算 (1 个):
    - mono : 对任意ᵐ ω ∂P, 递增 (τ · ω)

Depends on / 依赖: IsPreLocalizingSequence, Monotone, extends, volume_tac
-/
structure IsLocalizingSequence [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (τ : Nat -> Ω -> WithTop ι)
    (P : Measure Ω := by volume_tac) extends IsPreLocalizingSequence 𝓕 τ P where
  mono : forallᵐ ω ∂P, Monotone (τ · ω)

/--
lemma `isLocalizingSequence_const_top` / 引理 `isLocalizingSequence_const_top`

English:
lemma isLocalizingSequence_const_top
  statement: [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
  proof: by simp [IsStoppingTime]
  mono := ae_of_all _ fun _ _ _ _ => by simp
  tendsto_top := ae_of_all _ fun _ => tendsto_const_nhds

中文:
引理 isLocalizingSequence_const_top
  结论: [预序 ι] [拓扑空间 ι] [Order拓扑 ι]
  证明: by simp [IsStoppingTime]
  mono := ae_of_all _ fun _ _ _ _ => by simp
  tendsto_top := ae_of_all _ fun _ => tendsto_const_nhds

Depends on / 依赖: IsStoppingTime, ae_of_all, tendsto_const_nhds, tendsto_top
-/
lemma isLocalizingSequence_const_top [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι mΩ) (P : Measure Ω) : IsLocalizingSequence 𝓕 (fun _ _ => ⊤) P where
  isStoppingTime n := by simp [IsStoppingTime]
  mono := ae_of_all _ fun _ _ _ _ => by simp
  tendsto_top := ae_of_all _ fun _ => tendsto_const_nhds

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ} {X : ι -> Ω -> E} {p q : (ι -> Ω -> E) -> Prop}

/--
lemma `IsLocalizingSequence.min` / 引理 `IsLocalizingSequence.min`

English:
lemma IsLocalizingSequence.min
  statement: [TopologicalSpace ι] [OrderTopology ι]
  proof: (hτ.isStoppingTime n).min (hσ.isStoppingTime n)
  mono := by filter_upwards [hτ.mono, hσ.mono] with ω hτω hσω using hτω.min hσω
  tendsto_top := by
    filter_upwards [hτ.tendsto_top, hσ.tendsto_top] with ω hτω hσω using hτω.min hσω

中文:
引理 是LocalizingSequence.最小值
  结论: [拓扑空间 ι] [Order拓扑 ι]
  证明: (hτ.isStoppingTime n).min (hσ.isStoppingTime n)
  mono := by filter_upwards [hτ.mono, hσ.mono] with ω hτω hσω using hτω.min hσω
  tendsto_top := by
    filter_upwards [hτ.tendsto_top, hσ.tendsto_top] with ω hτω hσω using hτω.min hσω
-/
protected lemma IsLocalizingSequence.min [TopologicalSpace ι] [OrderTopology ι]
    {τ σ : Nat -> Ω -> WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : IsLocalizingSequence 𝓕 σ P) :
    IsLocalizingSequence 𝓕 (min τ σ) P where
  isStoppingTime n := (hτ.isStoppingTime n).min (hσ.isStoppingTime n)
  mono := by filter_upwards [hτ.mono, hσ.mono] with ω hτω hσω using hτω.min hσω
  tendsto_top := by
    filter_upwards [hτ.tendsto_top, hσ.tendsto_top] with ω hτω hσω using hτω.min hσω

variable [OrderBot ι]

/--
Definition of `Locally` / `Locally` 的定义

English:
definition Locally
  signature: [TopologicalSpace ι] [OrderTopology ι] [Zero E]
  body: exists τ : Nat -> Ω -> WithTop ι, IsLocalizingSequence 𝓕 τ P ∧
    forall n, p (stoppedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))

中文:
定义 Locally
  签名: [拓扑空间 ι] [Order拓扑 ι] [零 E]
  定义体: exists τ : Nat -> Ω -> WithTop ι, IsLocalizingSequence 𝓕 τ P ∧
    forall n, p (stoppedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))

Depends on / 依赖: IsLocalizingSequence, WithTop, indicator, stoppedProcess, volume_tac
-/
def Locally [TopologicalSpace ι] [OrderTopology ι] [Zero E]
    (p : (ι -> Ω -> E) -> Prop) (𝓕 : Filtration ι mΩ)
    (X : ι -> Ω -> E) (P : Measure Ω := by volume_tac) : Prop :=
  exists τ : Nat -> Ω -> WithTop ι, IsLocalizingSequence 𝓕 τ P ∧
    forall n, p (stoppedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))

namespace Locally

variable [TopologicalSpace ι] [OrderTopology ι]

/-- A localizing sequence, witness of the local property of the stochastic process. -/
noncomputable
/--
Definition of `localSeq` / `localSeq` 的定义

English:
definition localSeq
  signature: [Zero E] (hX : Locally p 𝓕 X P)
  body: hX.choose

中文:
定义 localSeq
  签名: [零 E] (hX : Locally p 𝓕 X P)
  定义体: hX.choose

Depends on / 依赖: hX.choose
-/
def localSeq [Zero E] (hX : Locally p 𝓕 X P) :
    Nat -> Ω -> WithTop ι :=
  hX.choose

/--
lemma `isLocalizingSequence_localSeq` / 引理 `isLocalizingSequence_localSeq`

English:
lemma isLocalizingSequence_localSeq
  given: [Zero E] (hX : Locally p 𝓕 X P)
  proof: hX.choose_spec.1

中文:
引理 isLocalizingSequence_localSeq
  条件: [零 E] (hX : Locally p 𝓕 X P)
  证明: hX.choose_spec.1

Depends on / 依赖: choose_spec, hX.choose_spec
-/
lemma isLocalizingSequence_localSeq [Zero E] (hX : Locally p 𝓕 X P) :
    IsLocalizingSequence 𝓕 hX.localSeq P :=
  hX.choose_spec.1

/--
lemma `stoppedProcess_localSeq` / 引理 `stoppedProcess_localSeq`

English:
lemma stoppedProcess_localSeq
  given: [Zero E] (hX : Locally p 𝓕 X P) (n : Nat)
  proof: hX.choose_spec.2 n

中文:
引理 stoppedProcess_localSeq
  条件: [零 E] (hX : Locally p 𝓕 X P) (n : 自然数)
  证明: hX.choose_spec.2 n

Depends on / 依赖: choose_spec, hX.choose_spec
-/
lemma stoppedProcess_localSeq [Zero E] (hX : Locally p 𝓕 X P) (n : Nat) :
    p (stoppedProcess (fun i => {ω | ⊥ < hX.localSeq n ω}.indicator (X i)) (hX.localSeq n)) :=
  hX.choose_spec.2 n

/--
lemma `of_prop` / 引理 `of_prop`

English:
lemma of_prop
  given: [Zero E] (hp : p X)
  statement: Locally p 𝓕 X P
  proof: ⟨fun n _ => ⊤, isLocalizingSequence_const_top _ _, by simpa⟩

中文:
引理 of_prop
  条件: [零 E] (hp : p X)
  结论: Locally p 𝓕 X P
  证明: ⟨fun n _ => ⊤, isLocalizingSequence_const_top _ _, by simpa⟩

Depends on / 依赖: isLocalizingSequence_const_top
-/
lemma of_prop [Zero E] (hp : p X) : Locally p 𝓕 X P :=
  ⟨fun n _ => ⊤, isLocalizingSequence_const_top _ _, by simpa⟩

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  given: [Zero E] (hpq : forall X, p X -> q X) (hpX : Locally p 𝓕 X P)
  proof: ⟨hpX.localSeq, hpX.isLocalizingSequence_localSeq, fun n => hpq _ hpX.stoppedProcess_localSeq n⟩

中文:
引理 mono
  条件: [零 E] (hpq : 对任意 X, p X -> q X) (hpX : Locally p 𝓕 X P)
  证明: ⟨hpX.localSeq, hpX.isLocalizingSequence_localSeq, fun n => hpq _ hpX.stoppedProcess_localSeq n⟩

Depends on / 依赖: hpX.isLocalizingSequence_localSeq, hpX.localSeq, hpX.stoppedProcess_localSeq, isLocalizingSequence_localSeq, localSeq, stoppedProcess_localSeq
-/
lemma mono [Zero E] (hpq : forall X, p X -> q X) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
⟨hpX.localSeq, hpX.isLocalizingSequence_localSeq, fun n => hpq _ hpX.stoppedProcess_localSeq n⟩

/--
lemma `of_and` / 引理 `of_and`

English:
lemma of_and
  given: [Zero E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P)
  proof: ⟨hX.mono fun _ => And.left, hX.mono fun _ => And.right⟩

中文:
引理 of_and
  条件: [零 E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P)
  证明: ⟨hX.mono fun _ => And.left, hX.mono fun _ => And.right⟩

Depends on / 依赖: And.left, And.right, hX.mono
-/
lemma of_and [Zero E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P) :
    Locally p 𝓕 X P ∧ Locally q 𝓕 X P :=
⟨hX.mono fun _ => And.left, hX.mono fun _ => And.right⟩

/--
lemma `left` / 引理 `left`

English:
lemma left
  given: [Zero E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P)
  proof: hX.of_and.left

中文:
引理 left
  条件: [零 E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P)
  证明: hX.of_and.left

Depends on / 依赖: hX.of_and.left, of_and
-/
lemma left [Zero E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P) :
    Locally p 𝓕 X P :=
  hX.of_and.left

/--
lemma `right` / 引理 `right`

English:
lemma right
  given: [Zero E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P)
  proof: hX.of_and.right

中文:
引理 right
  条件: [零 E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P)
  证明: hX.of_and.right

Depends on / 依赖: hX.of_and.right, of_and
-/
lemma right [Zero E] (hX : Locally (fun Y => p Y ∧ q Y) 𝓕 X P) :
    Locally q 𝓕 X P :=
  hX.of_and.right

end Locally

variable [Zero E]

/--
Definition of `IsStable` / `IsStable` 的定义

English:
definition IsStable
  body: forall X : ι -> Ω -> E, p X -> forall τ : Ω -> WithTop ι, IsStoppingTime 𝓕 τ ->
    p (stoppedProcess (fun i => {ω | ⊥ < τ ω}.indicator (X i)) τ)

中文:
定义 IsStable
  定义体: forall X : ι -> Ω -> E, p X -> forall τ : Ω -> WithTop ι, IsStoppingTime 𝓕 τ ->
    p (stoppedProcess (fun i => {ω | ⊥ < τ ω}.indicator (X i)) τ)

Depends on / 依赖: IsStoppingTime, WithTop, indicator, stoppedProcess
-/
def IsStable
    (𝓕 : Filtration ι mΩ) (p : (ι -> Ω -> E) -> Prop) : Prop :=
  forall X : ι -> Ω -> E, p X -> forall τ : Ω -> WithTop ι, IsStoppingTime 𝓕 τ ->
    p (stoppedProcess (fun i => {ω | ⊥ < τ ω}.indicator (X i)) τ)

/--
lemma `IsStable.and` / 引理 `IsStable.and`

English:
lemma IsStable.and
  given: (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
  proof: fun _ hX τ hτ => ⟨hp _ hX.left τ hτ, hq _ hX.right τ hτ⟩

中文:
引理 IsStable.and
  条件: (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
  证明: fun _ hX τ hτ => ⟨hp _ hX.left τ hτ, hq _ hX.right τ hτ⟩
-/
protected lemma IsStable.and (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q) :
    IsStable 𝓕 (fun X => p X ∧ q X) :=
  fun _ hX τ hτ => ⟨hp _ hX.left τ hτ, hq _ hX.right τ hτ⟩

variable [TopologicalSpace ι] [OrderTopology ι]

/--
lemma `IsStable.locally` / 引理 `IsStable.locally`

English:
lemma IsStable.locally
  given: (hp : IsStable 𝓕 p)
  proof: by
  refine fun X hX τ hτ => ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n => ?_⟩
  simp_rw [← stoppedProcess_indicator_comm', Set.indicator_indicator, Set.inter_comm,
    ← Set.indicator_indicator, stoppedProcess_stoppedProcess, inf_comm,
    stoppedProcess_indicator_comm', ← stoppedProcess

中文:
引理 IsStable.locally
  条件: (hp : IsStable 𝓕 p)
  证明: by
  refine fun X hX τ hτ => ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n => ?_⟩
  simp_rw [← stoppedProcess_indicator_comm', Set.indicator_indicator, Set.inter_comm,
    ← Set.indicator_indicator, stoppedProcess_stoppedProcess, inf_comm,
    stoppedProcess_indicator_comm', ← stoppedProcess

Depends on / 依赖: Set.indicator_indicator, Set.inter_comm, hX.isLocalizingSequence_localSeq, hX.localSeq, hX.stoppedProcess_localSeq, indicator_indicator, inf_comm, inter_comm, isLocalizingSequence_localSeq, localSeq, simp_rw, stoppedProcess_indicator_comm, stoppedProcess_localSeq, stoppedProcess_stoppedProcess
-/
lemma IsStable.locally (hp : IsStable 𝓕 p) :
    IsStable 𝓕 (fun Y => Locally p 𝓕 Y P) := by
  refine fun X hX τ hτ => ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n => ?_⟩
  simp_rw [← stoppedProcess_indicator_comm', Set.indicator_indicator, Set.inter_comm,
    ← Set.indicator_indicator, stoppedProcess_stoppedProcess, inf_comm,
    stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess]
  exact hp _ (hX.stoppedProcess_localSeq n) τ hτ

/--
lemma `IsStable.locally_and_iff` / 引理 `IsStable.locally_and_iff`

English:
lemma IsStable.locally_and_iff
  given: (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
  proof: by
  refine ⟨Locally.of_and, fun ⟨hpX, hqX⟩ =>
    ⟨_, hpX.isLocalizingSequence_localSeq.min hqX.isLocalizingSequence_localSeq, fun n => ?_⟩⟩
  suffices forall (p q : (ι -> Ω -> E) -> Prop) (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
      (hpX : Locally p 𝓕 X P) (hqX : Locally q 𝓕 X P),
      p (stoppe

中文:
引理 IsStable.locally_and_iff
  条件: (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
  证明: by
  refine ⟨Locally.of_and, fun ⟨hpX, hqX⟩ =>
    ⟨_, hpX.isLocalizingSequence_localSeq.min hqX.isLocalizingSequence_localSeq, fun n => ?_⟩⟩
  suffices forall (p q : (ι -> Ω -> E) -> Prop) (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
      (hpX : Locally p 𝓕 X P) (hqX : Locally q 𝓕 X P),
      p (stoppe

Depends on / 依赖: IsStable, Locally, Locally.of_and, hpX.isLocalizingSequence_localSeq.min, hpX.localSeq, hqX.isLocalizingSequence_localSeq, hqX.localSeq, indicator, inf_comm, isLocalizingSequence_localSeq, localSeq, of_and, simp_rw, stoppedProcess
-/
lemma IsStable.locally_and_iff (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q) :
    Locally (fun Y => p Y ∧ q Y) 𝓕 X P ↔ Locally p 𝓕 X P ∧ Locally q 𝓕 X P := by
  refine ⟨Locally.of_and, fun ⟨hpX, hqX⟩ =>
    ⟨_, hpX.isLocalizingSequence_localSeq.min hqX.isLocalizingSequence_localSeq, fun n => ?_⟩⟩
  suffices forall (p q : (ι -> Ω -> E) -> Prop) (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
      (hpX : Locally p 𝓕 X P) (hqX : Locally q 𝓕 X P),
      p (stoppedProcess (fun i => {ω | ⊥ < (hpX.localSeq ⊓ hqX.localSeq) n ω}.indicator (X i))
      ((hpX.localSeq ⊓ hqX.localSeq) n)) by
    refine ⟨this p q hp hq hpX hqX, ?_⟩
    simp_rw [inf_comm hpX.localSeq]
    exact this q p hq hp hqX hpX
  intro p q hp hq hpX hqX
  convert!
hp _ (hpX.stoppedProcess_localSeq n) _
      hqX.isLocalizingSequence_localSeq.isStoppingTime n using 1
  ext i ω
  simp_rw [stoppedProcess_indicator_comm, Pi.inf_apply, lt_inf_iff, inf_comm (hpX.localSeq n)]
  rw [← stoppedProcess_stoppedProcess]; rw [← stoppedProcess_indicator_comm]; rw [Set.ofPred_and]; rw [Set.inter_comm]
  simp_rw [← Set.indicator_indicator]
  rfl

end LinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {𝓕 : Filtration ι mΩ} {X : ι -> Ω -> E} {p q : (ι -> Ω -> E) -> Prop}

/--
lemma `IsPreLocalizingSequence.isLocalizingSequence_biInf` / 引理 `IsPreLocalizingSequence.isLocalizingSequence_biInf`

English:
lemma IsPreLocalizingSequence.isLocalizingSequence_biInf
  proof: IsStoppingTime.biInf (Set.to_countable {j | j >= n})
    (fun j _ => hτ.isStoppingTime j)
mono := ae_of_all _ fun ω n m hnm => iInf_le_iInf_of_subset fun k hk => hnm.trans hk
  tendsto_top := by
    filter_upwards [hτ.tendsto_top] with ω hω
    replace hω := hω.liminf_eq
    rw [liminf_eq_iSup_iInf_

中文:
引理 是PreLocalizingSequence.isLocalizingSequence_biInf
  证明: IsStoppingTime.biInf (Set.to_countable {j | j >= n})
    (fun j _ => hτ.isStoppingTime j)
mono := ae_of_all _ fun ω n m hnm => iInf_le_iInf_of_subset fun k hk => hnm.trans hk
  tendsto_top := by
    filter_upwards [hτ.tendsto_top] with ω hω
    replace hω := hω.liminf_eq
    rw [liminf_eq_iSup_iInf_

Depends on / 依赖: IsStoppingTime, IsStoppingTime.biInf, Set.to_countable, to_countable
-/
lemma IsPreLocalizingSequence.isLocalizingSequence_biInf
    [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
    {τ : Nat -> Ω -> WithTop ι} [IsRightContinuous 𝓕] (hτ : IsPreLocalizingSequence 𝓕 τ P) :
    IsLocalizingSequence 𝓕 (fun i ω => ⨅ j >= i, τ j ω) P where
  isStoppingTime n := IsStoppingTime.biInf (Set.to_countable {j | j >= n})
    (fun j _ => hτ.isStoppingTime j)
mono := ae_of_all _ fun ω n m hnm => iInf_le_iInf_of_subset fun k hk => hnm.trans hk
  tendsto_top := by
    filter_upwards [hτ.tendsto_top] with ω hω
    replace hω := hω.liminf_eq
    rw [liminf_eq_iSup_iInf_of_nat] at hω
    rw [← hω]
    refine tendsto_atTop_iSup fun n m hnm => ?_
    simp [iInf_le_iff]
    grind

/--
lemma `IsStable.locally_of_isPreLocalizingSequence` / 引理 `IsStable.locally_of_isPreLocalizingSequence`

English:
lemma IsStable.locally_of_isPreLocalizingSequence
  proof: by
  refine ⟨_, hτ.isLocalizingSequence_biInf, fun n => ?_⟩
  rw [stoppedProcess_indicator_comm']; rw [← stoppedProcess_stoppedProcess_of_le_right
    (τ := fun ω => τ n ω) (fun _ => (iInf_le _ n).trans <| iInf_le _ le_rfl)]; rw [← stoppedProcess_indicator_comm']
  convert!
hp _ (hpτ n) (fun ω => ⨅ 

中文:
引理 IsStable.locally_of_isPreLocalizingSequence
  证明: by
  refine ⟨_, hτ.isLocalizingSequence_biInf, fun n => ?_⟩
  rw [stoppedProcess_indicator_comm']; rw [← stoppedProcess_stoppedProcess_of_le_right
    (τ := fun ω => τ n ω) (fun _ => (iInf_le _ n).trans <| iInf_le _ le_rfl)]; rw [← stoppedProcess_indicator_comm']
  convert!
hp _ (hpτ n) (fun ω => ⨅ 

Depends on / 依赖: Set.indicator_indicator, convert, iInf_le, indicator_indicator, isLocalizingSequence_biInf, isLocalizingSequence_biInf.isStoppingTime, isStoppingTime, le_rfl, lt_of_lt_of_le, stoppedProcess_indicator_comm, stoppedProcess_stoppedProcess_of_le_right
-/
lemma IsStable.locally_of_isPreLocalizingSequence
    [Zero E] [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι] {τ : Nat -> Ω -> WithTop ι}
    (hp : IsStable 𝓕 p) [IsRightContinuous 𝓕] (hτ : IsPreLocalizingSequence 𝓕 τ P)
    (hpτ : forall n, p (stoppedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))) :
    Locally p 𝓕 X P := by
  refine ⟨_, hτ.isLocalizingSequence_biInf, fun n => ?_⟩
  rw [stoppedProcess_indicator_comm']; rw [← stoppedProcess_stoppedProcess_of_le_right
    (τ := fun ω => τ n ω) (fun _ => (iInf_le _ n).trans <| iInf_le _ le_rfl)]; rw [← stoppedProcess_indicator_comm']
  convert!
hp _ (hpτ n) (fun ω => ⨅ j >= n, τ j ω) hτ.isLocalizingSequence_biInf.isStoppingTime n using 2
  ext i ω
  rw [stoppedProcess_indicator_comm']; rw [Set.indicator_indicator]
  congr with ω
exact ⟨fun h => ⟨h, lt_of_lt_of_le h (iInf_le _ n).trans (iInf_le _ le_rfl)⟩, fun h => h.1⟩

section

variable [SecondCountableTopology ι] [IsFiniteMeasure P]

/--
lemma `isPreLocalizingSequence_of_isLocalizingSequence_aux'` / 引理 `isPreLocalizingSequence_of_isLocalizingSequence_aux'`

English:
lemma isPreLocalizingSequence_of_isLocalizingSequence_aux'
  proof: by
  obtain ⟨T, -, hT⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
  refine ⟨T, hT, fun n => ?_⟩
  by_contra! hn
  suffices (1 / 2) ^ n <= P (⋂ k : Nat, {ω | σ n k ω < min (τ n ω) (T n)}) by
refine (by simp : ¬ (1 / 2 : Real>=0∞) ^ n <= 0) this.trans nonpos_iff_eq_zero.2 ?_
    rw [measure_e

中文:
引理 isPreLocalizingSequence_of_isLocalizingSequence_aux'
  证明: by
  obtain ⟨T, -, hT⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
  refine ⟨T, hT, fun n => ?_⟩
  by_contra! hn
  suffices (1 / 2) ^ n <= P (⋂ k : Nat, {ω | σ n k ω < min (τ n ω) (T n)}) by
refine (by simp : ¬ (1 / 2 : Real>=0∞) ^ n <= 0) this.trans nonpos_iff_eq_zero.2 ?_
    rw [measure_e
-/
private lemma isPreLocalizingSequence_of_isLocalizingSequence_aux'
    {τ : Nat -> Ω -> WithTop ι} {σ : Nat -> Nat -> Ω -> WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : forall n, IsLocalizingSequence 𝓕 (σ n) P) :
    exists T : Nat -> ι, Tendsto T atTop atTop ∧
      forall n, exists k, P {ω | σ n k ω < min (τ n ω) (T n)} <= (1 / 2) ^ n := by
  obtain ⟨T, -, hT⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
  refine ⟨T, hT, fun n => ?_⟩
  by_contra! hn
  suffices (1 / 2) ^ n <= P (⋂ k : Nat, {ω | σ n k ω < min (τ n ω) (T n)}) by
refine (by simp : ¬ (1 / 2 : Real>=0∞) ^ n <= 0) this.trans nonpos_iff_eq_zero.2 ?_
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [(hσ n).tendsto_top] with ω hTop hmem
    simp_rw [WithTop.tendsto_nhds_top_iff, eventually_atTop] at hTop
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hmem
    obtain ⟨N, hN⟩ := hTop (T n)
    specialize hN N le_rfl
    specialize hmem N
    grind
  rw [measure_iInter_of_ae_antitone]; rw [le_iInf_iff]
  · exact fun k => (hn k).le
  · filter_upwards [(hσ n).mono] with ω hω
    intros i j hij
    specialize hω hij
    simp [Set.ofPred] at *
    grind
  · refine fun i => .nullMeasurableSet ?_
    simp_rw [lt_inf_iff, Set.ofPred_and]
    exact MeasurableSet.inter
      (measurableSet_lt ((hσ n).isStoppingTime i).measurable' (hτ.isStoppingTime n).measurable')
 measurableSet_lt ((hσ n).isStoppingTime i).measurable' measurable_const
  · exact ⟨0, measure_ne_top P _⟩

/--
Definition of `mkStrictMonoAux` / `mkStrictMonoAux` 的定义

English:
definition mkStrictMonoAux
  signature: (x : Nat -> Nat)

中文:
定义 mkStrictMonoAux
  签名: (x : 自然数 -> 自然数)
-/
private def mkStrictMonoAux (x : Nat -> Nat) : Nat -> Nat
  | 0 => x 0
  | n + 1 => max (x (n + 1)) (mkStrictMonoAux x n) + 1

/--
lemma `mkStrictMonoAux_strictMono` / 引理 `mkStrictMonoAux_strictMono`

English:
lemma mkStrictMonoAux_strictMono
  given: (x : Nat -> Nat)
  statement: StrictMono (mkStrictMonoAux x)
  proof: strictMono_nat_of_lt_succ fun n => by grind [mkStrictMonoAux]

中文:
引理 mkStrictMonoAux_strictMono
  条件: (x : 自然数 -> 自然数)
  结论: 严格递增 (mkStrictMonoAux x)
  证明: strictMono_nat_of_lt_succ fun n => by grind [mkStrictMonoAux]
-/
private lemma mkStrictMonoAux_strictMono (x : Nat -> Nat) : StrictMono (mkStrictMonoAux x) :=
strictMono_nat_of_lt_succ fun n => by grind [mkStrictMonoAux]

/--
lemma `le_mkStrictMonoAux` / 引理 `le_mkStrictMonoAux`

English:
lemma le_mkStrictMonoAux
  given: (x : Nat -> Nat)
  statement: forall n, x n <= mkStrictMonoAux x n

中文:
引理 le_mkStrictMonoAux
  条件: (x : 自然数 -> 自然数)
  结论: 对任意 n, x n <= mkStrictMonoAux x n
-/
private lemma le_mkStrictMonoAux (x : Nat -> Nat) : forall n, x n <= mkStrictMonoAux x n
  | 0 => by simp [mkStrictMonoAux]
  | n + 1 => by grind [mkStrictMonoAux]

/--
lemma `isPreLocalizingSequence_of_isLocalizingSequence_aux` / 引理 `isPreLocalizingSequence_of_isLocalizingSequence_aux`

English:
lemma isPreLocalizingSequence_of_isLocalizingSequence_aux
  proof: by
  obtain ⟨T, hT, h⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux' hτ hσ
  choose nk hnk using h
  refine ⟨mkStrictMonoAux nk, T, mkStrictMonoAux_strictMono nk, hT,
    fun n => le_trans (EventuallyLE.measure_le ?_) (hnk n)⟩
  filter_upwards [(hσ n).mono] with ω hω
  specialize hω (le_mk

中文:
引理 isPreLocalizingSequence_of_isLocalizingSequence_aux
  证明: by
  obtain ⟨T, hT, h⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux' hτ hσ
  choose nk hnk using h
  refine ⟨mkStrictMonoAux nk, T, mkStrictMonoAux_strictMono nk, hT,
    fun n => le_trans (EventuallyLE.measure_le ?_) (hnk n)⟩
  filter_upwards [(hσ n).mono] with ω hω
  specialize hω (le_mk
-/
private lemma isPreLocalizingSequence_of_isLocalizingSequence_aux
    {τ : Nat -> Ω -> WithTop ι} {σ : Nat -> Nat -> Ω -> WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : forall n, IsLocalizingSequence 𝓕 (σ n) P) :
    exists (nk : Nat -> Nat) (T : Nat -> ι), StrictMono nk ∧ Tendsto T atTop atTop ∧
      forall n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} <= (1 / 2) ^ n := by
  obtain ⟨T, hT, h⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux' hτ hσ
  choose nk hnk using h
  refine ⟨mkStrictMonoAux nk, T, mkStrictMonoAux_strictMono nk, hT,
    fun n => le_trans (EventuallyLE.measure_le ?_) (hnk n)⟩
  filter_upwards [(hσ n).mono] with ω hω
  specialize hω (le_mkStrictMonoAux nk n)
  simp [Set.ofPred]
  grind

/--
lemma `IsLocalizingSequence.isPrelocalizingSequence_inf_extraction` / 引理 `IsLocalizingSequence.isPrelocalizingSequence_inf_extraction`

English:
lemma IsLocalizingSequence.isPrelocalizingSequence_inf_extraction
  proof: by
  obtain ⟨nk, T, hnk, hT, hP⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux hτ hσ
  refine ⟨nk, hnk, fun n => (hτ.isStoppingTime n).min ((hσ _).isStoppingTime _), ?_⟩
  have : ∑' n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} < ∞ :=
    lt_of_le_of_lt (ENNReal.summable.tsum_mono ENNReal.sum

中文:
引理 是LocalizingSequence.isPrelocalizingSequence_inf_extraction
  证明: by
  obtain ⟨nk, T, hnk, hT, hP⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux hτ hσ
  refine ⟨nk, hnk, fun n => (hτ.isStoppingTime n).min ((hσ _).isStoppingTime _), ?_⟩
  have : ∑' n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} < ∞ :=
    lt_of_le_of_lt (ENNReal.summable.tsum_mono ENNReal.sum

Depends on / 依赖: ENNReal, ENNReal.summable, ENNReal.summable.tsum_mono, WithTop, WithTop.tendsto_co, ae_eventually_notMem, filter_upwards, isPreLocalizingSequence_of_isLocalizingSequence_aux, isStoppingTime, lt_of_le_of_lt, summable, tendsto_co, tendsto_of_tendsto_of_tendsto_of_le_of_le, tendsto_top, this.ne, tsum_geometric_lt_top, tsum_mono
-/
lemma IsLocalizingSequence.isPrelocalizingSequence_inf_extraction
    [NoMaxOrder ι] {τ : Nat -> Ω -> WithTop ι} {σ : Nat -> Nat -> Ω -> WithTop ι}
    (hτ : IsLocalizingSequence 𝓕 τ P) (hσ : forall n, IsLocalizingSequence 𝓕 (σ n) P) :
    exists nk : Nat -> Nat, StrictMono nk ∧
      IsPreLocalizingSequence 𝓕 (fun i ω => (τ i ω) ⊓ (σ i (nk i) ω)) P := by
  obtain ⟨nk, T, hnk, hT, hP⟩ := isPreLocalizingSequence_of_isLocalizingSequence_aux hτ hσ
  refine ⟨nk, hnk, fun n => (hτ.isStoppingTime n).min ((hσ _).isStoppingTime _), ?_⟩
  have : ∑' n, P {ω | σ n (nk n) ω < min (τ n ω) (T n)} < ∞ :=
    lt_of_le_of_lt (ENNReal.summable.tsum_mono ENNReal.summable hP)
      (tsum_geometric_lt_top.2 <| by simp)
  filter_upwards [ae_eventually_notMem this.ne, hτ.tendsto_top] with ω hω hωτ
exact hωτ.min tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hωτ.min <| WithTop.tendsto_coe_atTop.comp hT) tendsto_const_nhds (by grind) (by simp)

variable [DenselyOrdered ι] [NoMaxOrder ι] [Zero E]

/-- A stable property holding locally is idempotent. -/
@[simp]
/--
lemma `IsStable.locally_locally_iff` / 引理 `IsStable.locally_locally_iff`

English:
lemma IsStable.locally_locally_iff
  given: [IsRightContinuous 𝓕] (hp : IsStable 𝓕 p)
  proof: by
  refine ⟨fun hL => ?_, fun hL => ⟨hL.localSeq, hL.isLocalizingSequence_localSeq,
fun n => .of_prop hL.stoppedProcess_localSeq n⟩⟩
  choose τ hτ₁ hτ₂ using hL.stoppedProcess_localSeq
  obtain ⟨nk, hnk, hpre⟩ :=
    hL.isLocalizingSequence_localSeq.isPrelocalizingSequence_inf_extraction hτ₁
refine

中文:
引理 IsStable.locally_locally_iff
  条件: [是RightContinuous 𝓕] (hp : IsStable 𝓕 p)
  证明: by
  refine ⟨fun hL => ?_, fun hL => ⟨hL.localSeq, hL.isLocalizingSequence_localSeq,
fun n => .of_prop hL.stoppedProcess_localSeq n⟩⟩
  choose τ hτ₁ hτ₂ using hL.stoppedProcess_localSeq
  obtain ⟨nk, hnk, hpre⟩ :=
    hL.isLocalizingSequence_localSeq.isPrelocalizingSequence_inf_extraction hτ₁
refine

Depends on / 依赖: convert, hL.isLocalizingSequence_localSeq, hL.isLocalizingSequence_localSeq.isPrelocalizingSequence_inf_extraction, hL.localSeq, hL.stoppedProcess_localSeq, isLocalizingSequence_localSeq, isPrelocalizingSequence_inf_extraction, localSeq, locally_of_isPreLocalizingSequence, of_prop, stoppedProcess_indicator_comm, stoppedProcess_localSeq, stoppedProcess_stoppedProcess
-/
lemma IsStable.locally_locally_iff [IsRightContinuous 𝓕] (hp : IsStable 𝓕 p) :
    Locally (fun Y => Locally p 𝓕 Y P) 𝓕 X P ↔ Locally p 𝓕 X P := by
  refine ⟨fun hL => ?_, fun hL => ⟨hL.localSeq, hL.isLocalizingSequence_localSeq,
fun n => .of_prop hL.stoppedProcess_localSeq n⟩⟩
  choose τ hτ₁ hτ₂ using hL.stoppedProcess_localSeq
  obtain ⟨nk, hnk, hpre⟩ :=
    hL.isLocalizingSequence_localSeq.isPrelocalizingSequence_inf_extraction hτ₁
refine locally_of_isPreLocalizingSequence hp hpre fun n => ?_
  convert! hτ₂ n (nk n) using 1 with
  ext i ω
  rw [stoppedProcess_indicator_comm']; rw [stoppedProcess_indicator_comm']; rw [stoppedProcess_stoppedProcess]; rw [stoppedProcess_indicator_comm']
  simp only [lt_inf_iff, Set.indicator_indicator]
  congr 1
  · ext; grind
  · simp_rw [inf_comm]
    rfl

/--
lemma `IsStable.locally_induction` / 引理 `IsStable.locally_induction`

English:
lemma IsStable.locally_induction
  statement: [IsRightContinuous 𝓕]
  proof: hq.locally_locally_iff.1 hpX.mono hpq

中文:
引理 IsStable.locally_induction
  结论: [是RightContinuous 𝓕]
  证明: hq.locally_locally_iff.1 hpX.mono hpq

Depends on / 依赖: hpX.mono, hq.locally_locally_iff, locally_locally_iff
-/
lemma IsStable.locally_induction [IsRightContinuous 𝓕]
    (hq : IsStable 𝓕 q) (hpq : forall Y, p Y -> Locally q 𝓕 Y P) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
hq.locally_locally_iff.1 hpX.mono hpq

/--
lemma `IsStable.locally_induction₂` / 引理 `IsStable.locally_induction₂`

English:
lemma IsStable.locally_induction₂
  statement: {r : (ι -> Ω -> E) -> Prop} [IsRightContinuous 𝓕]
  proof: hq.locally_induction (p := fun Y => r Y ∧ p Y) (and_imp.2 <| hrpq ·)
    (hr.locally_and_iff hp).2 ⟨hrX, hpX⟩

中文:
引理 IsStable.locally_induction₂
  结论: {r : (ι -> Ω -> E) -> 命题} [是RightContinuous 𝓕]
  证明: hq.locally_induction (p := fun Y => r Y ∧ p Y) (and_imp.2 <| hrpq ·)
    (hr.locally_and_iff hp).2 ⟨hrX, hpX⟩

Depends on / 依赖: and_imp, hq.locally_induction, hr.locally_and_iff, locally_and_iff, locally_induction
-/
lemma IsStable.locally_induction₂ {r : (ι -> Ω -> E) -> Prop} [IsRightContinuous 𝓕]
    (hrpq : forall Y, r Y -> p Y -> Locally q 𝓕 Y P)
    (hr : IsStable 𝓕 r) (hp : IsStable 𝓕 p) (hq : IsStable 𝓕 q)
    (hrX : Locally r 𝓕 X P) (hpX : Locally p 𝓕 X P) :
    Locally q 𝓕 X P :=
hq.locally_induction (p := fun Y => r Y ∧ p Y) (and_imp.2 <| hrpq ·)
    (hr.locally_and_iff hp).2 ⟨hrX, hpX⟩

end

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
