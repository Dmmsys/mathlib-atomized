/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Condexp

/-!
# Conditional Independence

We define conditional independence of sets/σ-algebras/functions with respect to a σ-algebra.

Two σ-algebras `m₁` and `m₂` are conditionally independent given a third σ-algebra `m'` if for all
`m₁`-measurable sets `t₁` and `m₂`-measurable sets `t₂`,
`μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`.

On standard Borel spaces, the conditional expectation with respect to `m'` defines a kernel
`ProbabilityTheory.condExpKernel`, and the definition above is equivalent to
`∀ᵐ ω ∂μ, condExpKernel μ m' ω (t₁ ∩ t₂) = condExpKernel μ m' ω t₁ * condExpKernel μ m' ω t₂`.
We use this property as the definition of conditional independence.

## Main definitions

We provide four definitions of conditional independence:
* `iCondIndepSets`: conditional independence of a family of sets of sets `pi : ι → Set (Set Ω)`.
  This is meant to be used with π-systems.
* `iCondIndep`: conditional independence of a family of measurable space structures
  `m : ι → MeasurableSpace Ω`,
* `iCondIndepSet`: conditional independence of a family of sets `s : ι → Set Ω`,
* `iCondIndepFun`: conditional independence of a family of functions. For measurable spaces
  `m : Π (i : ι), MeasurableSpace (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without the starting `i`, for example `CondIndepFun` is the version of
`iCondIndepFun` for two functions.

## Main statements

* `ProbabilityTheory.iCondIndepSets.iCondIndep`: if π-systems are conditionally independent as sets
  of sets, then the measurable space structures they generate are conditionally independent.
* `ProbabilityTheory.condIndepSets.condIndep`: variant with two π-systems.

## Notation

* `X ⟂ᵢ[Z, hZ; μ] Y` for `CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ`,
  independence of `X` and `Y` given `Z`.
* `X ⟂ᵢ[Z, hZ] Y` for the cases of `μ = volume`.

These notations are scoped in the `ProbabilityTheory` namespace.

## Implementation notes

The definitions of conditional independence in this file are a particular case of independence with
respect to a kernel and a measure, as defined in the file
`Mathlib/Probability/Independence/Kernel.lean`.
The kernel used is `ProbabilityTheory.condExpKernel`.

-/

@[expose] public section

open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

section Definitions

section

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] (hm' : m' <= mΩ)

/--
Definition of `iCondIndepSets` / `iCondIndepSets` 的定义

English:
definition iCondIndepSets
  signature: (π : ι -> Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ]
  body: Kernel.iIndepSets π (condExpKernel μ m') (μ.trim hm')

中文:
定义 iCondIndepSets
  签名: (π : ι -> 集合 (集合 Ω)) (μ : 测度 Ω := by volume_tac) [是有限测度 μ]
  定义体: Kernel.iIndepSets π (condExpKernel μ m') (μ.trim hm')

Depends on / 依赖: IsFiniteMeasure, Kernel, Kernel.iIndepSets, condExpKernel, iIndepSets, volume_tac
-/
def iCondIndepSets (π : ι -> Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] :
    Prop :=
  Kernel.iIndepSets π (condExpKernel μ m') (μ.trim hm')

/--
Definition of `CondIndepSets` / `CondIndepSets` 的定义

English:
definition CondIndepSets
  signature: (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ]
  body: Kernel.IndepSets s1 s2 (condExpKernel μ m') (μ.trim hm')

中文:
定义 CondIndepSets
  签名: (s1 s2 : 集合 (集合 Ω)) (μ : 测度 Ω := by volume_tac) [是有限测度 μ]
  定义体: Kernel.IndepSets s1 s2 (condExpKernel μ m') (μ.trim hm')

Depends on / 依赖: IndepSets, IsFiniteMeasure, Kernel, Kernel.IndepSets, condExpKernel, volume_tac
-/
def CondIndepSets (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] :
    Prop :=
  Kernel.IndepSets s1 s2 (condExpKernel μ m') (μ.trim hm')

/--
Definition of `iCondIndep` / `iCondIndep` 的定义

English:
definition iCondIndep
  signature: (m : ι -> MeasurableSpace Ω)
  body: Kernel.iIndep m (condExpKernel (mΩ := mΩ) μ m') (μ.trim hm')

中文:
定义 iCondIndep
  签名: (m : ι -> 可测空间 Ω)
  定义体: Kernel.iIndep m (condExpKernel (mΩ := mΩ) μ m') (μ.trim hm')

Depends on / 依赖: IsFiniteMeasure, Kernel, Kernel.iIndep, condExpKernel, iIndep, volume_tac
-/
def iCondIndep (m : ι -> MeasurableSpace Ω)
    (μ : @Measure Ω mΩ := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndep m (condExpKernel (mΩ := mΩ) μ m') (μ.trim hm')

end

/--
Definition of `CondIndep` / `CondIndep` 的定义

English:
definition CondIndep
  signature: (m' m₁ m₂ : MeasurableSpace Ω)
  body: Kernel.Indep m₁ m₂ (condExpKernel μ m') (μ.trim hm')

中文:
定义 CondIndep
  签名: (m' m₁ m₂ : 可测空间 Ω)
  定义体: Kernel.Indep m₁ m₂ (condExpKernel μ m') (μ.trim hm')

Depends on / 依赖: IsFiniteMeasure, Kernel, Kernel.Indep, condExpKernel, volume_tac
-/
def CondIndep (m' m₁ m₂ : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hm' : m' <= mΩ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.Indep m₁ m₂ (condExpKernel μ m') (μ.trim hm')

section

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  (hm' : m' <= mΩ)

/--
Definition of `iCondIndepSet` / `iCondIndepSet` 的定义

English:
definition iCondIndepSet
  signature: (s : ι -> Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ]
  body: Kernel.iIndepSet s (condExpKernel μ m') (μ.trim hm')

中文:
定义 iCondIndepSet
  签名: (s : ι -> 集合 Ω) (μ : 测度 Ω := by volume_tac) [是有限测度 μ]
  定义体: Kernel.iIndepSet s (condExpKernel μ m') (μ.trim hm')

Depends on / 依赖: IsFiniteMeasure, Kernel, Kernel.iIndepSet, condExpKernel, iIndepSet, volume_tac
-/
def iCondIndepSet (s : ι -> Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndepSet s (condExpKernel μ m') (μ.trim hm')

/--
Definition of `CondIndepSet` / `CondIndepSet` 的定义

English:
definition CondIndepSet
  signature: (s t : Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ]
  body: Kernel.IndepSet s t (condExpKernel μ m') (μ.trim hm')

中文:
定义 CondIndepSet
  签名: (s t : 集合 Ω) (μ : 测度 Ω := by volume_tac) [是有限测度 μ]
  定义体: Kernel.IndepSet s t (condExpKernel μ m') (μ.trim hm')

Depends on / 依赖: IndepSet, IsFiniteMeasure, Kernel, Kernel.IndepSet, condExpKernel, volume_tac
-/
def CondIndepSet (s t : Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.IndepSet s t (condExpKernel μ m') (μ.trim hm')

/--
Definition of `iCondIndepFun` / `iCondIndepFun` 的定义

English:
definition iCondIndepFun
  signature: {β : ι -> Type*} [m : forall x : ι, MeasurableSpace (β x)]
  body: Kernel.iIndepFun f (condExpKernel μ m') (μ.trim hm')

中文:
定义 iCondIndepFun
  签名: {β : ι -> 类型} [m : 对任意 x : ι, 可测空间 (β x)]
  定义体: Kernel.iIndepFun f (condExpKernel μ m') (μ.trim hm')

Depends on / 依赖: IsFiniteMeasure, Kernel, Kernel.iIndepFun, condExpKernel, iIndepFun, volume_tac
-/
def iCondIndepFun {β : ι -> Type*} [m : forall x : ι, MeasurableSpace (β x)]
    (f : forall x : ι, Ω -> β x) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.iIndepFun f (condExpKernel μ m') (μ.trim hm')

/--
Definition of `CondIndepFun` / `CondIndepFun` 的定义

English:
definition CondIndepFun
  signature: {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
  body: Kernel.IndepFun f g (condExpKernel μ m') (μ.trim hm')

中文:
定义 CondIndepFun
  签名: {β γ : 类型} [可测空间 β] [可测空间 γ]
  定义体: Kernel.IndepFun f g (condExpKernel μ m') (μ.trim hm')

Depends on / 依赖: IndepFun, IsFiniteMeasure, Kernel, Kernel.IndepFun, condExpKernel, volume_tac
-/
def CondIndepFun {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω -> β) (g : Ω -> γ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.IndepFun f g (condExpKernel μ m') (μ.trim hm')

end

end Definitions

@[inherit_doc ProbabilityTheory.CondIndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" Z ", " hZ "; " μ "] " Y:50 =>
  ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance) (Measurable.comap_le hZ)
  X Y μ

@[inherit_doc ProbabilityTheory.CondIndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" Z ", " hZ "] " Y:50 =>
  ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance) (Measurable.comap_le hZ)
  X Y volume

section DefinitionLemmas

section
variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] (hm' : m' <= mΩ)

/--
lemma `iCondIndepSets_iff` / 引理 `iCondIndepSets_iff`

English:
lemma iCondIndepSets_iff
  statement: (π : ι -> Set (Set Ω)) (hπ : forall i s (_hs : s in π i), MeasurableSet s)
  proof: by
  simp only [iCondIndepSets, Kernel.iIndepSets]
  have h_eq' : forall (s : Finset ι) (f : ι -> Set Ω) (_H : forall i, i in s -> f i in π i) i (_hi : i in s),
      (fun ω => ENNReal.toReal (condExpKernel μ m' ω (f i))) =ᵐ[μ] μ⟦f i | m'⟧ :=
    fun s f H i hi => condExpKernel_ae_eq_condExp hm' (hπ

中文:
引理 iCondIndepSets_iff
  结论: (π : ι -> 集合 (集合 Ω)) (hπ : 对任意 i s (_hs : s in π i), 可测集 s)
  证明: by
  simp only [iCondIndepSets, Kernel.iIndepSets]
  have h_eq' : forall (s : Finset ι) (f : ι -> Set Ω) (_H : forall i, i in s -> f i in π i) i (_hi : i in s),
      (fun ω => ENNReal.toReal (condExpKernel μ m' ω (f i))) =ᵐ[μ] μ⟦f i | m'⟧ :=
    fun s f H i hi => condExpKernel_ae_eq_condExp hm' (hπ

Depends on / 依赖: ENNReal, ENNReal.toReal, Finset, Kernel, Kernel.iIndepSets, condExpKernel, condExpKernel_ae_eq_condExp, h_eq, iCondIndepSets, iIndepSets, toReal
-/
lemma iCondIndepSets_iff (π : ι -> Set (Set Ω)) (hπ : forall i s (_hs : s in π i), MeasurableSet s)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSets m' hm' π μ ↔ forall (s : Finset ι) {f : ι -> Set Ω} (_H : forall i, i in s -> f i in π i),
      μ⟦⋂ i in s, f i | m'⟧ =ᵐ[μ] ∏ i in s, (μ⟦f i | m'⟧) := by
  simp only [iCondIndepSets, Kernel.iIndepSets]
  have h_eq' : forall (s : Finset ι) (f : ι -> Set Ω) (_H : forall i, i in s -> f i in π i) i (_hi : i in s),
      (fun ω => ENNReal.toReal (condExpKernel μ m' ω (f i))) =ᵐ[μ] μ⟦f i | m'⟧ :=
    fun s f H i hi => condExpKernel_ae_eq_condExp hm' (hπ i (f i) (H i hi))
  have h_eq : forall (s : Finset ι) (f : ι -> Set Ω) (_H : forall i, i in s -> f i in π i), forallᵐ ω ∂μ,
      forall i in s, ENNReal.toReal (condExpKernel μ m' ω (f i)) = (μ⟦f i | m'⟧) ω := by
    intro s f H
    simp_rw [← Finset.mem_coe]
    rw [ae_ball_iff (Finset.countable_toSet s)]
    exact h_eq' s f H
  have h_inter_eq : forall (s : Finset ι) (f : ι -> Set Ω) (_H : forall i, i in s -> f i in π i),
      (fun ω => ENNReal.toReal (condExpKernel μ m' ω (⋂ i in s, f i)))
        =ᵐ[μ] μ⟦⋂ i in s, f i | m'⟧ := by
    refine fun s f H => condExpKernel_ae_eq_condExp hm' ?_
    exact MeasurableSet.biInter (Finset.countable_toSet _) (fun i hi => hπ i _ (H i hi))
  refine ⟨fun h s f hf => ?_, fun h s f hf => ?_⟩ <;> specialize h s hf
  · have h' := ae_eq_of_ae_eq_trim h
    filter_upwards [h_eq s f hf, h_inter_eq s f hf, h'] with ω h_eq h_inter_eq h'
    rw [← h_inter_eq]; rw [h']; rw [ENNReal.toReal_prod]; rw [Finset.prod_apply]
    exact Finset.prod_congr rfl h_eq
  · refine ((stronglyMeasurable_condExpKernel ?_).ae_eq_trim_iff hm' ?_).mpr ?_
    · exact .biInter (Finset.countable_toSet _) (fun i hi => hπ i _ (hf i hi))
    · refine Measurable.stronglyMeasurable ?_
      exact Finset.measurable_fun_prod s (fun i hi => measurable_condExpKernel (hπ i _ (hf i hi)))
    filter_upwards [h_eq s f hf, h_inter_eq s f hf, h] with ω h_eq h_inter_eq h
    have h_ne_top : condExpKernel μ m' ω (⋂ i in s, f i) != ∞ :=
      (measure_ne_top (condExpKernel μ m' ω) _)
    have : (∏ i in s, condExpKernel μ m' ω (f i)) != ∞ :=
      ENNReal.prod_ne_top fun _ _ => measure_ne_top (condExpKernel μ m' ω) _
    rw [← ENNReal.ofReal_toReal h_ne_top]; rw [h_inter_eq]; rw [h]; rw [Finset.prod_apply]; rw [← ENNReal.ofReal_toReal this]; rw [ENNReal.toReal_prod]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => (h_eq i hi).symm)

/--
lemma `condIndepSets_iff` / 引理 `condIndepSets_iff`

English:
lemma condIndepSets_iff
  statement: (s1 s2 : Set (Set Ω)) (hs1 : forall s in s1, MeasurableSet s)
  proof: by
  simp only [CondIndepSets, Kernel.IndepSets]
  have hs1_eq : forall s in s1, (fun ω => ENNReal.toReal (condExpKernel μ m' ω s)) =ᵐ[μ] μ⟦s | m'⟧ :=
    fun s hs => condExpKernel_ae_eq_condExp hm' (hs1 s hs)
  have hs2_eq : forall s in s2, (fun ω => ENNReal.toReal (condExpKernel μ m' ω s)) =ᵐ[μ] μ

中文:
引理 condIndepSets_iff
  结论: (s1 s2 : 集合 (集合 Ω)) (hs1 : 对任意 s in s1, 可测集 s)
  证明: by
  simp only [CondIndepSets, Kernel.IndepSets]
  have hs1_eq : forall s in s1, (fun ω => ENNReal.toReal (condExpKernel μ m' ω s)) =ᵐ[μ] μ⟦s | m'⟧ :=
    fun s hs => condExpKernel_ae_eq_condExp hm' (hs1 s hs)
  have hs2_eq : forall s in s2, (fun ω => ENNReal.toReal (condExpKernel μ m' ω s)) =ᵐ[μ] μ

Depends on / 依赖: CondIndepSets, ENNReal, ENNReal.toReal, IndepSets, Kernel, Kernel.IndepSets, condExpKernel, condExpKernel_ae_eq_condExp, hs12_eq, hs1_eq, hs2_eq, toReal
-/
lemma condIndepSets_iff (s1 s2 : Set (Set Ω)) (hs1 : forall s in s1, MeasurableSet s)
    (hs2 : forall s in s2, MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSets m' hm' s1 s2 μ ↔ forall (t1 t2 : Set Ω) (_ : t1 in s1) (_ : t2 in s2),
      (μ⟦t1 inter t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧) := by
  simp only [CondIndepSets, Kernel.IndepSets]
  have hs1_eq : forall s in s1, (fun ω => ENNReal.toReal (condExpKernel μ m' ω s)) =ᵐ[μ] μ⟦s | m'⟧ :=
    fun s hs => condExpKernel_ae_eq_condExp hm' (hs1 s hs)
  have hs2_eq : forall s in s2, (fun ω => ENNReal.toReal (condExpKernel μ m' ω s)) =ᵐ[μ] μ⟦s | m'⟧ :=
    fun s hs => condExpKernel_ae_eq_condExp hm' (hs2 s hs)
  have hs12_eq : forall s in s1, forall t in s2, (fun ω => ENNReal.toReal (condExpKernel μ m' ω (s inter t)))
      =ᵐ[μ] μ⟦s inter t | m'⟧ :=
    fun s hs t ht => condExpKernel_ae_eq_condExp hm' ((hs1 s hs).inter ((hs2 t ht)))
  refine ⟨fun h s t hs ht => ?_, fun h s t hs ht => ?_⟩ <;> specialize h s t hs ht
  · have h' := ae_eq_of_ae_eq_trim h
    filter_upwards [hs1_eq s hs, hs2_eq t ht, hs12_eq s hs t ht, h'] with ω hs_eq ht_eq hst_eq h'
    rw [← hst_eq]; rw [Pi.mul_apply]; rw [← hs_eq]; rw [← ht_eq]; rw [h']; rw [ENNReal.toReal_mul]
  · refine ((stronglyMeasurable_condExpKernel ((hs1 s hs).inter (hs2 t ht))).ae_eq_trim_iff hm'
      ((measurable_condExpKernel (hs1 s hs)).fun_mul
        (measurable_condExpKernel (hs2 t ht))).stronglyMeasurable).mpr ?_
    filter_upwards [hs1_eq s hs, hs2_eq t ht, hs12_eq s hs t ht, h] with ω hs_eq ht_eq hst_eq h
    have h_ne_top : condExpKernel μ m' ω (s inter t) != ∞ := measure_ne_top (condExpKernel μ m' ω) _
    rw [← ENNReal.ofReal_toReal h_ne_top]; rw [hst_eq]; rw [h]; rw [Pi.mul_apply]; rw [← hs_eq]; rw [← ht_eq]; rw [← ENNReal.toReal_mul]; rw [ENNReal.ofReal_toReal]
    exact ENNReal.mul_ne_top (measure_ne_top (condExpKernel μ m' ω) s)
      (measure_ne_top (condExpKernel μ m' ω) t)

/--
lemma `iCondIndepSets_singleton_iff` / 引理 `iCondIndepSets_singleton_iff`

English:
lemma iCondIndepSets_singleton_iff
  statement: (s : ι -> Set Ω) (hπ : forall i, MeasurableSet (s i))
  proof: by
  rw [iCondIndepSets_iff]
  · simp_all only [Set.mem_singleton_iff]
    constructor
    · intros
      simp [*]
    · grind
  · simpa

中文:
引理 iCondIndepSets_singleton_iff
  结论: (s : ι -> 集合 Ω) (hπ : 对任意 i, 可测集 (s i))
  证明: by
  rw [iCondIndepSets_iff]
  · simp_all only [Set.mem_singleton_iff]
    constructor
    · intros
      simp [*]
    · grind
  · simpa

Depends on / 依赖: Set.mem_singleton_iff, iCondIndepSets_iff, intros, mem_singleton_iff
-/
lemma iCondIndepSets_singleton_iff (s : ι -> Set Ω) (hπ : forall i, MeasurableSet (s i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSets m' hm' (fun i => {s i}) μ ↔ forall S : Finset ι,
      μ⟦⋂ i in S, s i | m'⟧ =ᵐ[μ] ∏ i in S, (μ⟦s i | m'⟧) := by
  rw [iCondIndepSets_iff]
  · simp_all only [Set.mem_singleton_iff]
    constructor
    · intros
      simp [*]
    · grind
  · simpa

/--
theorem `condIndepSets_singleton_iff` / 定理 `condIndepSets_singleton_iff`

English:
theorem condIndepSets_singleton_iff
  statement: {μ : Measure Ω} [IsFiniteMeasure μ]
  proof: by
  rw [condIndepSets_iff _ _ _ _ ?_ ?_]
  · simp
  · intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rwa [hs']
  · intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rwa [hs']

中文:
定理 condIndepSets_singleton_iff
  结论: {μ : 测度 Ω} [是有限测度 μ]
  证明: by
  rw [condIndepSets_iff _ _ _ _ ?_ ?_]
  · simp
  · intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rwa [hs']
  · intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rwa [hs']

Depends on / 依赖: Set.mem_singleton_iff, condIndepSets_iff, mem_singleton_iff
-/
theorem condIndepSets_singleton_iff {μ : Measure Ω} [IsFiniteMeasure μ]
    {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    CondIndepSets m' hm' {s} {t} μ ↔ (μ⟦s inter t | m'⟧) =ᵐ[μ] (μ⟦s | m'⟧) * (μ⟦t | m'⟧) := by
  rw [condIndepSets_iff _ _ _ _ ?_ ?_]
  · simp
  · intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rwa [hs']
  · intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rwa [hs']

/--
lemma `iCondIndep_iff_iCondIndepSets` / 引理 `iCondIndep_iff_iCondIndepSets`

English:
lemma iCondIndep_iff_iCondIndepSets
  statement: (m : ι -> MeasurableSpace Ω)
  proof: by
  simp only [iCondIndep, iCondIndepSets, Kernel.iIndep]

中文:
引理 iCondIndep_iff_iCondIndepSets
  结论: (m : ι -> 可测空间 Ω)
  证明: by
  simp only [iCondIndep, iCondIndepSets, Kernel.iIndep]

Depends on / 依赖: Kernel, Kernel.iIndep, iCondIndep, iCondIndepSets, iIndep
-/
lemma iCondIndep_iff_iCondIndepSets (m : ι -> MeasurableSpace Ω)
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] :
    iCondIndep m' hm' m μ ↔ iCondIndepSets m' hm' (fun x => {s | MeasurableSet[m x] s}) μ := by
  simp only [iCondIndep, iCondIndepSets, Kernel.iIndep]

/--
lemma `iCondIndep_iff` / 引理 `iCondIndep_iff`

English:
lemma iCondIndep_iff
  statement: (m : ι -> MeasurableSpace Ω) (hm : forall i, m i <= mΩ)
  proof: by
  rw [iCondIndep_iff_iCondIndepSets]; rw [iCondIndepSets_iff]
  · rfl
  · exact hm

中文:
引理 iCondIndep_iff
  结论: (m : ι -> 可测空间 Ω) (hm : 对任意 i, m i <= mΩ)
  证明: by
  rw [iCondIndep_iff_iCondIndepSets]; rw [iCondIndepSets_iff]
  · rfl
  · exact hm

Depends on / 依赖: iCondIndepSets_iff, iCondIndep_iff_iCondIndepSets
-/
lemma iCondIndep_iff (m : ι -> MeasurableSpace Ω) (hm : forall i, m i <= mΩ)
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] :
    iCondIndep m' hm' m μ
      ↔ forall (s : Finset ι) {f : ι -> Set Ω} (_H : forall i, i in s -> MeasurableSet[m i] (f i)),
      μ⟦⋂ i in s, f i | m'⟧ =ᵐ[μ] ∏ i in s, (μ⟦f i | m'⟧) := by
  rw [iCondIndep_iff_iCondIndepSets]; rw [iCondIndepSets_iff]
  · rfl
  · exact hm

end

section CondIndep

/--
lemma `condIndep_iff_condIndepSets` / 引理 `condIndep_iff_condIndepSets`

English:
lemma condIndep_iff_condIndepSets
  statement: (m' m₁ m₂ : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
  proof: by
  simp only [CondIndep, CondIndepSets, Kernel.Indep]

中文:
引理 condIndep_iff_condIndepSets
  结论: (m' m₁ m₂ : 可测空间 Ω) {mΩ : 可测空间 Ω}
  证明: by
  simp only [CondIndep, CondIndepSets, Kernel.Indep]

Depends on / 依赖: CondIndep, CondIndepSets, Kernel, Kernel.Indep
-/
lemma condIndep_iff_condIndepSets (m' m₁ m₂ : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hm' : m' <= mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ
      ↔ CondIndepSets m' hm' {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s} μ := by
  simp only [CondIndep, CondIndepSets, Kernel.Indep]

/--
lemma `condIndep_iff` / 引理 `condIndep_iff`

English:
lemma condIndep_iff
  statement: (m' m₁ m₂ : MeasurableSpace Ω)
  proof: by
  rw [condIndep_iff_condIndepSets]; rw [condIndepSets_iff]
  · rfl
  · exact hm₁
  · exact hm₂

中文:
引理 condIndep_iff
  结论: (m' m₁ m₂ : 可测空间 Ω)
  证明: by
  rw [condIndep_iff_condIndepSets]; rw [condIndepSets_iff]
  · rfl
  · exact hm₁
  · exact hm₂

Depends on / 依赖: condIndepSets_iff, condIndep_iff_condIndepSets
-/
lemma condIndep_iff (m' m₁ m₂ : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hm' : m' <= mΩ) (hm₁ : m₁ <= mΩ) (hm₂ : m₂ <= mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ
      ↔ forall t1 t2, MeasurableSet[m₁] t1 -> MeasurableSet[m₂] t2
        -> (μ⟦t1 inter t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧) := by
  rw [condIndep_iff_condIndepSets]; rw [condIndepSets_iff]
  · rfl
  · exact hm₁
  · exact hm₂

end CondIndep

variable (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  (hm' : m' <= mΩ)

/--
lemma `iCondIndepSet_iff_iCondIndep` / 引理 `iCondIndepSet_iff_iCondIndep`

English:
lemma iCondIndepSet_iff_iCondIndep
  given: (s : ι -> Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
  proof: by
  simp only [iCondIndepSet, iCondIndep, Kernel.iIndepSet]

中文:
引理 iCondIndepSet_iff_iCondIndep
  条件: (s : ι -> 集合 Ω) (μ : 测度 Ω) [是有限测度 μ]
  证明: by
  simp only [iCondIndepSet, iCondIndep, Kernel.iIndepSet]

Depends on / 依赖: Kernel, Kernel.iIndepSet, iCondIndep, iCondIndepSet, iIndepSet
-/
lemma iCondIndepSet_iff_iCondIndep (s : ι -> Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔ iCondIndep m' hm' (fun i => generateFrom {s i}) μ := by
  simp only [iCondIndepSet, iCondIndep, Kernel.iIndepSet]

/--
theorem `iCondIndepSet_iff_iCondIndepSets_singleton` / 定理 `iCondIndepSet_iff_iCondIndepSets_singleton`

English:
theorem iCondIndepSet_iff_iCondIndepSets_singleton
  statement: (s : ι -> Set Ω) (hs : forall i, MeasurableSet (s i))
  proof: Kernel.iIndepSet_iff_iIndepSets_singleton hs

中文:
定理 iCondIndepSet_iff_iCondIndepSets_singleton
  结论: (s : ι -> 集合 Ω) (hs : 对任意 i, 可测集 (s i))
  证明: Kernel.iIndepSet_iff_iIndepSets_singleton hs

Depends on / 依赖: Kernel, Kernel.iIndepSet_iff_iIndepSets_singleton, iIndepSet_iff_iIndepSets_singleton
-/
theorem iCondIndepSet_iff_iCondIndepSets_singleton (s : ι -> Set Ω) (hs : forall i, MeasurableSet (s i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔ iCondIndepSets m' hm' (fun i => {s i}) μ :=
  Kernel.iIndepSet_iff_iIndepSets_singleton hs

/--
lemma `iCondIndepSet_iff` / 引理 `iCondIndepSet_iff`

English:
lemma iCondIndepSet_iff
  statement: (s : ι -> Set Ω) (hs : forall i, MeasurableSet (s i))
  proof: by
  rw [iCondIndepSet_iff_iCondIndepSets_singleton _ _ _ hs]; rw [iCondIndepSets_singleton_iff _ _ _ hs]

中文:
引理 iCondIndepSet_iff
  结论: (s : ι -> 集合 Ω) (hs : 对任意 i, 可测集 (s i))
  证明: by
  rw [iCondIndepSet_iff_iCondIndepSets_singleton _ _ _ hs]; rw [iCondIndepSets_singleton_iff _ _ _ hs]

Depends on / 依赖: iCondIndepSet_iff_iCondIndepSets_singleton, iCondIndepSets_singleton_iff
-/
lemma iCondIndepSet_iff (s : ι -> Set Ω) (hs : forall i, MeasurableSet (s i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔
      forall S : Finset ι, μ⟦⋂ i in S, s i | m'⟧ =ᵐ[μ] ∏ i in S, μ⟦s i | m'⟧ := by
  rw [iCondIndepSet_iff_iCondIndepSets_singleton _ _ _ hs]; rw [iCondIndepSets_singleton_iff _ _ _ hs]

/--
lemma `condIndepSet_iff_condIndep` / 引理 `condIndepSet_iff_condIndep`

English:
lemma condIndepSet_iff_condIndep
  given: (s t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
  proof: by
  simp only [CondIndepSet, CondIndep, Kernel.IndepSet]

中文:
引理 condIndepSet_iff_condIndep
  条件: (s t : 集合 Ω) (μ : 测度 Ω) [是有限测度 μ]
  证明: by
  simp only [CondIndepSet, CondIndep, Kernel.IndepSet]

Depends on / 依赖: CondIndep, CondIndepSet, IndepSet, Kernel, Kernel.IndepSet
-/
lemma condIndepSet_iff_condIndep (s t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ CondIndep m' (generateFrom {s}) (generateFrom {t}) hm' μ := by
  simp only [CondIndepSet, CondIndep, Kernel.IndepSet]

/--
theorem `condIndepSet_iff_condIndepSets_singleton` / 定理 `condIndepSet_iff_condIndepSets_singleton`

English:
theorem condIndepSet_iff_condIndepSets_singleton
  statement: {s t : Set Ω} (hs_meas : MeasurableSet s)
  proof: Kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _

中文:
定理 condIndepSet_iff_condIndepSets_singleton
  结论: {s t : 集合 Ω} (hs_meas : 可测集 s)
  证明: Kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _

Depends on / 依赖: Kernel, Kernel.indepSet_iff_indepSets_singleton, hs_meas, ht_meas, indepSet_iff_indepSets_singleton
-/
theorem condIndepSet_iff_condIndepSets_singleton {s t : Set Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ CondIndepSets m' hm' {s} {t} μ :=
  Kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _

/--
lemma `condIndepSet_iff` / 引理 `condIndepSet_iff`

English:
lemma condIndepSet_iff
  statement: (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  rw [condIndepSet_iff_condIndepSets_singleton _ _ hs ht μ]; rw [condIndepSets_singleton_iff _ _ hs ht]

中文:
引理 condIndepSet_iff
  结论: (s t : 集合 Ω) (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  rw [condIndepSet_iff_condIndepSets_singleton _ _ hs ht μ]; rw [condIndepSets_singleton_iff _ _ hs ht]

Depends on / 依赖: condIndepSet_iff_condIndepSets_singleton, condIndepSets_singleton_iff
-/
lemma condIndepSet_iff (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ (μ⟦s inter t | m'⟧) =ᵐ[μ] (μ⟦s | m'⟧) * (μ⟦t | m'⟧) := by
  rw [condIndepSet_iff_condIndepSets_singleton _ _ hs ht μ]; rw [condIndepSets_singleton_iff _ _ hs ht]

/--
lemma `iCondIndepFun_iff_iCondIndep` / 引理 `iCondIndepFun_iff_iCondIndep`

English:
lemma iCondIndepFun_iff_iCondIndep
  statement: {β : ι -> Type*}
  proof: by
  simp only [iCondIndepFun, iCondIndep, Kernel.iIndepFun]

中文:
引理 iCondIndepFun_iff_iCondIndep
  结论: {β : ι -> 类型}
  证明: by
  simp only [iCondIndepFun, iCondIndep, Kernel.iIndepFun]

Depends on / 依赖: Kernel, Kernel.iIndepFun, iCondIndep, iCondIndepFun, iIndepFun
-/
lemma iCondIndepFun_iff_iCondIndep {β : ι -> Type*}
    (m : forall x : ι, MeasurableSpace (β x)) (f : forall x : ι, Ω -> β x)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepFun m' hm' f μ
      ↔ iCondIndep m' hm' (fun x => MeasurableSpace.comap (f x) (m x)) μ := by
  simp only [iCondIndepFun, iCondIndep, Kernel.iIndepFun]

/--
lemma `iCondIndepFun_iff` / 引理 `iCondIndepFun_iff`

English:
lemma iCondIndepFun_iff
  statement: {β : ι -> Type*}
  proof: by
  simp only [iCondIndepFun_iff_iCondIndep]
  rw [iCondIndep_iff]
  exact fun i => (hf i).comap_le

中文:
引理 iCondIndepFun_iff
  结论: {β : ι -> 类型}
  证明: by
  simp only [iCondIndepFun_iff_iCondIndep]
  rw [iCondIndep_iff]
  exact fun i => (hf i).comap_le

Depends on / 依赖: comap_le, iCondIndepFun_iff_iCondIndep, iCondIndep_iff
-/
lemma iCondIndepFun_iff {β : ι -> Type*}
    (m : forall x : ι, MeasurableSpace (β x)) (f : forall x : ι, Ω -> β x) (hf : forall i, Measurable (f i))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepFun m' hm' f μ
      ↔ forall (s : Finset ι) {g : ι -> Set Ω} (_H : forall i, i in s -> MeasurableSet[(m i).comap (f i)] (g i)),
      μ⟦⋂ i in s, g i | m'⟧ =ᵐ[μ] ∏ i in s, (μ⟦g i | m'⟧) := by
  simp only [iCondIndepFun_iff_iCondIndep]
  rw [iCondIndep_iff]
  exact fun i => (hf i).comap_le

/--
lemma `condIndepFun_iff_condIndep` / 引理 `condIndepFun_iff_condIndep`

English:
lemma condIndepFun_iff_condIndep
  statement: {β γ : Type*} [mβ : MeasurableSpace β]
  proof: by
  simp only [CondIndepFun, CondIndep, Kernel.IndepFun]

中文:
引理 condIndepFun_iff_condIndep
  结论: {β γ : 类型} [mβ : 可测空间 β]
  证明: by
  simp only [CondIndepFun, CondIndep, Kernel.IndepFun]

Depends on / 依赖: CondIndep, CondIndepFun, IndepFun, Kernel, Kernel.IndepFun
-/
lemma condIndepFun_iff_condIndep {β γ : Type*} [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (f : Ω -> β) (g : Ω -> γ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepFun m' hm' f g μ
      ↔ CondIndep m' (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) hm' μ := by
  simp only [CondIndepFun, CondIndep, Kernel.IndepFun]

/--
lemma `condIndepFun_iff` / 引理 `condIndepFun_iff`

English:
lemma condIndepFun_iff
  statement: {β γ : Type*} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
  proof: by
  rw [condIndepFun_iff_condIndep]; rw [condIndep_iff _ _ _ _ hf.comap_le hg.comap_le]

中文:
引理 condIndepFun_iff
  结论: {β γ : 类型} [mβ : 可测空间 β] [mγ : 可测空间 γ]
  证明: by
  rw [condIndepFun_iff_condIndep]; rw [condIndep_iff _ _ _ _ hf.comap_le hg.comap_le]

Depends on / 依赖: comap_le, condIndepFun_iff_condIndep, condIndep_iff, hf.comap_le, hg.comap_le
-/
lemma condIndepFun_iff {β γ : Type*} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω -> β) (g : Ω -> γ) (hf : Measurable f) (hg : Measurable g)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepFun m' hm' f g μ ↔ forall t1 t2, MeasurableSet[MeasurableSpace.comap f mβ] t1
      -> MeasurableSet[MeasurableSpace.comap g mγ] t2
        -> (μ⟦t1 inter t2 | m'⟧) =ᵐ[μ] (μ⟦t1 | m'⟧) * (μ⟦t2 | m'⟧) := by
  rw [condIndepFun_iff_condIndep]; rw [condIndep_iff _ _ _ _ hf.comap_le hg.comap_le]

end DefinitionLemmas

section CondIndepSets

variable {m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

@[symm]
/--
theorem `CondIndepSets.symm` / 定理 `CondIndepSets.symm`

English:
theorem CondIndepSets.symm
  statement: {s₁ s₂ : Set (Set Ω)}
  proof: Kernel.IndepSets.symm h

中文:
定理 CondIndepSets.symm
  结论: {s₁ s₂ : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.symm h

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.symm
-/
theorem CondIndepSets.symm {s₁ s₂ : Set (Set Ω)}
    (h : CondIndepSets m' hm' s₁ s₂ μ) : CondIndepSets m' hm' s₂ s₁ μ :=
  Kernel.IndepSets.symm h

/--
theorem `condIndepSets_of_condIndepSets_of_le_left` / 定理 `condIndepSets_of_condIndepSets_of_le_left`

English:
theorem condIndepSets_of_condIndepSets_of_le_left
  statement: {s₁ s₂ s₃ : Set (Set Ω)}
  proof: Kernel.indepSets_of_indepSets_of_le_left h_indep h31

中文:
定理 condIndepSets_of_condIndepSets_of_le_left
  结论: {s₁ s₂ s₃ : 集合 (集合 Ω)}
  证明: Kernel.indepSets_of_indepSets_of_le_left h_indep h31

Depends on / 依赖: Kernel, Kernel.indepSets_of_indepSets_of_le_left, h_indep, indepSets_of_indepSets_of_le_left
-/
theorem condIndepSets_of_condIndepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : CondIndepSets m' hm' s₁ s₂ μ) (h31 : s₃ subseteq s₁) :
    CondIndepSets m' hm' s₃ s₂ μ :=
  Kernel.indepSets_of_indepSets_of_le_left h_indep h31

/--
theorem `condIndepSets_of_condIndepSets_of_le_right` / 定理 `condIndepSets_of_condIndepSets_of_le_right`

English:
theorem condIndepSets_of_condIndepSets_of_le_right
  statement: {s₁ s₂ s₃ : Set (Set Ω)}
  proof: Kernel.indepSets_of_indepSets_of_le_right h_indep h32

中文:
定理 condIndepSets_of_condIndepSets_of_le_right
  结论: {s₁ s₂ s₃ : 集合 (集合 Ω)}
  证明: Kernel.indepSets_of_indepSets_of_le_right h_indep h32

Depends on / 依赖: Kernel, Kernel.indepSets_of_indepSets_of_le_right, h_indep, indepSets_of_indepSets_of_le_right
-/
theorem condIndepSets_of_condIndepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : CondIndepSets m' hm' s₁ s₂ μ) (h32 : s₃ subseteq s₂) :
    CondIndepSets m' hm' s₁ s₃ μ :=
  Kernel.indepSets_of_indepSets_of_le_right h_indep h32

/--
theorem `CondIndepSets.union` / 定理 `CondIndepSets.union`

English:
theorem CondIndepSets.union
  statement: {s₁ s₂ s' : Set (Set Ω)}
  proof: Kernel.IndepSets.union h₁ h₂

@[simp]

中文:
定理 CondIndepSets.union
  结论: {s₁ s₂ s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.union h₁ h₂

@[simp]

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.union
-/
theorem CondIndepSets.union {s₁ s₂ s' : Set (Set Ω)}
    (h₁ : CondIndepSets m' hm' s₁ s' μ) (h₂ : CondIndepSets m' hm' s₂ s' μ) :
    CondIndepSets m' hm' (s₁ union s₂) s' μ :=
  Kernel.IndepSets.union h₁ h₂

@[simp]
/--
theorem `CondIndepSets.union_iff` / 定理 `CondIndepSets.union_iff`

English:
theorem CondIndepSets.union_iff
  given: {s₁ s₂ s' : Set (Set Ω)}
  proof: Kernel.IndepSets.union_iff

中文:
定理 CondIndepSets.union_iff
  条件: {s₁ s₂ s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.union_iff

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.union_iff, union_iff
-/
theorem CondIndepSets.union_iff {s₁ s₂ s' : Set (Set Ω)} :
    CondIndepSets m' hm' (s₁ union s₂) s' μ
      ↔ CondIndepSets m' hm' s₁ s' μ ∧ CondIndepSets m' hm' s₂ s' μ :=
  Kernel.IndepSets.union_iff

/--
theorem `CondIndepSets.iUnion` / 定理 `CondIndepSets.iUnion`

English:
theorem CondIndepSets.iUnion
  statement: {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
  proof: Kernel.IndepSets.iUnion hyp

中文:
定理 CondIndepSets.iUnion
  结论: {s : ι -> 集合 (集合 Ω)} {s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.iUnion hyp

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.iUnion, iUnion
-/
theorem CondIndepSets.iUnion {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
    (hyp : forall n, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋃ n, s n) s' μ :=
  Kernel.IndepSets.iUnion hyp

/--
theorem `CondIndepSets.biUnion` / 定理 `CondIndepSets.biUnion`

English:
theorem CondIndepSets.biUnion
  statement: {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
  proof: Kernel.IndepSets.biUnion hyp

中文:
定理 CondIndepSets.biUnion
  结论: {s : ι -> 集合 (集合 Ω)} {s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.biUnion hyp

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.biUnion, biUnion
-/
theorem CondIndepSets.biUnion {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (hyp : forall n in u, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋃ n in u, s n) s' μ :=
  Kernel.IndepSets.biUnion hyp

/--
theorem `CondIndepSets.inter` / 定理 `CondIndepSets.inter`

English:
theorem CondIndepSets.inter
  statement: {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω))
  proof: Kernel.IndepSets.inter s₂ h₁

中文:
定理 CondIndepSets.inter
  结论: {s₁ s' : 集合 (集合 Ω)} (s₂ : 集合 (集合 Ω))
  证明: Kernel.IndepSets.inter s₂ h₁

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.inter
-/
theorem CondIndepSets.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω))
    (h₁ : CondIndepSets m' hm' s₁ s' μ) :
    CondIndepSets m' hm' (s₁ inter s₂) s' μ :=
  Kernel.IndepSets.inter s₂ h₁

/--
theorem `CondIndepSets.iInter` / 定理 `CondIndepSets.iInter`

English:
theorem CondIndepSets.iInter
  statement: {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
  proof: Kernel.IndepSets.iInter h

中文:
定理 CondIndepSets.i整数er
  结论: {s : ι -> 集合 (集合 Ω)} {s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.iInter h

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.iInter, WfDvdMonoid, iInter, wfDvdMonoid
-/
theorem CondIndepSets.iInter {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
    (h : exists n, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋂ n, s n) s' μ :=
  Kernel.IndepSets.iInter h

/--
theorem `CondIndepSets.bInter` / 定理 `CondIndepSets.bInter`

English:
theorem CondIndepSets.bInter
  statement: {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
  proof: Kernel.IndepSets.bInter h

中文:
定理 CondIndepSets.b整数er
  结论: {s : ι -> 集合 (集合 Ω)} {s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.bInter h

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.bInter, bInter
-/
theorem CondIndepSets.bInter {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (h : exists n in u, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋂ n in u, s n) s' μ :=
  Kernel.IndepSets.bInter h

end CondIndepSets

section CondIndepSet

variable {m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

/--
theorem `condIndepSet_empty_right` / 定理 `condIndepSet_empty_right`

English:
theorem condIndepSet_empty_right
  given: (s : Set Ω)
  statement: CondIndepSet m' hm' s ∅ μ
  proof: Kernel.indepSet_empty_right s

中文:
定理 condIndepSet_empty_right
  条件: (s : 集合 Ω)
  结论: CondIndepSet m' hm' s ∅ μ
  证明: Kernel.indepSet_empty_right s

Depends on / 依赖: Kernel, Kernel.indepSet_empty_right, indepSet_empty_right
-/
theorem condIndepSet_empty_right (s : Set Ω) : CondIndepSet m' hm' s ∅ μ :=
  Kernel.indepSet_empty_right s

/--
theorem `condIndepSet_empty_left` / 定理 `condIndepSet_empty_left`

English:
theorem condIndepSet_empty_left
  given: (s : Set Ω)
  statement: CondIndepSet m' hm' ∅ s μ
  proof: Kernel.indepSet_empty_left s

中文:
定理 condIndepSet_empty_left
  条件: (s : 集合 Ω)
  结论: CondIndepSet m' hm' ∅ s μ
  证明: Kernel.indepSet_empty_left s

Depends on / 依赖: Kernel, Kernel.indepSet_empty_left, indepSet_empty_left
-/
theorem condIndepSet_empty_left (s : Set Ω) : CondIndepSet m' hm' ∅ s μ :=
  Kernel.indepSet_empty_left s

end CondIndepSet

section CondIndep

@[symm]
/--
theorem `CondIndep.symm` / 定理 `CondIndep.symm`

English:
theorem CondIndep.symm
  statement: {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  proof: CondIndepSets.symm h

中文:
定理 CondIndep.symm
  结论: {m' m₁ m₂ : 可测空间 Ω} {mΩ : 可测空间 Ω}
  证明: CondIndepSets.symm h

Depends on / 依赖: Classical, Classical.arbitrary, CondIndepSets, CondIndepSets.symm, NormalizedGCDMonoid, UniqueFactorizationMonoid, arbitrary, ufm_of_decomposition_of_wfDvdMonoid, uniqueFactorizationMonoid
-/
theorem CondIndep.symm {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (h : CondIndep m' m₁ m₂ hm' μ) :
    CondIndep m' m₂ m₁ hm' μ :=
  CondIndepSets.symm h

/--
theorem `condIndep_bot_right` / 定理 `condIndep_bot_right`

English:
theorem condIndep_bot_right
  statement: (m₁ : MeasurableSpace Ω) {m' : MeasurableSpace Ω}
  proof: Kernel.indep_bot_right m₁

中文:
定理 condIndep_bot_right
  结论: (m₁ : 可测空间 Ω) {m' : 可测空间 Ω}
  证明: Kernel.indep_bot_right m₁

Depends on / 依赖: Kernel, Kernel.indep_bot_right, indep_bot_right
-/
theorem condIndep_bot_right (m₁ : MeasurableSpace Ω) {m' : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ] :
    CondIndep m' m₁ ⊥ hm' μ :=
  Kernel.indep_bot_right m₁

/--
theorem `condIndep_bot_left` / 定理 `condIndep_bot_left`

English:
theorem condIndep_bot_left
  statement: (m₁ : MeasurableSpace Ω) {m' : MeasurableSpace Ω}
  proof: (Kernel.indep_bot_right m₁).symm

中文:
定理 condIndep_bot_left
  结论: (m₁ : 可测空间 Ω) {m' : 可测空间 Ω}
  证明: (Kernel.indep_bot_right m₁).symm

Depends on / 依赖: Kernel, Kernel.indep_bot_right, indep_bot_right, uniqueFactorizationMonoid
-/
theorem condIndep_bot_left (m₁ : MeasurableSpace Ω) {m' : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ] :
    CondIndep m' ⊥ m₁ hm' μ :=
  (Kernel.indep_bot_right m₁).symm

/--
theorem `condIndep_of_condIndep_of_le_left` / 定理 `condIndep_of_condIndep_of_le_left`

English:
theorem condIndep_of_condIndep_of_le_left
  statement: {m' m₁ m₂ m₃ : MeasurableSpace Ω}
  proof: Kernel.indep_of_indep_of_le_left h_indep h31

中文:
定理 condIndep_of_condIndep_of_le_left
  结论: {m' m₁ m₂ m₃ : 可测空间 Ω}
  证明: Kernel.indep_of_indep_of_le_left h_indep h31

Depends on / 依赖: Kernel, Kernel.indep_of_indep_of_le_left, h_indep, indep_of_indep_of_le_left
-/
theorem condIndep_of_condIndep_of_le_left {m' m₁ m₂ m₃ : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (h_indep : CondIndep m' m₁ m₂ hm' μ) (h31 : m₃ <= m₁) :
    CondIndep m' m₃ m₂ hm' μ :=
  Kernel.indep_of_indep_of_le_left h_indep h31

/--
theorem `condIndep_of_condIndep_of_le_right` / 定理 `condIndep_of_condIndep_of_le_right`

English:
theorem condIndep_of_condIndep_of_le_right
  statement: {m' m₁ m₂ m₃ : MeasurableSpace Ω}
  proof: Kernel.indep_of_indep_of_le_right h_indep h32

中文:
定理 condIndep_of_condIndep_of_le_right
  结论: {m' m₁ m₂ m₃ : 可测空间 Ω}
  证明: Kernel.indep_of_indep_of_le_right h_indep h32

Depends on / 依赖: Kernel, Kernel.indep_of_indep_of_le_right, h_indep, indep_of_indep_of_le_right
-/
theorem condIndep_of_condIndep_of_le_right {m' m₁ m₂ m₃ : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
    (h_indep : CondIndep m' m₁ m₂ hm' μ) (h32 : m₃ <= m₂) :
    CondIndep m' m₁ m₃ hm' μ :=
  Kernel.indep_of_indep_of_le_right h_indep h32

end CondIndep

/-! ### Deducing `CondIndep` from `iCondIndep` -/


section FromiCondIndepToCondIndep

variable {m' : MeasurableSpace Ω}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

/--
theorem `iCondIndepSets.condIndepSets` / 定理 `iCondIndepSets.condIndepSets`

English:
theorem iCondIndepSets.condIndepSets
  statement: {s : ι -> Set (Set Ω)}
  proof: Kernel.iIndepSets.indepSets h_indep hij

中文:
定理 iCondIndepSets.condIndepSets
  结论: {s : ι -> 集合 (集合 Ω)}
  证明: Kernel.iIndepSets.indepSets h_indep hij

Depends on / 依赖: Kernel, Kernel.iIndepSets.indepSets, h_indep, iIndepSets, indepSets
-/
theorem iCondIndepSets.condIndepSets {s : ι -> Set (Set Ω)}
    (h_indep : iCondIndepSets m' hm' s μ) {i j : ι} (hij : i != j) :
    CondIndepSets m' hm' (s i) (s j) μ :=
  Kernel.iIndepSets.indepSets h_indep hij

/--
theorem `iCondIndep.condIndep` / 定理 `iCondIndep.condIndep`

English:
theorem iCondIndep.condIndep
  statement: {m : ι -> MeasurableSpace Ω}
  proof: Kernel.iIndep.indep h_indep hij

中文:
定理 iCondIndep.condIndep
  结论: {m : ι -> 可测空间 Ω}
  证明: Kernel.iIndep.indep h_indep hij

Depends on / 依赖: Kernel, Kernel.iIndep.indep, h_indep, iIndep
-/
theorem iCondIndep.condIndep {m : ι -> MeasurableSpace Ω}
    (h_indep : iCondIndep m' hm' m μ) {i j : ι} (hij : i != j) :
      CondIndep m' (m i) (m j) hm' μ :=
  Kernel.iIndep.indep h_indep hij

/--
theorem `iCondIndepFun.condIndepFun` / 定理 `iCondIndepFun.condIndepFun`

English:
theorem iCondIndepFun.condIndepFun
  statement: {β : ι -> Type*}
  proof: Kernel.iIndepFun.indepFun hf_Indep hij

中文:
定理 iCondIndepFun.condIndepFun
  结论: {β : ι -> 类型}
  证明: Kernel.iIndepFun.indepFun hf_Indep hij

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun, hf_Indep, iIndepFun, indepFun
-/
theorem iCondIndepFun.condIndepFun {β : ι -> Type*}
    {m : forall x, MeasurableSpace (β x)} {f : forall i, Ω -> β i}
    (hf_Indep : iCondIndepFun m' hm' f μ) {i j : ι} (hij : i != j) :
    CondIndepFun m' hm' (f i) (f j) μ :=
  Kernel.iIndepFun.indepFun hf_Indep hij

end FromiCondIndepToCondIndep

/-!
## π-system lemma

Conditional independence of measurable spaces is equivalent to conditional independence of
generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Conditional independence of σ-algebras implies conditional independence of
  generating π-systems -/

variable {m' : MeasurableSpace Ω}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

/--
theorem `iCondIndep.iCondIndepSets` / 定理 `iCondIndep.iCondIndepSets`

English:
theorem iCondIndep.iCondIndepSets
  statement: {m : ι -> MeasurableSpace Ω}
  proof: Kernel.iIndep.iIndepSets hms h_indep

中文:
定理 iCondIndep.iCondIndepSets
  结论: {m : ι -> 可测空间 Ω}
  证明: Kernel.iIndep.iIndepSets hms h_indep

Depends on / 依赖: Kernel, Kernel.iIndep.iIndepSets, h_indep, iIndep, iIndepSets
-/
theorem iCondIndep.iCondIndepSets {m : ι -> MeasurableSpace Ω}
    {s : ι -> Set (Set Ω)} (hms : forall n, m n = generateFrom (s n))
    (h_indep : iCondIndep m' hm' m μ) :
    iCondIndepSets m' hm' s μ :=
  Kernel.iIndep.iIndepSets hms h_indep

/--
theorem `CondIndep.condIndepSets` / 定理 `CondIndep.condIndepSets`

English:
theorem CondIndep.condIndepSets
  statement: {s1 s2 : Set (Set Ω)}
  proof: Kernel.Indep.indepSets h_indep

中文:
定理 CondIndep.condIndepSets
  结论: {s1 s2 : 集合 (集合 Ω)}
  证明: Kernel.Indep.indepSets h_indep

Depends on / 依赖: Kernel, Kernel.Indep.indepSets, h_indep, indepSets
-/
theorem CondIndep.condIndepSets {s1 s2 : Set (Set Ω)}
    (h_indep : CondIndep m' (generateFrom s1) (generateFrom s2) hm' μ) :
    CondIndepSets m' hm' s1 s2 μ :=
  Kernel.Indep.indepSets h_indep

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Conditional independence of generating π-systems implies conditional independence of
  σ-algebras -/

variable {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

/--
theorem `CondIndepSets.condIndep` / 定理 `CondIndepSets.condIndep`

English:
theorem CondIndepSets.condIndep
  proof: Kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp

中文:
定理 CondIndepSets.condIndep
  证明: Kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.indep
-/
theorem CondIndepSets.condIndep
    {p1 p2 : Set (Set Ω)} (h1 : m₁ <= mΩ) (h2 : m₂ <= mΩ)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2)
    (hpm1 : m₁ = generateFrom p1) (hpm2 : m₂ = generateFrom p2)
    (hyp : CondIndepSets m' hm' p1 p2 μ) :
    CondIndep m' m₁ m₂ hm' μ :=
  Kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp

/--
theorem `CondIndepSets.condIndep'` / 定理 `CondIndepSets.condIndep'`

English:
theorem CondIndepSets.condIndep'
  proof: Kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp

中文:
定理 CondIndepSets.condIndep'
  证明: Kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.indep
-/
theorem CondIndepSets.condIndep'
    {p1 p2 : Set (Set Ω)} (hp1m : forall s in p1, MeasurableSet s) (hp2m : forall s in p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : CondIndepSets m' hm' p1 p2 μ) :
    CondIndep m' (generateFrom p1) (generateFrom p2) hm' μ :=
  Kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp

/--
theorem `condIndepSets_piiUnionInter_of_disjoint` / 定理 `condIndepSets_piiUnionInter_of_disjoint`

English:
theorem condIndepSets_piiUnionInter_of_disjoint
  statement: {s : ι -> Set (Set Ω)}
  proof: Kernel.indepSets_piiUnionInter_of_disjoint h_indep hST

中文:
定理 condIndepSets_piiUnion整数er_of_disjoint
  结论: {s : ι -> 集合 (集合 Ω)}
  证明: Kernel.indepSets_piiUnionInter_of_disjoint h_indep hST

Depends on / 依赖: Kernel, Kernel.indepSets_piiUnionInter_of_disjoint, h_indep, indepSets_piiUnionInter_of_disjoint
-/
theorem condIndepSets_piiUnionInter_of_disjoint {s : ι -> Set (Set Ω)}
    {S T : Set ι} (h_indep : iCondIndepSets m' hm' s μ) (hST : Disjoint S T) :
    CondIndepSets m' hm' (piiUnionInter s S) (piiUnionInter s T) μ :=
  Kernel.indepSets_piiUnionInter_of_disjoint h_indep hST

/--
theorem `iCondIndepSet.condIndep_generateFrom_of_disjoint` / 定理 `iCondIndepSet.condIndep_generateFrom_of_disjoint`

English:
theorem iCondIndepSet.condIndep_generateFrom_of_disjoint
  statement: {s : ι -> Set Ω}
  proof: Kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST

中文:
定理 iCondIndepSet.condIndep_generateFrom_of_disjoint
  结论: {s : ι -> 集合 Ω}
  证明: Kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST

Depends on / 依赖: Kernel, Kernel.iIndepSet.indep_generateFrom_of_disjoint, iIndepSet, indep_generateFrom_of_disjoint
-/
theorem iCondIndepSet.condIndep_generateFrom_of_disjoint {s : ι -> Set Ω}
    (hsm : forall n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (S T : Set ι)
    (hST : Disjoint S T) :
    CondIndep m' (generateFrom { t | exists n in S, s n = t })
      (generateFrom { t | exists k in T, s k = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST

/--
theorem `condIndep_iSup_of_disjoint` / 定理 `condIndep_iSup_of_disjoint`

English:
theorem condIndep_iSup_of_disjoint
  statement: {m : ι -> MeasurableSpace Ω}
  proof: Kernel.indep_iSup_of_disjoint h_le h_indep hST

中文:
定理 condIndep_iSup_of_disjoint
  结论: {m : ι -> 可测空间 Ω}
  证明: Kernel.indep_iSup_of_disjoint h_le h_indep hST

Depends on / 依赖: Kernel, Kernel.indep_iSup_of_disjoint, h_indep, h_le, indep_iSup_of_disjoint
-/
theorem condIndep_iSup_of_disjoint {m : ι -> MeasurableSpace Ω}
    (h_le : forall i, m i <= mΩ) (h_indep : iCondIndep m' hm' m μ) {S T : Set ι} (hST : Disjoint S T) :
    CondIndep m' (⨆ i in S, m i) (⨆ i in T, m i) hm' μ :=
  Kernel.indep_iSup_of_disjoint h_le h_indep hST

/--
theorem `condIndep_iSup_of_directed_le` / 定理 `condIndep_iSup_of_directed_le`

English:
theorem condIndep_iSup_of_directed_le
  statement: {m : ι -> MeasurableSpace Ω}
  proof: Kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm

中文:
定理 condIndep_iSup_of_directed_le
  结论: {m : ι -> 可测空间 Ω}
  证明: Kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm

Depends on / 依赖: Kernel, Kernel.indep_iSup_of_directed_le, h_indep, h_le, indep_iSup_of_directed_le
-/
theorem condIndep_iSup_of_directed_le {m : ι -> MeasurableSpace Ω}
    (h_indep : forall i, CondIndep m' (m i) m₁ hm' μ)
    (h_le : forall i, m i <= mΩ) (h_le' : m₁ <= mΩ) (hm : Directed (· <= ·) m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  Kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm

/--
theorem `iCondIndepSet.condIndep_generateFrom_lt` / 定理 `iCondIndepSet.condIndep_generateFrom_lt`

English:
theorem iCondIndepSet.condIndep_generateFrom_lt
  statement: [Preorder ι] {s : ι -> Set Ω}
  proof: Kernel.iIndepSet.indep_generateFrom_lt hsm hs i

中文:
定理 iCondIndepSet.condIndep_generateFrom_lt
  结论: [预序 ι] {s : ι -> 集合 Ω}
  证明: Kernel.iIndepSet.indep_generateFrom_lt hsm hs i

Depends on / 依赖: Kernel, Kernel.iIndepSet.indep_generateFrom_lt, iIndepSet, indep_generateFrom_lt
-/
theorem iCondIndepSet.condIndep_generateFrom_lt [Preorder ι] {s : ι -> Set Ω}
    (hsm : forall n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (i : ι) :
    CondIndep m' (generateFrom {s i}) (generateFrom { t | exists j < i, s j = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_lt hsm hs i

/--
theorem `iCondIndepSet.condIndep_generateFrom_le` / 定理 `iCondIndepSet.condIndep_generateFrom_le`

English:
theorem iCondIndepSet.condIndep_generateFrom_le
  statement: [Preorder ι] {s : ι -> Set Ω}
  proof: Kernel.iIndepSet.indep_generateFrom_le hsm hs i hk

中文:
定理 iCondIndepSet.condIndep_generateFrom_le
  结论: [预序 ι] {s : ι -> 集合 Ω}
  证明: Kernel.iIndepSet.indep_generateFrom_le hsm hs i hk

Depends on / 依赖: Kernel, Kernel.iIndepSet.indep_generateFrom_le, iIndepSet, indep_generateFrom_le
-/
theorem iCondIndepSet.condIndep_generateFrom_le [Preorder ι] {s : ι -> Set Ω}
    (hsm : forall n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (i : ι) {k : ι} (hk : i < k) :
    CondIndep m' (generateFrom {s k}) (generateFrom { t | exists j <= i, s j = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_le hsm hs i hk

/--
theorem `iCondIndepSet.condIndep_generateFrom_le_nat` / 定理 `iCondIndepSet.condIndep_generateFrom_le_nat`

English:
theorem iCondIndepSet.condIndep_generateFrom_le_nat
  statement: {s : Nat -> Set Ω}
  proof: Kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n

中文:
定理 iCondIndepSet.condIndep_generateFrom_le_nat
  结论: {s : 自然数 -> 集合 Ω}
  证明: Kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n

Depends on / 依赖: Kernel, Kernel.iIndepSet.indep_generateFrom_le_nat, iIndepSet, indep_generateFrom_le_nat
-/
theorem iCondIndepSet.condIndep_generateFrom_le_nat {s : Nat -> Set Ω}
    (hsm : forall n, MeasurableSet (s n)) (hs : iCondIndepSet m' hm' s μ) (n : Nat) :
    CondIndep m' (generateFrom {s (n + 1)}) (generateFrom { t | exists k <= n, s k = t }) hm' μ :=
  Kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n

/--
theorem `condIndep_iSup_of_monotone` / 定理 `condIndep_iSup_of_monotone`

English:
theorem condIndep_iSup_of_monotone
  statement: [SemilatticeSup ι] {m : ι -> MeasurableSpace Ω}
  proof: Kernel.indep_iSup_of_monotone h_indep h_le h_le' hm

中文:
定理 condIndep_iSup_of_monotone
  结论: [SemilatticeSup ι] {m : ι -> 可测空间 Ω}
  证明: Kernel.indep_iSup_of_monotone h_indep h_le h_le' hm

Depends on / 依赖: Kernel, Kernel.indep_iSup_of_monotone, h_indep, h_le, indep_iSup_of_monotone
-/
theorem condIndep_iSup_of_monotone [SemilatticeSup ι] {m : ι -> MeasurableSpace Ω}
    (h_indep : forall i, CondIndep m' (m i) m₁ hm' μ) (h_le : forall i, m i <= mΩ) (h_le' : m₁ <= mΩ)
    (hm : Monotone m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  Kernel.indep_iSup_of_monotone h_indep h_le h_le' hm

/--
theorem `condIndep_iSup_of_antitone` / 定理 `condIndep_iSup_of_antitone`

English:
theorem condIndep_iSup_of_antitone
  statement: [SemilatticeInf ι] {m : ι -> MeasurableSpace Ω}
  proof: Kernel.indep_iSup_of_antitone h_indep h_le h_le' hm

中文:
定理 condIndep_iSup_of_antitone
  结论: [SemilatticeInf ι] {m : ι -> 可测空间 Ω}
  证明: Kernel.indep_iSup_of_antitone h_indep h_le h_le' hm

Depends on / 依赖: Kernel, Kernel.indep_iSup_of_antitone, h_indep, h_le, indep_iSup_of_antitone
-/
theorem condIndep_iSup_of_antitone [SemilatticeInf ι] {m : ι -> MeasurableSpace Ω}
    (h_indep : forall i, CondIndep m' (m i) m₁ hm' μ) (h_le : forall i, m i <= mΩ) (h_le' : m₁ <= mΩ)
    (hm : Antitone m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  Kernel.indep_iSup_of_antitone h_indep h_le h_le' hm

/--
theorem `iCondIndepSets.piiUnionInter_of_notMem` / 定理 `iCondIndepSets.piiUnionInter_of_notMem`

English:
theorem iCondIndepSets.piiUnionInter_of_notMem
  statement: {π : ι -> Set (Set Ω)} {a : ι} {S : Finset ι}
  proof: Kernel.iIndepSets.piiUnionInter_of_notMem hp_ind haS

中文:
定理 iCondIndepSets.piiUnion整数er_of_notMem
  结论: {π : ι -> 集合 (集合 Ω)} {a : ι} {S : 有限集 ι}
  证明: Kernel.iIndepSets.piiUnionInter_of_notMem hp_ind haS

Depends on / 依赖: Kernel, Kernel.iIndepSets.piiUnionInter_of_notMem, hp_ind, iIndepSets, piiUnionInter_of_notMem
-/
theorem iCondIndepSets.piiUnionInter_of_notMem {π : ι -> Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iCondIndepSets m' hm' π μ) (haS : a ∉ S) :
    CondIndepSets m' hm' (piiUnionInter π S) (π a) μ :=
  Kernel.iIndepSets.piiUnionInter_of_notMem hp_ind haS

/--
theorem `iCondIndepSets.iCondIndep` / 定理 `iCondIndepSets.iCondIndep`

English:
theorem iCondIndepSets.iCondIndep
  statement: (m : ι -> MeasurableSpace Ω)
  proof: Kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind

中文:
定理 iCondIndepSets.iCondIndep
  结论: (m : ι -> 可测空间 Ω)
  证明: Kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind

Depends on / 依赖: Kernel, Kernel.iIndepSets.iIndep, h_generate, h_ind, h_le, h_pi, iIndep, iIndepSets
-/
theorem iCondIndepSets.iCondIndep (m : ι -> MeasurableSpace Ω)
    (h_le : forall i, m i <= mΩ) (π : ι -> Set (Set Ω)) (h_pi : forall n, IsPiSystem (π n))
    (h_generate : forall i, m i = generateFrom (π i)) (h_ind : iCondIndepSets m' hm' π μ) :
    iCondIndep m' hm' m μ :=
  Kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind

end FromPiSystemsToMeasurableSpaces

section CondIndepSet

/-! ### Conditional independence of measurable sets

-/

variable {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' <= mΩ}
  {s t : Set Ω} (S T : Set (Set Ω))

/--
theorem `CondIndepSets.condIndepSet_of_mem` / 定理 `CondIndepSets.condIndepSet_of_mem`

English:
theorem CondIndepSets.condIndepSet_of_mem
  statement: (hs : s in S) (ht : t in T)
  proof: Kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep

中文:
定理 CondIndepSets.condIndepSet_of_mem
  结论: (hs : s in S) (ht : t in T)
  证明: Kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.indepSet_of_mem, h_indep, hs_meas, ht_meas, indepSet_of_mem
-/
theorem CondIndepSets.condIndepSet_of_mem (hs : s in S) (ht : t in T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t) (μ : Measure Ω) [IsFiniteMeasure μ]
    (h_indep : CondIndepSets m' hm' S T μ) :
    CondIndepSet m' hm' s t μ :=
  Kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep

/--
theorem `CondIndep.condIndepSet_of_measurableSet` / 定理 `CondIndep.condIndepSet_of_measurableSet`

English:
theorem CondIndep.condIndepSet_of_measurableSet
  statement: {μ : Measure Ω} [IsFiniteMeasure μ]
  proof: Kernel.Indep.indepSet_of_measurableSet h_indep hs ht

中文:
定理 CondIndep.condIndepSet_of_measurableSet
  结论: {μ : 测度 Ω} [是有限测度 μ]
  证明: Kernel.Indep.indepSet_of_measurableSet h_indep hs ht

Depends on / 依赖: Kernel, Kernel.Indep.indepSet_of_measurableSet, h_indep, indepSet_of_measurableSet
-/
theorem CondIndep.condIndepSet_of_measurableSet {μ : Measure Ω} [IsFiniteMeasure μ]
    (h_indep : CondIndep m' m₁ m₂ hm' μ) {s t : Set Ω} (hs : MeasurableSet[m₁] s)
    (ht : MeasurableSet[m₂] t) :
    CondIndepSet m' hm' s t μ :=
  Kernel.Indep.indepSet_of_measurableSet h_indep hs ht

/--
theorem `condIndep_iff_forall_condIndepSet` / 定理 `condIndep_iff_forall_condIndepSet`

English:
theorem condIndep_iff_forall_condIndepSet
  given: (μ : Measure Ω) [IsFiniteMeasure μ]
  proof: Kernel.indep_iff_forall_indepSet m₁ m₂ _ _

中文:
定理 condIndep_iff_对任意_condIndepSet
  条件: (μ : 测度 Ω) [是有限测度 μ]
  证明: Kernel.indep_iff_forall_indepSet m₁ m₂ _ _

Depends on / 依赖: Kernel, Kernel.indep_iff_forall_indepSet, indep_iff_forall_indepSet
-/
theorem condIndep_iff_forall_condIndepSet (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ ↔ forall s t, MeasurableSet[m₁] s -> MeasurableSet[m₂] t
      -> CondIndepSet m' hm' s t μ :=
  Kernel.indep_iff_forall_indepSet m₁ m₂ _ _

end CondIndepSet

section CondIndepFun

/-! ### Conditional independence of random variables

-/

variable {β β' : Type*} {m' : MeasurableSpace Ω}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' <= mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {f : Ω -> β} {g : Ω -> β'}

/--
theorem `condIndepFun_iff_condExp_inter_preimage_eq_mul` / 定理 `condIndepFun_iff_condExp_inter_preimage_eq_mul`

English:
theorem condIndepFun_iff_condExp_inter_preimage_eq_mul
  statement: {mβ : MeasurableSpace β}
  proof: by
  rw [condIndepFun_iff _ _ _ _ hf hg]
  refine ⟨fun h s t hs ht => ?_, fun h s t => ?_⟩
  · exact h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact h s t hs ht

中文:
定理 condIndepFun_iff_condExp_inter_preimage_eq_mul
  结论: {mβ : 可测空间 β}
  证明: by
  rw [condIndepFun_iff _ _ _ _ hf hg]
  refine ⟨fun h s t hs ht => ?_, fun h s t => ?_⟩
  · exact h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact h s t hs ht

Depends on / 依赖: condIndepFun_iff
-/
theorem condIndepFun_iff_condExp_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ ↔
      forall s t, MeasurableSet s -> MeasurableSet t
        -> (μ⟦f ⁻¹' s inter g ⁻¹' t | m'⟧) =ᵐ[μ] fun ω => (μ⟦f ⁻¹' s | m'⟧) ω * (μ⟦g ⁻¹' t | m'⟧) ω := by
  rw [condIndepFun_iff _ _ _ _ hf hg]
  refine ⟨fun h s t hs ht => ?_, fun h s t => ?_⟩
  · exact h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact h s t hs ht

/--
theorem `iCondIndepFun_iff_condExp_inter_preimage_eq_mul` / 定理 `iCondIndepFun_iff_condExp_inter_preimage_eq_mul`

English:
theorem iCondIndepFun_iff_condExp_inter_preimage_eq_mul
  statement: {β : ι -> Type*}
  proof: by
  rw [iCondIndepFun_iff]
  swap
  · exact hf
  refine ⟨fun h s sets h_sets => ?_, fun h s sets h_sets => ?_⟩
  · refine h s (g := fun i => f i ⁻¹' (sets i)) (fun i hi => ?_)
    exact ⟨sets i, h_sets i hi, rfl⟩
  · classical
    let g := fun i => if hi : i in s then (h_sets i hi).choose else Set.

中文:
定理 iCondIndepFun_iff_condExp_inter_preimage_eq_mul
  结论: {β : ι -> 类型}
  证明: by
  rw [iCondIndepFun_iff]
  swap
  · exact hf
  refine ⟨fun h s sets h_sets => ?_, fun h s sets h_sets => ?_⟩
  · refine h s (g := fun i => f i ⁻¹' (sets i)) (fun i hi => ?_)
    exact ⟨sets i, h_sets i hi, rfl⟩
  · classical
    let g := fun i => if hi : i in s then (h_sets i hi).choose else Set.

Depends on / 依赖: Set.univ, choose_spec, classical, dif_pos, h_sets, iCondIndepFun_iff, specialize
-/
theorem iCondIndepFun_iff_condExp_inter_preimage_eq_mul {β : ι -> Type*}
    (m : forall x, MeasurableSpace (β x)) (f : forall i, Ω -> β i) (hf : forall i, Measurable (f i)) :
    iCondIndepFun m' hm' f μ ↔
      forall (S : Finset ι) {sets : forall i : ι, Set (β i)} (_H : forall i, i in S -> MeasurableSet[m i] (sets i)),
        (μ⟦⋂ i in S, f i ⁻¹' sets i | m'⟧) =ᵐ[μ] ∏ i in S, (μ⟦f i ⁻¹' sets i | m'⟧) := by
  rw [iCondIndepFun_iff]
  swap
  · exact hf
  refine ⟨fun h s sets h_sets => ?_, fun h s sets h_sets => ?_⟩
  · refine h s (g := fun i => f i ⁻¹' (sets i)) (fun i hi => ?_)
    exact ⟨sets i, h_sets i hi, rfl⟩
  · classical
    let g := fun i => if hi : i in s then (h_sets i hi).choose else Set.univ
    specialize h s (sets := g) (fun i hi => ?_)
    · simp only [g, dif_pos hi]
      exact (h_sets i hi).choose_spec.1
    · have hg : forall i in s, sets i = f i ⁻¹' g i := by
        intro i hi
        rw [(h_sets i hi).choose_spec.2.symm]
        simp only [g, dif_pos hi]
      convert! h with i hi i hi <;> exact hg i hi

/--
theorem `condIndepFun_iff_condIndepSet_preimage` / 定理 `condIndepFun_iff_condIndepSet_preimage`

English:
theorem condIndepFun_iff_condIndepSet_preimage
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  simp only [CondIndepFun, CondIndepSet, Kernel.indepFun_iff_indepSet_preimage hf hg]

@[symm]
nonrec theorem CondIndepFun.symm {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f : Ω -> β} {g : Ω -> β'} (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' g f μ :=
  hfg.symm

中文:
定理 condIndepFun_iff_condIndepSet_preimage
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  simp only [CondIndepFun, CondIndepSet, Kernel.indepFun_iff_indepSet_preimage hf hg]

@[symm]
nonrec theorem CondIndepFun.symm {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f : Ω -> β} {g : Ω -> β'} (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' g f μ :=
  hfg.symm

Depends on / 依赖: CondIndepFun, CondIndepSet, Kernel, Kernel.indepFun_iff_indepSet_preimage, indepFun_iff_indepSet_preimage
-/
theorem condIndepFun_iff_condIndepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ ↔
      forall s t, MeasurableSet s -> MeasurableSet t -> CondIndepSet m' hm' (f ⁻¹' s) (g ⁻¹' t) μ := by
  simp only [CondIndepFun, CondIndepSet, Kernel.indepFun_iff_indepSet_preimage hf hg]

@[symm]
nonrec theorem CondIndepFun.symm {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f : Ω -> β} {g : Ω -> β'} (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' g f μ :=
  hfg.symm

/--
theorem `CondIndepFun.comp` / 定理 `CondIndepFun.comp`

English:
theorem CondIndepFun.comp
  statement: {γ γ' : Type*} {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
  proof: Kernel.IndepFun.comp hfg hφ hψ

中文:
定理 CondIndepFun.comp
  结论: {γ γ' : 类型} {_mβ : 可测空间 β} {_mβ' : 可测空间 β'}
  证明: Kernel.IndepFun.comp hfg hφ hψ

Depends on / 依赖: IndepFun, Kernel, Kernel.IndepFun.comp
-/
theorem CondIndepFun.comp {γ γ' : Type*} {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β -> γ} {ψ : β' -> γ'}
    (hfg : CondIndepFun m' hm' f g μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    CondIndepFun m' hm' (φ ∘ f) (ψ ∘ g) μ :=
  Kernel.IndepFun.comp hfg hφ hψ

/--
lemma `condIndepFun_const_left` / 引理 `condIndepFun_const_left`

English:
lemma condIndepFun_const_left
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: Kernel.indepFun_const_left c X

中文:
引理 condIndepFun_const_left
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: Kernel.indepFun_const_left c X

Depends on / 依赖: Kernel, Kernel.indepFun_const_left, indepFun_const_left
-/
lemma condIndepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (c : β) (X : Ω -> β') :
    CondIndepFun m' hm' (fun _ => c) X μ :=
  Kernel.indepFun_const_left c X

/--
lemma `condIndepFun_const_right` / 引理 `condIndepFun_const_right`

English:
lemma condIndepFun_const_right
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: Kernel.indepFun_const_right X c

中文:
引理 condIndepFun_const_right
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: Kernel.indepFun_const_right X c

Depends on / 依赖: Kernel, Kernel.indepFun_const_right, indepFun_const_right
-/
lemma condIndepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (X : Ω -> β) (c : β') :
    CondIndepFun m' hm' X (fun _ => c) μ :=
  Kernel.indepFun_const_right X c

/--
theorem `CondIndepFun.neg_right` / 定理 `CondIndepFun.neg_right`

English:
theorem CondIndepFun.neg_right
  statement: {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
  proof: hfg.comp measurable_id measurable_neg

中文:
定理 CondIndepFun.neg_right
  结论: {_mβ : 可测空间 β} {_mβ' : 可测空间 β'} [取负 β']
  证明: hfg.comp measurable_id measurable_neg

Depends on / 依赖: hfg.comp, measurable_id, measurable_neg
-/
theorem CondIndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' f (-g) μ := hfg.comp measurable_id measurable_neg

/--
theorem `CondIndepFun.neg_left` / 定理 `CondIndepFun.neg_left`

English:
theorem CondIndepFun.neg_left
  statement: {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
  proof: hfg.comp measurable_neg measurable_id

中文:
定理 CondIndepFun.neg_left
  结论: {_mβ : 可测空间 β} {_mβ' : 可测空间 β'} [取负 β]
  证明: hfg.comp measurable_neg measurable_id

Depends on / 依赖: hfg.comp, measurable_id, measurable_neg
-/
theorem CondIndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' (-f) g μ := hfg.comp measurable_neg measurable_id

/--
lemma `condIndepFun_of_measurable_left` / 引理 `condIndepFun_of_measurable_left`

English:
lemma condIndepFun_of_measurable_left
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  rw [condIndepFun_iff _ hm' _ _ (hX.mono hm' le_rfl) hY]
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  rw [show (fun ω : Ω => (1 : Real)) = 1 from rfl]; rw [Set.inter_indicator_one]
  calc μ[(X ⁻¹' s).indicator 1 * (Y ⁻¹' t).indicator 1 | m']
  _ =ᵐ[μ] (X ⁻¹' s).indicator 1 * μ[(Y ⁻¹' t).indicator 1 

中文:
引理 condIndepFun_of_measurable_left
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  rw [condIndepFun_iff _ hm' _ _ (hX.mono hm' le_rfl) hY]
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  rw [show (fun ω : Ω => (1 : Real)) = 1 from rfl]; rw [Set.inter_indicator_one]
  calc μ[(X ⁻¹' s).indicator 1 * (Y ⁻¹' t).indicator 1 | m']
  _ =ᵐ[μ] (X ⁻¹' s).indicator 1 * μ[(Y ⁻¹' t).indicator 1 

Depends on / 依赖: Set.indicato, Set.inter_indicator_one, ae_of_all, condExp_stronglyMeasurable_mul_of_bound, condIndepFun_iff, hX.mono, indicato, indicator, integrableOn_const, integrable_indicator_iff, inter_indicator_one, le_rfl, stronglyMeasurable_const, stronglyMeasurable_const.indicator
-/
lemma condIndepFun_of_measurable_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω -> β} {Y : Ω -> β'} (hX : Measurable[m'] X) (hY : Measurable Y) :
    CondIndepFun m' hm' X Y μ := by
  rw [condIndepFun_iff _ hm' _ _ (hX.mono hm' le_rfl) hY]
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  rw [show (fun ω : Ω => (1 : Real)) = 1 from rfl]; rw [Set.inter_indicator_one]
  calc μ[(X ⁻¹' s).indicator 1 * (Y ⁻¹' t).indicator 1 | m']
  _ =ᵐ[μ] (X ⁻¹' s).indicator 1 * μ[(Y ⁻¹' t).indicator 1 | m'] := by
    refine condExp_stronglyMeasurable_mul_of_bound hm' (stronglyMeasurable_const.indicator (hX hs))
      ((integrable_indicator_iff (hY ht)).2 integrableOn_const) 1 (ae_of_all μ fun ω => ?_)
    rw [Set.indicator]
    split_ifs with h <;> simp
  _ =ᵐ[μ] μ[(X ⁻¹' s).indicator 1 | m'] * μ[(Y ⁻¹' t).indicator 1 | m'] := by
    nth_rw 2 [condExp_of_stronglyMeasurable hm']
    · exact stronglyMeasurable_const.indicator (hX hs)
    · exact (integrable_indicator_iff ((hX.le hm') hs)).2 integrableOn_const

/--
lemma `condIndepFun_of_measurable_right` / 引理 `condIndepFun_of_measurable_right`

English:
lemma condIndepFun_of_measurable_right
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: (condIndepFun_of_measurable_left hY hX).symm

中文:
引理 condIndepFun_of_measurable_right
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: (condIndepFun_of_measurable_left hY hX).symm

Depends on / 依赖: condIndepFun_of_measurable_left
-/
lemma condIndepFun_of_measurable_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω -> β} {Y : Ω -> β'} (hX : Measurable X) (hY : Measurable[m'] Y) :
    CondIndepFun m' hm' X Y μ :=
  (condIndepFun_of_measurable_left hY hX).symm

/--
lemma `condIndepFun_self_left` / 引理 `condIndepFun_self_left`

English:
lemma condIndepFun_self_left
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: condIndepFun_of_measurable_left (comap_measurable Z) hX

中文:
引理 condIndepFun_self_left
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: condIndepFun_of_measurable_left (comap_measurable Z) hX

Depends on / 依赖: comap_measurable, condIndepFun_of_measurable_left
-/
lemma condIndepFun_self_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω -> β} {Z : Ω -> β'} (hX : Measurable X) (hZ : Measurable Z) :
    Z ⟂ᵢ[Z, hZ; μ] X :=
  condIndepFun_of_measurable_left (comap_measurable Z) hX

/--
lemma `condIndepFun_self_right` / 引理 `condIndepFun_self_right`

English:
lemma condIndepFun_self_right
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: condIndepFun_of_measurable_right hX (comap_measurable Z)

中文:
引理 condIndepFun_self_right
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: condIndepFun_of_measurable_right hX (comap_measurable Z)

Depends on / 依赖: comap_measurable, condIndepFun_of_measurable_right
-/
lemma condIndepFun_self_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {X : Ω -> β} {Z : Ω -> β'} (hX : Measurable X) (hZ : Measurable Z) :
    X ⟂ᵢ[Z, hZ; μ] Z :=
  condIndepFun_of_measurable_right hX (comap_measurable Z)

/--
theorem `condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map` / 定理 `condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map`

English:
theorem condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
  proof: Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg

中文:
定理 condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
  证明: Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg

Depends on / 依赖: Kernel, Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map, indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
-/
theorem condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ
      ↔ (μ.trim hm') otimesₘ (condExpKernel μ m').map (fun ω => (f ω, g ω))
        = (μ.trim hm') otimesₘ ((condExpKernel μ m').map f ×ₖ (condExpKernel μ m').map g) :=
  Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg

/--
theorem `condIndepFun_iff_map_prod_eq_prod_map_map` / 定理 `condIndepFun_iff_map_prod_eq_prod_map_map`

English:
theorem condIndepFun_iff_map_prod_eq_prod_map_map
  proof: by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg]; rw [← Kernel.compProd_eq_iff]

中文:
定理 condIndepFun_iff_map_prod_eq_prod_map_map
  证明: by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg]; rw [← Kernel.compProd_eq_iff]

Depends on / 依赖: Kernel, Kernel.compProd_eq_iff, compProd_eq_iff, condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
-/
theorem condIndepFun_iff_map_prod_eq_prod_map_map
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [CountableOrCountablyGenerated Ω (β × β')]
    (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ
      ↔ (condExpKernel μ m').map (fun ω => (f ω, g ω))
        =ᵐ[μ.trim hm'] (condExpKernel μ m').map f ×ₖ (condExpKernel μ m').map g := by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg]; rw [← Kernel.compProd_eq_iff]

/--
lemma `condIndepFun_iff_map_prod_eq_prod_comp_trim` / 引理 `condIndepFun_iff_map_prod_eq_prod_comp_trim`

English:
lemma condIndepFun_iff_map_prod_eq_prod_comp_trim
  proof: by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg]
  congr!
  · rw [Measure.compProd_map (by fun_prop), compProd_trim_condExpKernel]
    exact Measure.map_map (by fun_prop) ((measurable_id.mono le_rfl hm').prodMk measurable_id)
  · rw [Measure.compProd_eq_comp_prod]

中文:
引理 condIndepFun_iff_map_prod_eq_prod_comp_trim
  证明: by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg]
  congr!
  · rw [Measure.compProd_map (by fun_prop), compProd_trim_condExpKernel]
    exact Measure.map_map (by fun_prop) ((measurable_id.mono le_rfl hm').prodMk measurable_id)
  · rw [Measure.compProd_eq_comp_prod]

Depends on / 依赖: Measure, Measure.compProd_eq_comp_prod, Measure.compProd_map, Measure.map_map, compProd_eq_comp_prod, compProd_map, compProd_trim_condExpKernel, condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map, fun_prop, le_rfl, map_map, measurable_id, measurable_id.mono, prodMk
-/
lemma condIndepFun_iff_map_prod_eq_prod_comp_trim
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} (hf : Measurable f) (hg : Measurable g) :
    CondIndepFun m' hm' f g μ
      ↔ @Measure.map _ _ _ (m'.prod _) (fun ω => (ω, f ω, g ω)) μ
        = (Kernel.id ×ₖ ((condExpKernel μ m').map f ×ₖ (condExpKernel μ m').map g))
          ∘ₘ μ.trim hm' := by
  rw [condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hf hg]
  congr!
  · rw [Measure.compProd_map (by fun_prop), compProd_trim_condExpKernel]
    exact Measure.map_map (by fun_prop) ((measurable_id.mono le_rfl hm').prodMk measurable_id)
  · rw [Measure.compProd_eq_comp_prod]

/--
theorem `condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib` / 定理 `condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib`

English:
theorem condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
  proof: by
  rw [condIndepFun_iff_map_prod_eq_prod_comp_trim hf hg]
  simp_rw [Measure.ext_prod₃_iff]
  have hk_meas {s : Set γ} (hs : MeasurableSet s) : MeasurableSet[mγ.comap k] (k ⁻¹' s) :=
    ⟨s, hs, rfl⟩
  have h_left {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
 

中文:
定理 condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
  证明: by
  rw [condIndepFun_iff_map_prod_eq_prod_comp_trim hf hg]
  simp_rw [Measure.ext_prod₃_iff]
  have hk_meas {s : Set γ} (hs : MeasurableSet s) : MeasurableSet[mγ.comap k] (k ⁻¹' s) :=
    ⟨s, hs, rfl⟩
  have h_left {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
 

Depends on / 依赖: MeasurableSet, Measure, Measure.ext_prod, Measure.map, Measure.map_apply, condIndepFun_iff_map_prod_eq_prod_comp_trim, h_left, hk_meas, map_apply, simp_rw
-/
theorem condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    {γ : Type*} {mγ : MeasurableSpace γ} {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β']
    (hf : Measurable f) (hg : Measurable g) {k : Ω -> γ} (hk : Measurable k) :
    f ⟂ᵢ[k, hk; μ] g ↔
      μ.map (fun ω => (k ω, f ω, g ω)) =
        (Kernel.id ×ₖ (condDistrib f k μ ×ₖ condDistrib g k μ)) ∘ₘ μ.map k := by
  rw [condIndepFun_iff_map_prod_eq_prod_comp_trim hf hg]
  simp_rw [Measure.ext_prod₃_iff]
  have hk_meas {s : Set γ} (hs : MeasurableSet s) : MeasurableSet[mγ.comap k] (k ⁻¹' s) :=
    ⟨s, hs, rfl⟩
  have h_left {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      (μ.map (fun ω => (k ω, f ω, g ω))) (s ×ˢ t ×ˢ u) =
        (@Measure.map _ _ _ ((mγ.comap k).prod inferInstance)
          (fun ω => (ω, f ω, g ω)) μ) ((k ⁻¹' s) ×ˢ t ×ˢ u) := by
    rw [Measure.map_apply (by fun_prop) (hs.prod (ht.prod hu))]; rw [Measure.map_apply _ ((hk_meas hs).prod (ht.prod hu))]
    · simp [Set.mk_preimage_prod]
    · exact (measurable_id.mono le_rfl hk.comap_le).prodMk (by fun_prop)
  have h_right {s : Set γ} {t : Set β} {u : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hu : MeasurableSet u) :
      ((Kernel.id ×ₖ (condDistrib f k μ ×ₖ condDistrib g k μ)) ∘ₘ μ.map k) (s ×ˢ t ×ˢ u) =
        ((Kernel.id ×ₖ
          ((condExpKernel μ (mγ.comap k)).map f ×ₖ (condExpKernel μ (mγ.comap k)).map g)) ∘ₘ
        μ.trim hk.comap_le) ((k ⁻¹' s) ×ˢ t ×ˢ u) := by
    rw [Measure.bind_apply ((hk_meas hs).prod (ht.prod hu)) (by fun_prop)]; rw [Measure.bind_apply (hs.prod (ht.prod hu)) (by fun_prop)]; rw [lintegral_map ?_ (by fun_prop)]; rw [lintegral_trim]
    rotate_left
    · exact Kernel.measurable_coe _ ((hk_meas hs).prod (ht.prod hu))
    · exact Kernel.measurable_coe _ (hs.prod (ht.prod hu))
    refine lintegral_congr_ae ?_
    filter_upwards [condDistrib_apply_ae_eq_condExpKernel_map hf hk ht,
      condDistrib_apply_ae_eq_condExpKernel_map hg hk hu] with a haX haT
    simp only [Kernel.prod_apply_prod, Kernel.id_apply, Measure.dirac_apply' _ hs]
    rw [@Measure.dirac_apply' _ (mγ.comap k) _ _ (hk_meas hs)]
    congr
  refine ⟨fun h s t u hs ht hu => ?_, fun h => ?_⟩
  · convert! h (hk_meas hs) ht hu
    · exact h_left hs ht hu
    · exact h_right hs ht hu
  · rintro - t u ⟨s, hs, rfl⟩ ht hu
    convert! h hs ht hu
    · exact (h_left hs ht hu).symm
    · exact (h_right hs ht hu).symm

/--
theorem `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` / 定理 `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`

English:
theorem condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
  proof: by
  rw [condDistrib_ae_eq_iff_measure_eq_compProd (μ := μ) _ hf.aemeasurable]; rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hg hf hk]; rw [Measure.compProd_eq_comp_prod]
  let e : γ × β' × β ≃ᵐ (γ × β') × β := MeasurableEquiv.prodAssoc.symm
  have h_eq : ((Kernel.id ×ₖ condDis

中文:
定理 condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
  证明: by
  rw [condDistrib_ae_eq_iff_measure_eq_compProd (μ := μ) _ hf.aemeasurable]; rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hg hf hk]; rw [Measure.compProd_eq_comp_prod]
  let e : γ × β' × β ≃ᵐ (γ × β') × β := MeasurableEquiv.prodAssoc.symm
  have h_eq : ((Kernel.id ×ₖ condDis

Depends on / 依赖: Kernel, Kernel.id, MeasurableEquiv, MeasurableEquiv.prodAssoc.symm, Measure, Measure.compProd_eq_comp_prod, aemeasurable, compProd_eq_comp_prod, condDistrib, condDistrib_ae_eq_iff_measure_eq_compProd, condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib, h_eq, hf.aemeasurable, prodAssoc, prodMkRight
-/
theorem condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    {γ : Type*} {mγ : MeasurableSpace γ} {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β']
    (hf : Measurable f) (hg : Measurable g) {k : Ω -> γ} (hk : Measurable k) :
    g ⟂ᵢ[k, hk; μ] f ↔
      condDistrib f (fun ω => (k ω, g ω)) μ =ᵐ[μ.map (fun ω => (k ω, g ω))]
        (condDistrib f k μ).prodMkRight _ := by
  rw [condDistrib_ae_eq_iff_measure_eq_compProd (μ := μ) _ hf.aemeasurable]; rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hg hf hk]; rw [Measure.compProd_eq_comp_prod]
  let e : γ × β' × β ≃ᵐ (γ × β') × β := MeasurableEquiv.prodAssoc.symm
  have h_eq : ((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k =
      (Kernel.id ×ₖ (condDistrib f k μ).prodMkRight _) ∘ₘ μ.map (fun a => (k a, g a)) := by
    calc ((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k
    _ = (Kernel.id ×ₖ (condDistrib f k μ).prodMkRight _) ∘ₘ (μ.map k otimesₘ condDistrib g k μ) := by
      rw [Measure.compProd_eq_comp_prod]; rw [Measure.comp_assoc]
      congr 2
      have h := Kernel.prod_prodMkRight_comp_deterministic_prod (condDistrib g k μ)
        (condDistrib f k μ) Kernel.id measurable_id
      rw [← Kernel.id] at h
      simpa using h.symm
    _ = (Kernel.id ×ₖ (condDistrib f k μ).prodMkRight _) ∘ₘ μ.map (fun a => (k a, g a)) := by
      rw [compProd_map_condDistrib hg.aemeasurable]
  rw [← h_eq]
  have h1 : μ.map (fun x => ((k x, g x), f x)) = (μ.map (fun a => (k a, g a, f a))).map e := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have h1_symm : μ.map (fun a => (k a, g a, f a)) =
      (μ.map (fun x => ((k x, g x), f x))).map e.symm := by
    rw [h1]; rw [Measure.map_map (by fun_prop) (by fun_prop)]; rw [MeasurableEquiv.symm_comp_self]; rw [Measure.map_id]
  have h2 : ((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k =
      ((Kernel.id ×ₖ (condDistrib g k μ ×ₖ condDistrib f k μ)) ∘ₘ μ.map k).map e := by
    rw [← Measure.deterministic_comp_eq_map e.measurable]; rw [Measure.comp_assoc]
    congr 2
    unfold e
    rw [Kernel.deterministic_comp_eq_map]; rw [Kernel.prodAssoc_symm_prod]
  have h2_symm : (Kernel.id ×ₖ (condDistrib g k μ ×ₖ condDistrib f k μ)) ∘ₘ μ.map k =
      (((Kernel.id ×ₖ condDistrib g k μ) ×ₖ condDistrib f k μ) ∘ₘ μ.map k).map e.symm := by
    rw [h2]; rw [Measure.map_map (by fun_prop) (by fun_prop)]; rw [MeasurableEquiv.symm_comp_self]; rw [Measure.map_id]
  rw [h1]; rw [h2]
  exact ⟨fun h => by rw [h], fun h => by rw [h1_symm, h1, h2_symm, h2, h]⟩

section iCondIndepFun
variable {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)} {f : forall i, Ω -> β i}

@[nontriviality]
/--
lemma `iCondIndepFun.of_subsingleton` / 引理 `iCondIndepFun.of_subsingleton`

English:
lemma iCondIndepFun.of_subsingleton
  given: [Subsingleton ι]
  statement: iCondIndepFun m' hm' f μ
  proof: Kernel.iIndepFun.of_subsingleton

中文:
引理 iCondIndepFun.of_subsingleton
  条件: [子单例 ι]
  结论: iCondIndepFun m' hm' f μ
  证明: Kernel.iIndepFun.of_subsingleton

Depends on / 依赖: Kernel, Kernel.iIndepFun.of_subsingleton, iIndepFun, of_subsingleton
-/
lemma iCondIndepFun.of_subsingleton [Subsingleton ι] : iCondIndepFun m' hm' f μ :=
  Kernel.iIndepFun.of_subsingleton

/--
theorem `iCondIndepFun.condIndepFun_finset` / 定理 `iCondIndepFun.condIndepFun_finset`

English:
theorem iCondIndepFun.condIndepFun_finset
  statement: {β : ι -> Type*}
  proof: Kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas

中文:
定理 iCondIndepFun.condIndepFun_finset
  结论: {β : ι -> 类型}
  证明: Kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_finset, hf_Indep, hf_meas, iIndepFun, indepFun_finset
-/
theorem iCondIndepFun.condIndepFun_finset {β : ι -> Type*}
    {m : forall i, MeasurableSpace (β i)} {f : forall i, Ω -> β i} (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iCondIndepFun m' hm' f μ) (hf_meas : forall i, Measurable (f i)) :
    CondIndepFun m' hm' (fun a (i : S) => f i a) (fun a (i : T) => f i a) μ :=
  Kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas

/--
theorem `iCondIndepFun.condIndepFun_prodMk` / 定理 `iCondIndepFun.condIndepFun_prodMk`

English:
theorem iCondIndepFun.condIndepFun_prodMk
  statement: {β : ι -> Type*}
  proof: Kernel.iIndepFun.indepFun_prodMk hf_Indep hf_meas i j k hik hjk

中文:
定理 iCondIndepFun.condIndepFun_prodMk
  结论: {β : ι -> 类型}
  证明: Kernel.iIndepFun.indepFun_prodMk hf_Indep hf_meas i j k hik hjk

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_prodMk, hf_Indep, hf_meas, iIndepFun, indepFun_prodMk
-/
theorem iCondIndepFun.condIndepFun_prodMk {β : ι -> Type*}
    {m : forall i, MeasurableSpace (β i)} {f : forall i, Ω -> β i} (hf_Indep : iCondIndepFun m' hm' f μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    CondIndepFun m' hm' (fun a => (f i a, f j a)) (f k) μ :=
  Kernel.iIndepFun.indepFun_prodMk hf_Indep hf_meas i j k hik hjk

open Finset in
/--
lemma `iCondIndepFun.condIndepFun_prodMk_prodMk` / 引理 `iCondIndepFun.condIndepFun_prodMk_prodMk`

English:
lemma iCondIndepFun.condIndepFun_prodMk_prodMk
  statement: (h_indep : iCondIndepFun m' hm' f μ)
  proof: by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (h_indep.indepFun_finset {i, j} {k, l} (by aesop) hf).comp (hg i j) (hg k l

中文:
引理 iCondIndepFun.condIndepFun_prodMk_prodMk
  结论: (h_indep : iCondIndepFun m' hm' f μ)
  证明: by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (h_indep.indepFun_finset {i, j} {k, l} (by aesop) hf).comp (hg i j) (hg k l

Depends on / 依赖: Finset, Measurable, classical, fun_prop, h_indep, h_indep.indepFun_finset, indepFun_finset, mem_insert_of_mem, mem_insert_self, mem_singleton_self
-/
lemma iCondIndepFun.condIndepFun_prodMk_prodMk (h_indep : iCondIndepFun m' hm' f μ)
    (hf : forall i, Measurable (f i))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    CondIndepFun m' hm' (fun a => (f i a, f j a)) (fun a => (f k a, f l a)) μ := by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (h_indep.indepFun_finset {i, j} {k, l} (by aesop) hf).comp (hg i j) (hg k l)

end iCondIndepFun

section Mul
variable {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι -> Ω -> β}

@[to_additive]
/--
lemma `iCondIndepFun.indepFun_mul_left` / 引理 `iCondIndepFun.indepFun_mul_left`

English:
lemma iCondIndepFun.indepFun_mul_left
  statement: (hf_indep : iCondIndepFun m' hm' f μ)
  proof: Kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk

@[to_additive]

中文:
引理 iCondIndepFun.indepFun_mul_left
  结论: (hf_indep : iCondIndepFun m' hm' f μ)
  证明: Kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_mul_left, hf_indep, hf_meas, iIndepFun, indepFun_mul_left
-/
lemma iCondIndepFun.indepFun_mul_left (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    CondIndepFun m' hm' (f i * f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk

@[to_additive]
/--
lemma `iCondIndepFun.indepFun_mul_right` / 引理 `iCondIndepFun.indepFun_mul_right`

English:
lemma iCondIndepFun.indepFun_mul_right
  statement: (hf_indep : iCondIndepFun m' hm' f μ)
  proof: Kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]

中文:
引理 iCondIndepFun.indepFun_mul_right
  结论: (hf_indep : iCondIndepFun m' hm' f μ)
  证明: Kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_mul_right, hf_indep, hf_meas, iIndepFun, indepFun_mul_right
-/
lemma iCondIndepFun.indepFun_mul_right (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hij : i != j) (hik : i != k) :
    CondIndepFun m' hm' (f i) (f j * f k) μ :=
  Kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]
/--
lemma `iCondIndepFun.indepFun_mul_mul` / 引理 `iCondIndepFun.indepFun_mul_mul`

English:
lemma iCondIndepFun.indepFun_mul_mul
  statement: (hf_indep : iCondIndepFun m' hm' f μ)
  proof: Kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

中文:
引理 iCondIndepFun.indepFun_mul_mul
  结论: (hf_indep : iCondIndepFun m' hm' f μ)
  证明: Kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_mul_mul, hf_indep, hf_meas, iIndepFun, indepFun_mul_mul
-/
lemma iCondIndepFun.indepFun_mul_mul (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : forall i, Measurable (f i))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    CondIndepFun m' hm' (f i * f j) (f k * f l) μ :=
  Kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

end Mul

section Div
variable {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι -> Ω -> β}

@[to_additive]
/--
lemma `iCondIndepFun.indepFun_div_left` / 引理 `iCondIndepFun.indepFun_div_left`

English:
lemma iCondIndepFun.indepFun_div_left
  statement: (hf_indep : iCondIndepFun m' hm' f μ)
  proof: Kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]

中文:
引理 iCondIndepFun.indepFun_div_left
  结论: (hf_indep : iCondIndepFun m' hm' f μ)
  证明: Kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_div_left, hf_indep, hf_meas, iIndepFun, indepFun_div_left
-/
lemma iCondIndepFun.indepFun_div_left (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    CondIndepFun m' hm' (f i / f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]
/--
lemma `iCondIndepFun.indepFun_div_right` / 引理 `iCondIndepFun.indepFun_div_right`

English:
lemma iCondIndepFun.indepFun_div_right
  statement: (hf_indep : iCondIndepFun m' hm' f μ)
  proof: Kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]

中文:
引理 iCondIndepFun.indepFun_div_right
  结论: (hf_indep : iCondIndepFun m' hm' f μ)
  证明: Kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_div_right, hf_indep, hf_meas, iIndepFun, indepFun_div_right
-/
lemma iCondIndepFun.indepFun_div_right (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hij : i != j) (hik : i != k) :
    CondIndepFun m' hm' (f i) (f j / f k) μ :=
  Kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]
/--
lemma `iCondIndepFun.indepFun_div_div` / 引理 `iCondIndepFun.indepFun_div_div`

English:
lemma iCondIndepFun.indepFun_div_div
  statement: (hf_indep : iCondIndepFun m' hm' f μ)
  proof: Kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

中文:
引理 iCondIndepFun.indepFun_div_div
  结论: (hf_indep : iCondIndepFun m' hm' f μ)
  证明: Kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_div_div, hf_indep, hf_meas, iIndepFun, indepFun_div_div
-/
lemma iCondIndepFun.indepFun_div_div (hf_indep : iCondIndepFun m' hm' f μ)
    (hf_meas : forall i, Measurable (f i))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    CondIndepFun m' hm' (f i / f j) (f k / f l) μ :=
  Kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

end Div

section CommMonoid
variable {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι -> Ω -> β}

@[to_additive]
/--
theorem `iCondIndepFun.condIndepFun_finsetProd_of_notMem` / 定理 `iCondIndepFun.condIndepFun_finsetProd_of_notMem`

English:
theorem iCondIndepFun.condIndepFun_finsetProd_of_notMem
  proof: Kernel.iIndepFun.indepFun_finsetProd_of_notMem hf_Indep hf_meas hi

@[deprecated (since := "2026-04-08")]
alias iCondIndepFun.condIndepFun_finset_sum_of_notMem :=
  iCondIndepFun.condIndepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iCondIndepFun.condInd

中文:
定理 iCondIndepFun.condIndepFun_finsetProd_of_notMem
  证明: Kernel.iIndepFun.indepFun_finsetProd_of_notMem hf_Indep hf_meas hi

@[deprecated (since := "2026-04-08")]
alias iCondIndepFun.condIndepFun_finset_sum_of_notMem :=
  iCondIndepFun.condIndepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iCondIndepFun.condInd

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_finsetProd_of_notMem, hf_Indep, hf_meas, iIndepFun, indepFun_finsetProd_of_notMem
-/
theorem iCondIndepFun.condIndepFun_finsetProd_of_notMem
    (hf_Indep : iCondIndepFun m' hm' f μ) (hf_meas : forall i, Measurable (f i))
    {s : Finset ι} {i : ι} (hi : i ∉ s) :
    CondIndepFun m' hm' (∏ j in s, f j) (f i) μ :=
  Kernel.iIndepFun.indepFun_finsetProd_of_notMem hf_Indep hf_meas hi

@[deprecated (since := "2026-04-08")]
alias iCondIndepFun.condIndepFun_finset_sum_of_notMem :=
  iCondIndepFun.condIndepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iCondIndepFun.condIndepFun_finset_prod_of_notMem :=
  iCondIndepFun.condIndepFun_finsetProd_of_notMem

@[to_additive]
/--
theorem `iCondIndepFun.condIndepFun_prod_range_succ` / 定理 `iCondIndepFun.condIndepFun_prod_range_succ`

English:
theorem iCondIndepFun.condIndepFun_prod_range_succ
  statement: {f : Nat -> Ω -> β}
  proof: Kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n

中文:
定理 iCondIndepFun.condIndepFun_prod_range_succ
  结论: {f : 自然数 -> Ω -> β}
  证明: Kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_prod_range_succ, hf_Indep, hf_meas, iIndepFun, indepFun_prod_range_succ
-/
theorem iCondIndepFun.condIndepFun_prod_range_succ {f : Nat -> Ω -> β}
    (hf_Indep : iCondIndepFun m' hm' f μ) (hf_meas : forall i, Measurable (f i)) (n : Nat) :
    CondIndepFun m' hm' (∏ j in Finset.range n, f j) (f n) μ :=
  Kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n

end CommMonoid

/--
theorem `iCondIndepSet.iCondIndepFun_indicator` / 定理 `iCondIndepSet.iCondIndepFun_indicator`

English:
theorem iCondIndepSet.iCondIndepFun_indicator
  statement: [Zero β] [One β] {m : MeasurableSpace β}
  proof: Kernel.iIndepSet.iIndepFun_indicator hs

中文:
定理 iCondIndepSet.iCondIndepFun_indicator
  结论: [零 β] [幺 β] {m : 可测空间 β}
  证明: Kernel.iIndepSet.iIndepFun_indicator hs

Depends on / 依赖: Kernel, Kernel.iIndepSet.iIndepFun_indicator, iIndepFun_indicator, iIndepSet
-/
theorem iCondIndepSet.iCondIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β}
    {s : ι -> Set Ω} (hs : iCondIndepSet m' hm' s μ) :
    iCondIndepFun m' hm' (fun n => (s n).indicator fun _ω => (1 : β)) μ :=
  Kernel.iIndepSet.iIndepFun_indicator hs

end CondIndepFun

end ProbabilityTheory
