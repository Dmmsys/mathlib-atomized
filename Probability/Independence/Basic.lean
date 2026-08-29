/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → MeasurableSpace Ω` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `MeasurableSpace.comap f m`.

## Main statements

* `iIndepSets.iIndep`: if π-systems are independent as sets of sets, then the
  measurable space structures they generate are independent.
* `IndepSets.indep`: variant with two π-systems.

## Notation

* `X ⟂ᵢ[μ] Y` for `IndepFun X Y μ`, independence of two random variables.
* `X ⟂ᵢ Y` for `IndepFun X Y volume`.

These notations are scoped in the `ProbabilityTheory` namespace.

## Implementation notes

The definitions of independence in this file are a particular case of independence with respect to a
kernel and a measure, as defined in the file `Kernel.lean`.

We provide four definitions of independence:
* `iIndepSets`: independence of a family of sets of sets `pi : ι → Set (Set Ω)`. This is meant to
  be used with π-systems.
* `iIndep`: independence of a family of measurable space structures `m : ι → MeasurableSpace Ω`,
* `iIndepSet`: independence of a family of sets `s : ι → Set Ω`,
* `iIndepFun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), MeasurableSpace (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without the starting `i`, for example `IndepFun` is the version of `iIndepFun`
for two functions.

The definition of independence for `iIndepSets` uses finite sets (`Finset`). See
`ProbabilityTheory.Kernel.iIndepSets`. An alternative and equivalent way of defining independence
would have been to use countable sets.

Most of the definitions and lemmas in this file list all variables instead of using the `variable`
keyword at the beginning of a section, for example
`lemma Indep.symm {Ω} {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {μ : measure Ω} ...` .
This is intentional, to be able to control the order of the `MeasurableSpace` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`{_mΩ : MeasurableSpace Ω}`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
  Part A, Chapter 4.
-/

@[expose] public section

assert_not_exists MeasureTheory.Integrable

open MeasureTheory MeasurableSpace Set

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι β γ : Type*} {κ : ι -> Type*}

section Definitions

/--
Definition of `iIndepSets` / `iIndepSets` 的定义

English:
definition iIndepSets
  signature: {_mΩ : MeasurableSpace Ω}
  body: Kernel.iIndepSets π (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

中文:
定义 iIndepSets
  签名: {_mΩ : 可测空间 Ω}
  定义体: Kernel.iIndepSets π (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

Depends on / 依赖: Kernel, Kernel.const, Kernel.iIndepSets, Measure, Measure.dirac, iIndepSets, volume_tac
-/
def iIndepSets {_mΩ : MeasurableSpace Ω}
    (π : ι -> Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepSets π (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/--
Definition of `IndepSets` / `IndepSets` 的定义

English:
definition IndepSets
  signature: {_mΩ : MeasurableSpace Ω}
  body: Kernel.IndepSets s1 s2 (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

中文:
定义 IndepSets
  签名: {_mΩ : 可测空间 Ω}
  定义体: Kernel.IndepSets s1 s2 (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets, Kernel.const, Measure, Measure.dirac, volume_tac
-/
def IndepSets {_mΩ : MeasurableSpace Ω}
    (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepSets s1 s2 (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/--
Definition of `iIndep` / `iIndep` 的定义

English:
definition iIndep
  signature: (m : ι -> MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac)
  body: Kernel.iIndep m (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

中文:
定义 iIndep
  签名: (m : ι -> 可测空间 Ω) {_mΩ : 可测空间 Ω} (μ : 测度 Ω := by volume_tac)
  定义体: Kernel.iIndep m (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

Depends on / 依赖: Kernel, Kernel.const, Kernel.iIndep, Measure, Measure.dirac, iIndep, volume_tac
-/
def iIndep (m : ι -> MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) :
    Prop :=
  Kernel.iIndep m (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/--
Definition of `Indep` / `Indep` 的定义

English:
definition Indep
  signature: (m₁ m₂ : MeasurableSpace Ω)
  body: Kernel.Indep m₁ m₂ (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

中文:
定义 Indep
  签名: (m₁ m₂ : 可测空间 Ω)
  定义体: Kernel.Indep m₁ m₂ (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

Depends on / 依赖: Kernel, Kernel.Indep, Kernel.const, Measure, Measure.dirac, volume_tac
-/
def Indep (m₁ m₂ : MeasurableSpace Ω)
    {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.Indep m₁ m₂ (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/--
Definition of `iIndepSet` / `iIndepSet` 的定义

English:
definition iIndepSet
  signature: {_mΩ : MeasurableSpace Ω} (s : ι -> Set Ω) (μ : Measure Ω := by volume_tac)
  body: Kernel.iIndepSet s (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

中文:
定义 iIndepSet
  签名: {_mΩ : 可测空间 Ω} (s : ι -> 集合 Ω) (μ : 测度 Ω := by volume_tac)
  定义体: Kernel.iIndepSet s (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

Depends on / 依赖: Kernel, Kernel.const, Kernel.iIndepSet, Measure, Measure.dirac, iIndepSet, volume_tac
-/
def iIndepSet {_mΩ : MeasurableSpace Ω} (s : ι -> Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepSet s (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/--
Definition of `IndepSet` / `IndepSet` 的定义

English:
definition IndepSet
  signature: {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (μ : Measure Ω := by volume_tac)
  body: Kernel.IndepSet s t (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

中文:
定义 IndepSet
  签名: {_mΩ : 可测空间 Ω} (s t : 集合 Ω) (μ : 测度 Ω := by volume_tac)
  定义体: Kernel.IndepSet s t (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

Depends on / 依赖: IndepSet, Kernel, Kernel.IndepSet, Kernel.const, Measure, Measure.dirac, volume_tac
-/
def IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepSet s t (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/--
Definition of `iIndepFun` / `iIndepFun` 的定义

English:
definition iIndepFun
  signature: {_mΩ : MeasurableSpace Ω} {β : ι -> Type*} [m : forall x : ι, MeasurableSpace (β x)]
  body: Kernel.iIndepFun f (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

中文:
定义 iIndepFun
  签名: {_mΩ : 可测空间 Ω} {β : ι -> 类型} [m : 对任意 x : ι, 可测空间 (β x)]
  定义体: Kernel.iIndepFun f (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

Depends on / 依赖: Kernel, Kernel.const, Kernel.iIndepFun, Measure, Measure.dirac, iIndepFun, volume_tac
-/
def iIndepFun {_mΩ : MeasurableSpace Ω} {β : ι -> Type*} [m : forall x : ι, MeasurableSpace (β x)]
    (f : forall x : ι, Ω -> β x) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.iIndepFun f (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

/--
Definition of `IndepFun` / `IndepFun` 的定义

English:
definition IndepFun
  signature: {β γ} {_mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSpace γ]
  body: Kernel.IndepFun f g (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

中文:
定义 IndepFun
  签名: {β γ} {_mΩ : 可测空间 Ω} [可测空间 β] [可测空间 γ]
  定义体: Kernel.IndepFun f g (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

Depends on / 依赖: IndepFun, Kernel, Kernel.IndepFun, Kernel.const, Measure, Measure.dirac, volume_tac
-/
def IndepFun {β γ} {_mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω -> β) (g : Ω -> γ) (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.IndepFun f g (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)

end Definitions

@[inherit_doc ProbabilityTheory.IndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" μ "] " Y:50 => ProbabilityTheory.IndepFun X Y μ

@[inherit_doc ProbabilityTheory.IndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ " Y:50 => ProbabilityTheory.IndepFun X Y volume

section Definition_lemmas
variable {π : ι -> Set (Set Ω)} {m : ι -> MeasurableSpace Ω} {_ : MeasurableSpace Ω} {μ : Measure Ω}
  {S : Finset ι} {s : ι -> Set Ω} {ι' : Type*} {g : ι' -> ι}

/--
lemma `iIndepSets_iff` / 引理 `iIndepSets_iff`

English:
lemma iIndepSets_iff
  given: (π : ι -> Set (Set Ω)) (μ : Measure Ω)
  proof: by
  simp only [iIndepSets, Kernel.iIndepSets, ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply]

中文:
引理 iIndepSets_iff
  条件: (π : ι -> 集合 (集合 Ω)) (μ : 测度 Ω)
  证明: by
  simp only [iIndepSets, Kernel.iIndepSets, ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply]

Depends on / 依赖: Filter, Filter.eventually_pure, Kernel, Kernel.const_apply, Kernel.iIndepSets, ae_dirac_eq, const_apply, eventually_pure, iIndepSets
-/
lemma iIndepSets_iff (π : ι -> Set (Set Ω)) (μ : Measure Ω) :
    iIndepSets π μ ↔ forall (s : Finset ι) {f : ι -> Set Ω} (_H : forall i, i in s -> f i in π i),
      μ (⋂ i in s, f i) = ∏ i in s, μ (f i) := by
  simp only [iIndepSets, Kernel.iIndepSets, ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply]

/--
lemma `iIndepSets.meas_biInter` / 引理 `iIndepSets.meas_biInter`

English:
lemma iIndepSets.meas_biInter
  statement: (h : iIndepSets π μ) (s : Finset ι) {f : ι -> Set Ω}
  proof: (iIndepSets_iff _ _).1 h s hf

中文:
引理 iIndepSets.meas_bi整数er
  结论: (h : iIndepSets π μ) (s : 有限集 ι) {f : ι -> 集合 Ω}
  证明: (iIndepSets_iff _ _).1 h s hf

Depends on / 依赖: iIndepSets_iff
-/
lemma iIndepSets.meas_biInter (h : iIndepSets π μ) (s : Finset ι) {f : ι -> Set Ω}
    (hf : forall i, i in s -> f i in π i) : μ (⋂ i in s, f i) = ∏ i in s, μ (f i) :=
  (iIndepSets_iff _ _).1 h s hf

/--
lemma `iIndepSets.isProbabilityMeasure` / 引理 `iIndepSets.isProbabilityMeasure`

English:
lemma iIndepSets.isProbabilityMeasure
  given: (h : iIndepSets π μ)
  statement: IsProbabilityMeasure μ
  proof: ⟨by simpa using h ∅ (f := fun _ => univ)⟩

中文:
引理 iIndepSets.isProbabilityMeasure
  条件: (h : iIndepSets π μ)
  结论: 是概率测度 μ
  证明: ⟨by simpa using h ∅ (f := fun _ => univ)⟩
-/
lemma iIndepSets.isProbabilityMeasure (h : iIndepSets π μ) : IsProbabilityMeasure μ :=
  ⟨by simpa using h ∅ (f := fun _ => univ)⟩

/--
lemma `iIndepSets.meas_iInter` / 引理 `iIndepSets.meas_iInter`

English:
lemma iIndepSets.meas_iInter
  given: [Fintype ι] (h : iIndepSets π μ) (hs : forall i, s i in π i)
  proof: by simp [← h.meas_biInter _ fun _i _ => hs _]

中文:
引理 iIndepSets.meas_i整数er
  条件: [有限类型 ι] (h : iIndepSets π μ) (hs : 对任意 i, s i in π i)
  证明: by simp [← h.meas_biInter _ fun _i _ => hs _]

Depends on / 依赖: h.meas_biInter, meas_biInter
-/
lemma iIndepSets.meas_iInter [Fintype ι] (h : iIndepSets π μ) (hs : forall i, s i in π i) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := by simp [← h.meas_biInter _ fun _i _ => hs _]

/--
lemma `IndepSets_iff` / 引理 `IndepSets_iff`

English:
lemma IndepSets_iff
  given: (s1 s2 : Set (Set Ω)) (μ : Measure Ω)
  proof: by
  simp only [IndepSets, Kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply]

中文:
引理 IndepSets_iff
  条件: (s1 s2 : 集合 (集合 Ω)) (μ : 测度 Ω)
  证明: by
  simp only [IndepSets, Kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply]

Depends on / 依赖: Filter, Filter.eventually_pure, IndepSets, Kernel, Kernel.IndepSets, Kernel.const_apply, ae_dirac_eq, const_apply, eventually_pure
-/
lemma IndepSets_iff (s1 s2 : Set (Set Ω)) (μ : Measure Ω) :
    IndepSets s1 s2 μ ↔ forall t1 t2 : Set Ω, t1 in s1 -> t2 in s2 -> (μ (t1 inter t2) = μ t1 * μ t2) := by
  simp only [IndepSets, Kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply]

/--
lemma `iIndep_iff_iIndepSets` / 引理 `iIndep_iff_iIndepSets`

English:
lemma iIndep_iff_iIndepSets
  given: (m : ι -> MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω)
  proof: by
  simp only [iIndep, iIndepSets, Kernel.iIndep]

中文:
引理 iIndep_iff_iIndepSets
  条件: (m : ι -> 可测空间 Ω) {_mΩ : 可测空间 Ω} (μ : 测度 Ω)
  证明: by
  simp only [iIndep, iIndepSets, Kernel.iIndep]

Depends on / 依赖: Kernel, Kernel.iIndep, iIndep, iIndepSets
-/
lemma iIndep_iff_iIndepSets (m : ι -> MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    iIndep m μ ↔ iIndepSets (fun x => {s | MeasurableSet[m x] s}) μ := by
  simp only [iIndep, iIndepSets, Kernel.iIndep]

/--
lemma `iIndep.iIndepSets'` / 引理 `iIndep.iIndepSets'`

English:
lemma iIndep.iIndepSets'
  statement: {m : ι -> MeasurableSpace Ω}
  proof: (iIndep_iff_iIndepSets _ _).1 hμ

中文:
引理 iIndep.iIndepSets'
  结论: {m : ι -> 可测空间 Ω}
  证明: (iIndep_iff_iIndepSets _ _).1 hμ

Depends on / 依赖: iIndep_iff_iIndepSets
-/
lemma iIndep.iIndepSets' {m : ι -> MeasurableSpace Ω}
    {_ : MeasurableSpace Ω} {μ : Measure Ω} (hμ : iIndep m μ) :
    iIndepSets (fun x => {s | MeasurableSet[m x] s}) μ := (iIndep_iff_iIndepSets _ _).1 hμ

/--
lemma `iIndep.isProbabilityMeasure` / 引理 `iIndep.isProbabilityMeasure`

English:
lemma iIndep.isProbabilityMeasure
  given: (h : iIndep m μ)
  statement: IsProbabilityMeasure μ
  proof: h.iIndepSets'.isProbabilityMeasure

中文:
引理 iIndep.isProbabilityMeasure
  条件: (h : iIndep m μ)
  结论: 是概率测度 μ
  证明: h.iIndepSets'.isProbabilityMeasure

Depends on / 依赖: h.iIndepSets, iIndepSets, isProbabilityMeasure
-/
lemma iIndep.isProbabilityMeasure (h : iIndep m μ) : IsProbabilityMeasure μ :=
  h.iIndepSets'.isProbabilityMeasure

/--
lemma `iIndep_iff` / 引理 `iIndep_iff`

English:
lemma iIndep_iff
  given: (m : ι -> MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω)
  proof: by
  simp only [iIndep_iff_iIndepSets, iIndepSets_iff]; rfl

中文:
引理 iIndep_iff
  条件: (m : ι -> 可测空间 Ω) {_mΩ : 可测空间 Ω} (μ : 测度 Ω)
  证明: by
  simp only [iIndep_iff_iIndepSets, iIndepSets_iff]; rfl

Depends on / 依赖: iIndepSets_iff, iIndep_iff_iIndepSets
-/
lemma iIndep_iff (m : ι -> MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    iIndep m μ ↔ forall (s : Finset ι) {f : ι -> Set Ω} (_H : forall i, i in s -> MeasurableSet[m i] (f i)),
      μ (⋂ i in s, f i) = ∏ i in s, μ (f i) := by
  simp only [iIndep_iff_iIndepSets, iIndepSets_iff]; rfl

/--
lemma `iIndep.meas_biInter` / 引理 `iIndep.meas_biInter`

English:
lemma iIndep.meas_biInter
  given: (hμ : iIndep m μ) (hs : forall i, i in S -> MeasurableSet[m i] (s i))
  proof: (iIndep_iff _ _).1 hμ _ hs

中文:
引理 iIndep.meas_bi整数er
  条件: (hμ : iIndep m μ) (hs : 对任意 i, i in S -> 可测集[m i] (s i))
  证明: (iIndep_iff _ _).1 hμ _ hs

Depends on / 依赖: iIndep_iff
-/
lemma iIndep.meas_biInter (hμ : iIndep m μ) (hs : forall i, i in S -> MeasurableSet[m i] (s i)) :
    μ (⋂ i in S, s i) = ∏ i in S, μ (s i) := (iIndep_iff _ _).1 hμ _ hs

/--
lemma `iIndep.meas_iInter` / 引理 `iIndep.meas_iInter`

English:
lemma iIndep.meas_iInter
  given: [Fintype ι] (hμ : iIndep m μ) (hs : forall i, MeasurableSet[m i] (s i))
  proof: by simp [← hμ.meas_biInter fun _ _ => hs _]

中文:
引理 iIndep.meas_i整数er
  条件: [有限类型 ι] (hμ : iIndep m μ) (hs : 对任意 i, 可测集[m i] (s i))
  证明: by simp [← hμ.meas_biInter fun _ _ => hs _]

Depends on / 依赖: meas_biInter
-/
lemma iIndep.meas_iInter [Fintype ι] (hμ : iIndep m μ) (hs : forall i, MeasurableSet[m i] (s i)) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := by simp [← hμ.meas_biInter fun _ _ => hs _]

/--
lemma `Indep_iff_IndepSets` / 引理 `Indep_iff_IndepSets`

English:
lemma Indep_iff_IndepSets
  given: (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω)
  proof: by
  simp only [Indep, IndepSets, Kernel.Indep]

中文:
引理 Indep_iff_IndepSets
  条件: (m₁ m₂ : 可测空间 Ω) {_mΩ : 可测空间 Ω} (μ : 测度 Ω)
  证明: by
  simp only [Indep, IndepSets, Kernel.Indep]

Depends on / 依赖: IndepSets, Kernel, Kernel.Indep
-/
lemma Indep_iff_IndepSets (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    Indep m₁ m₂ μ ↔ IndepSets {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s} μ := by
  simp only [Indep, IndepSets, Kernel.Indep]

/--
lemma `Indep_iff` / 引理 `Indep_iff`

English:
lemma Indep_iff
  given: (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω)
  proof: by
  rw [Indep_iff_IndepSets]; rw [IndepSets_iff]; rfl

中文:
引理 Indep_iff
  条件: (m₁ m₂ : 可测空间 Ω) {_mΩ : 可测空间 Ω} (μ : 测度 Ω)
  证明: by
  rw [Indep_iff_IndepSets]; rw [IndepSets_iff]; rfl

Depends on / 依赖: IndepSets_iff, Indep_iff_IndepSets
-/
lemma Indep_iff (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    Indep m₁ m₂ μ
      ↔ forall t1 t2, MeasurableSet[m₁] t1 -> MeasurableSet[m₂] t2 -> μ (t1 inter t2) = μ t1 * μ t2 := by
  rw [Indep_iff_IndepSets]; rw [IndepSets_iff]; rfl

/--
lemma `iIndepSet_iff_iIndep` / 引理 `iIndepSet_iff_iIndep`

English:
lemma iIndepSet_iff_iIndep
  given: (s : ι -> Set Ω) (μ : Measure Ω)
  proof: by
  simp only [iIndepSet, iIndep, Kernel.iIndepSet]

中文:
引理 iIndepSet_iff_iIndep
  条件: (s : ι -> 集合 Ω) (μ : 测度 Ω)
  证明: by
  simp only [iIndepSet, iIndep, Kernel.iIndepSet]

Depends on / 依赖: Kernel, Kernel.iIndepSet, iIndep, iIndepSet
-/
lemma iIndepSet_iff_iIndep (s : ι -> Set Ω) (μ : Measure Ω) :
    iIndepSet s μ ↔ iIndep (fun i => generateFrom {s i}) μ := by
  simp only [iIndepSet, iIndep, Kernel.iIndepSet]

/--
lemma `iIndepSet.isProbabilityMeasure` / 引理 `iIndepSet.isProbabilityMeasure`

English:
lemma iIndepSet.isProbabilityMeasure
  given: (h : iIndepSet s μ)
  statement: IsProbabilityMeasure μ
  proof: ((iIndepSet_iff_iIndep _ _).1 h).isProbabilityMeasure

中文:
引理 iIndepSet.isProbabilityMeasure
  条件: (h : iIndepSet s μ)
  结论: 是概率测度 μ
  证明: ((iIndepSet_iff_iIndep _ _).1 h).isProbabilityMeasure

Depends on / 依赖: iIndepSet_iff_iIndep, isProbabilityMeasure
-/
lemma iIndepSet.isProbabilityMeasure (h : iIndepSet s μ) : IsProbabilityMeasure μ :=
  ((iIndepSet_iff_iIndep _ _).1 h).isProbabilityMeasure

/--
lemma `iIndepSet_iff` / 引理 `iIndepSet_iff`

English:
lemma iIndepSet_iff
  given: (s : ι -> Set Ω) (μ : Measure Ω)
  proof: by
  simp only [iIndepSet_iff_iIndep, iIndep_iff]

中文:
引理 iIndepSet_iff
  条件: (s : ι -> 集合 Ω) (μ : 测度 Ω)
  证明: by
  simp only [iIndepSet_iff_iIndep, iIndep_iff]

Depends on / 依赖: iIndepSet_iff_iIndep, iIndep_iff
-/
lemma iIndepSet_iff (s : ι -> Set Ω) (μ : Measure Ω) :
    iIndepSet s μ ↔ forall (s' : Finset ι) {f : ι -> Set Ω}
      (_H : forall i, i in s' -> MeasurableSet[generateFrom {s i}] (f i)),
      μ (⋂ i in s', f i) = ∏ i in s', μ (f i) := by
  simp only [iIndepSet_iff_iIndep, iIndep_iff]

/--
lemma `IndepSet_iff_Indep` / 引理 `IndepSet_iff_Indep`

English:
lemma IndepSet_iff_Indep
  given: (s t : Set Ω) (μ : Measure Ω)
  proof: by
  simp only [IndepSet, Indep, Kernel.IndepSet]

中文:
引理 IndepSet_iff_Indep
  条件: (s t : 集合 Ω) (μ : 测度 Ω)
  证明: by
  simp only [IndepSet, Indep, Kernel.IndepSet]

Depends on / 依赖: IndepSet, Kernel, Kernel.IndepSet
-/
lemma IndepSet_iff_Indep (s t : Set Ω) (μ : Measure Ω) :
    IndepSet s t μ ↔ Indep (generateFrom {s}) (generateFrom {t}) μ := by
  simp only [IndepSet, Indep, Kernel.IndepSet]

/--
lemma `IndepSet_iff` / 引理 `IndepSet_iff`

English:
lemma IndepSet_iff
  given: (s t : Set Ω) (μ : Measure Ω)
  proof: by
  simp only [IndepSet_iff_Indep, Indep_iff]

中文:
引理 IndepSet_iff
  条件: (s t : 集合 Ω) (μ : 测度 Ω)
  证明: by
  simp only [IndepSet_iff_Indep, Indep_iff]

Depends on / 依赖: IndepSet_iff_Indep, Indep_iff
-/
lemma IndepSet_iff (s t : Set Ω) (μ : Measure Ω) :
    IndepSet s t μ ↔ forall t1 t2, MeasurableSet[generateFrom {s}] t1
      -> MeasurableSet[generateFrom {t}] t2 -> μ (t1 inter t2) = μ t1 * μ t2 := by
  simp only [IndepSet_iff_Indep, Indep_iff]

/--
lemma `iIndepFun_iff_iIndep` / 引理 `iIndepFun_iff_iIndep`

English:
lemma iIndepFun_iff_iIndep
  statement: {β : ι -> Type*}
  proof: by
  simp only [iIndepFun, iIndep, Kernel.iIndepFun]

@[nontriviality, simp]

中文:
引理 iIndepFun_iff_iIndep
  结论: {β : ι -> 类型}
  证明: by
  simp only [iIndepFun, iIndep, Kernel.iIndepFun]

@[nontriviality, simp]

Depends on / 依赖: Kernel, Kernel.iIndepFun, iIndep, iIndepFun
-/
lemma iIndepFun_iff_iIndep {β : ι -> Type*}
    (m : forall x : ι, MeasurableSpace (β x)) (f : forall x : ι, Ω -> β x) (μ : Measure Ω) :
    iIndepFun f μ ↔ iIndep (fun x => (m x).comap (f x)) μ := by
  simp only [iIndepFun, iIndep, Kernel.iIndepFun]

@[nontriviality, simp]
/--
lemma `iIndepSets.of_subsingleton` / 引理 `iIndepSets.of_subsingleton`

English:
lemma iIndepSets.of_subsingleton
  given: [Subsingleton ι] {m : ι -> Set (Set Ω)} [IsProbabilityMeasure μ]
  proof: Kernel.iIndepSets.of_subsingleton

@[nontriviality, simp]

中文:
引理 iIndepSets.of_subsingleton
  条件: [子单例 ι] {m : ι -> 集合 (集合 Ω)} [是概率测度 μ]
  证明: Kernel.iIndepSets.of_subsingleton

@[nontriviality, simp]

Depends on / 依赖: Kernel, Kernel.iIndepSets.of_subsingleton, iIndepSets, of_subsingleton
-/
lemma iIndepSets.of_subsingleton [Subsingleton ι] {m : ι -> Set (Set Ω)} [IsProbabilityMeasure μ] :
    iIndepSets m μ := Kernel.iIndepSets.of_subsingleton

@[nontriviality, simp]
/--
lemma `iIndep.of_subsingleton` / 引理 `iIndep.of_subsingleton`

English:
lemma iIndep.of_subsingleton
  given: [Subsingleton ι] {m : ι -> MeasurableSpace Ω} [IsProbabilityMeasure μ]
  proof: Kernel.iIndep.of_subsingleton

@[nontriviality, simp]

中文:
引理 iIndep.of_subsingleton
  条件: [子单例 ι] {m : ι -> 可测空间 Ω} [是概率测度 μ]
  证明: Kernel.iIndep.of_subsingleton

@[nontriviality, simp]

Depends on / 依赖: Kernel, Kernel.iIndep.of_subsingleton, iIndep, of_subsingleton
-/
lemma iIndep.of_subsingleton [Subsingleton ι] {m : ι -> MeasurableSpace Ω} [IsProbabilityMeasure μ] :
    iIndep m μ := Kernel.iIndep.of_subsingleton

@[nontriviality, simp]
/--
lemma `iIndepFun.of_subsingleton` / 引理 `iIndepFun.of_subsingleton`

English:
lemma iIndepFun.of_subsingleton
  statement: [Subsingleton ι] {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)}
  proof: Kernel.iIndepFun.of_subsingleton

中文:
引理 iIndepFun.of_subsingleton
  结论: [子单例 ι] {β : ι -> 类型} {m : 对任意 i, 可测空间 (β i)}
  证明: Kernel.iIndepFun.of_subsingleton

Depends on / 依赖: Kernel, Kernel.iIndepFun.of_subsingleton, iIndepFun, of_subsingleton
-/
lemma iIndepFun.of_subsingleton [Subsingleton ι] {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)}
    {f : forall i, Ω -> β i} [IsProbabilityMeasure μ] : iIndepFun f μ :=
  Kernel.iIndepFun.of_subsingleton

/--
lemma `iIndepFun.iIndep` / 引理 `iIndepFun.iIndep`

English:
lemma iIndepFun.iIndep
  statement: {m : forall i, MeasurableSpace (κ i)} {f : forall x : ι, Ω -> κ x}
  proof: hf

中文:
引理 iIndepFun.iIndep
  结论: {m : 对任意 i, 可测空间 (κ i)} {f : 对任意 x : ι, Ω -> κ x}
  证明: hf

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.injective, IsIntegrallyClosed, IsIntegrallyClosed.isIntegral_iff.mp, IsIntegrallyClosedIn, UniqueFactorizationMonoid, UniqueFactorizationMonoid.instIsIntegrallyClosed, hp.coeff, injective, instIsIntegrallyClosed, isIntegral_iff, isIntegrallyClosedIn_iff, isIntegrallyClosedIn_iff.mpr, lifts_iff_coeff_lifts, map_injective, of_isIntegrallyClosed_of_isIntegrallyClosedIn
-/
protected lemma iIndepFun.iIndep {m : forall i, MeasurableSpace (κ i)} {f : forall x : ι, Ω -> κ x}
    (hf : iIndepFun f μ) :
    iIndep (fun x => (m x).comap (f x)) μ := hf

/--
lemma `iIndepFun_iff` / 引理 `iIndepFun_iff`

English:
lemma iIndepFun_iff
  statement: {β : ι -> Type*}
  proof: by
  simp only [iIndepFun_iff_iIndep, iIndep_iff]

中文:
引理 iIndepFun_iff
  结论: {β : ι -> 类型}
  证明: by
  simp only [iIndepFun_iff_iIndep, iIndep_iff]

Depends on / 依赖: iIndepFun_iff_iIndep, iIndep_iff
-/
lemma iIndepFun_iff {β : ι -> Type*}
    (m : forall x : ι, MeasurableSpace (β x)) (f : forall x : ι, Ω -> β x) (μ : Measure Ω) :
    iIndepFun f μ ↔ forall (s : Finset ι) {f' : ι -> Set Ω}
      (_H : forall i, i in s -> MeasurableSet[(m i).comap (f i)] (f' i)),
      μ (⋂ i in s, f' i) = ∏ i in s, μ (f' i) := by
  simp only [iIndepFun_iff_iIndep, iIndep_iff]

/--
lemma `iIndepFun.meas_biInter` / 引理 `iIndepFun.meas_biInter`

English:
lemma iIndepFun.meas_biInter
  statement: {m : forall i, MeasurableSpace (κ i)} {f : forall x : ι, Ω -> κ x}
  proof: hf.iIndep.meas_biInter hs

中文:
引理 iIndepFun.meas_bi整数er
  结论: {m : 对任意 i, 可测空间 (κ i)} {f : 对任意 x : ι, Ω -> κ x}
  证明: hf.iIndep.meas_biInter hs

Depends on / 依赖: hf.iIndep.meas_biInter, iIndep, meas_biInter
-/
lemma iIndepFun.meas_biInter {m : forall i, MeasurableSpace (κ i)} {f : forall x : ι, Ω -> κ x}
    (hf : iIndepFun f μ) (hs : forall i, i in S -> MeasurableSet[(m i).comap (f i)] (s i)) :
    μ (⋂ i in S, s i) = ∏ i in S, μ (s i) := hf.iIndep.meas_biInter hs

/--
lemma `iIndepFun.meas_iInter` / 引理 `iIndepFun.meas_iInter`

English:
lemma iIndepFun.meas_iInter
  statement: [Fintype ι] {m : forall i, MeasurableSpace (κ i)} {f : forall x : ι, Ω -> κ x}
  proof: hf.iIndep.meas_iInter hs

中文:
引理 iIndepFun.meas_i整数er
  结论: [有限类型 ι] {m : 对任意 i, 可测空间 (κ i)} {f : 对任意 x : ι, Ω -> κ x}
  证明: hf.iIndep.meas_iInter hs

Depends on / 依赖: hf.iIndep.meas_iInter, iIndep, meas_iInter
-/
lemma iIndepFun.meas_iInter [Fintype ι] {m : forall i, MeasurableSpace (κ i)} {f : forall x : ι, Ω -> κ x}
    (hf : iIndepFun f μ) (hs : forall i, MeasurableSet[(m i).comap (f i)] (s i)) :
    μ (⋂ i, s i) = ∏ i, μ (s i) := hf.iIndep.meas_iInter hs

/--
lemma `IndepFun_iff_Indep` / 引理 `IndepFun_iff_Indep`

English:
lemma IndepFun_iff_Indep
  statement: [mβ : MeasurableSpace β]
  proof: by
  simp only [IndepFun, Indep, Kernel.IndepFun]

中文:
引理 IndepFun_iff_Indep
  结论: [mβ : 可测空间 β]
  证明: by
  simp only [IndepFun, Indep, Kernel.IndepFun]

Depends on / 依赖: IndepFun, Kernel, Kernel.IndepFun
-/
lemma IndepFun_iff_Indep [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (f : Ω -> β) (g : Ω -> γ) (μ : Measure Ω) :
    f ⟂ᵢ[μ] g ↔ Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ := by
  simp only [IndepFun, Indep, Kernel.IndepFun]

/--
lemma `IndepFun_iff` / 引理 `IndepFun_iff`

English:
lemma IndepFun_iff
  statement: {β γ} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
  proof: by
  rw [IndepFun_iff_Indep]; rw [Indep_iff]

中文:
引理 IndepFun_iff
  结论: {β γ} [mβ : 可测空间 β] [mγ : 可测空间 γ]
  证明: by
  rw [IndepFun_iff_Indep]; rw [Indep_iff]

Depends on / 依赖: IndepFun_iff_Indep, Indep_iff
-/
lemma IndepFun_iff {β γ} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω -> β) (g : Ω -> γ) (μ : Measure Ω) :
    f ⟂ᵢ[μ] g ↔ forall t1 t2, MeasurableSet[MeasurableSpace.comap f mβ] t1
      -> MeasurableSet[MeasurableSpace.comap g mγ] t2 -> μ (t1 inter t2) = μ t1 * μ t2 := by
  rw [IndepFun_iff_Indep]; rw [Indep_iff]

/--
lemma `IndepFun.meas_inter` / 引理 `IndepFun.meas_inter`

English:
lemma IndepFun.meas_inter
  statement: [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] {f : Ω -> β} {g : Ω -> γ}
  proof: (IndepFun_iff _ _ _).1 hfg _ _ hs ht

中文:
引理 IndepFun.meas_inter
  结论: [mβ : 可测空间 β] [mγ : 可测空间 γ] {f : Ω -> β} {g : Ω -> γ}
  证明: (IndepFun_iff _ _ _).1 hfg _ _ hs ht

Depends on / 依赖: IndepFun_iff
-/
lemma IndepFun.meas_inter [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] {f : Ω -> β} {g : Ω -> γ}
    (hfg : f ⟂ᵢ[μ] g) {s t : Set Ω} (hs : MeasurableSet[mβ.comap f] s)
    (ht : MeasurableSet[mγ.comap g] t) :
    μ (s inter t) = μ s * μ t :=
  (IndepFun_iff _ _ _).1 hfg _ _ hs ht

/--
lemma `iIndepSets.precomp` / 引理 `iIndepSets.precomp`

English:
lemma iIndepSets.precomp
  given: (hg : Function.Injective g) (h : iIndepSets π μ)
  proof: Kernel.iIndepSets.precomp hg h

中文:
引理 iIndepSets.precomp
  条件: (hg : 函数.单射 g) (h : iIndepSets π μ)
  证明: Kernel.iIndepSets.precomp hg h

Depends on / 依赖: Kernel, Kernel.iIndepSets.precomp, iIndepSets, precomp
-/
lemma iIndepSets.precomp (hg : Function.Injective g) (h : iIndepSets π μ) :
    iIndepSets (π ∘ g) μ :=
  Kernel.iIndepSets.precomp hg h

/--
lemma `iIndepSets.of_precomp` / 引理 `iIndepSets.of_precomp`

English:
lemma iIndepSets.of_precomp
  given: (hg : Function.Surjective g) (h : iIndepSets (π ∘ g) μ)
  proof: Kernel.iIndepSets.of_precomp hg h

中文:
引理 iIndepSets.of_precomp
  条件: (hg : 函数.满射 g) (h : iIndepSets (π ∘ g) μ)
  证明: Kernel.iIndepSets.of_precomp hg h

Depends on / 依赖: Kernel, Kernel.iIndepSets.of_precomp, iIndepSets, of_precomp
-/
lemma iIndepSets.of_precomp (hg : Function.Surjective g) (h : iIndepSets (π ∘ g) μ) :
    iIndepSets π μ :=
  Kernel.iIndepSets.of_precomp hg h

/--
lemma `iIndepSets_precomp_of_bijective` / 引理 `iIndepSets_precomp_of_bijective`

English:
lemma iIndepSets_precomp_of_bijective
  given: (hg : Function.Bijective g)
  proof: Kernel.iIndepSets_precomp_of_bijective hg

中文:
引理 iIndepSets_precomp_of_bijective
  条件: (hg : 函数.双射 g)
  证明: Kernel.iIndepSets_precomp_of_bijective hg

Depends on / 依赖: Kernel, Kernel.iIndepSets_precomp_of_bijective, iIndepSets_precomp_of_bijective
-/
lemma iIndepSets_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepSets (π ∘ g) μ ↔ iIndepSets π μ :=
  Kernel.iIndepSets_precomp_of_bijective hg

/--
lemma `iIndep.precomp` / 引理 `iIndep.precomp`

English:
lemma iIndep.precomp
  given: (hg : Function.Injective g) (h : iIndep m μ)
  proof: Kernel.iIndep.precomp hg h

中文:
引理 iIndep.precomp
  条件: (hg : 函数.单射 g) (h : iIndep m μ)
  证明: Kernel.iIndep.precomp hg h

Depends on / 依赖: Kernel, Kernel.iIndep.precomp, iIndep, precomp
-/
lemma iIndep.precomp (hg : Function.Injective g) (h : iIndep m μ) :
    iIndep (m ∘ g) μ :=
  Kernel.iIndep.precomp hg h

/--
lemma `iIndep.of_precomp` / 引理 `iIndep.of_precomp`

English:
lemma iIndep.of_precomp
  given: (hg : Function.Surjective g) (h : iIndep (m ∘ g) μ)
  proof: Kernel.iIndep.of_precomp hg h

中文:
引理 iIndep.of_precomp
  条件: (hg : 函数.满射 g) (h : iIndep (m ∘ g) μ)
  证明: Kernel.iIndep.of_precomp hg h

Depends on / 依赖: Kernel, Kernel.iIndep.of_precomp, iIndep, of_precomp
-/
lemma iIndep.of_precomp (hg : Function.Surjective g) (h : iIndep (m ∘ g) μ) :
    iIndep m μ :=
  Kernel.iIndep.of_precomp hg h

/--
lemma `iIndep_precomp_of_bijective` / 引理 `iIndep_precomp_of_bijective`

English:
lemma iIndep_precomp_of_bijective
  given: (hg : Function.Bijective g)
  proof: Kernel.iIndep_precomp_of_bijective hg

中文:
引理 iIndep_precomp_of_bijective
  条件: (hg : 函数.双射 g)
  证明: Kernel.iIndep_precomp_of_bijective hg

Depends on / 依赖: Kernel, Kernel.iIndep_precomp_of_bijective, iIndep_precomp_of_bijective
-/
lemma iIndep_precomp_of_bijective (hg : Function.Bijective g) :
    iIndep (m ∘ g) μ ↔ iIndep m μ :=
  Kernel.iIndep_precomp_of_bijective hg

/--
lemma `iIndepSet.precomp` / 引理 `iIndepSet.precomp`

English:
lemma iIndepSet.precomp
  given: (hg : Function.Injective g) (h : iIndepSet s μ)
  proof: Kernel.iIndepSet.precomp hg h

中文:
引理 iIndepSet.precomp
  条件: (hg : 函数.单射 g) (h : iIndepSet s μ)
  证明: Kernel.iIndepSet.precomp hg h

Depends on / 依赖: Kernel, Kernel.iIndepSet.precomp, iIndepSet, precomp
-/
lemma iIndepSet.precomp (hg : Function.Injective g) (h : iIndepSet s μ) :
    iIndepSet (s ∘ g) μ :=
  Kernel.iIndepSet.precomp hg h

/--
lemma `iIndepSet.of_precomp` / 引理 `iIndepSet.of_precomp`

English:
lemma iIndepSet.of_precomp
  given: (hg : Function.Surjective g) (h : iIndepSet (s ∘ g) μ)
  proof: Kernel.iIndepSet.of_precomp hg h

中文:
引理 iIndepSet.of_precomp
  条件: (hg : 函数.满射 g) (h : iIndepSet (s ∘ g) μ)
  证明: Kernel.iIndepSet.of_precomp hg h

Depends on / 依赖: Kernel, Kernel.iIndepSet.of_precomp, iIndepSet, of_precomp
-/
lemma iIndepSet.of_precomp (hg : Function.Surjective g) (h : iIndepSet (s ∘ g) μ) :
    iIndepSet s μ :=
  Kernel.iIndepSet.of_precomp hg h

/--
lemma `iIndepSet_precomp_of_bijective` / 引理 `iIndepSet_precomp_of_bijective`

English:
lemma iIndepSet_precomp_of_bijective
  given: (hg : Function.Bijective g)
  proof: Kernel.iIndepSet_precomp_of_bijective hg

中文:
引理 iIndepSet_precomp_of_bijective
  条件: (hg : 函数.双射 g)
  证明: Kernel.iIndepSet_precomp_of_bijective hg

Depends on / 依赖: Kernel, Kernel.iIndepSet_precomp_of_bijective, iIndepSet_precomp_of_bijective
-/
lemma iIndepSet_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepSet (s ∘ g) μ ↔ iIndepSet s μ :=
  Kernel.iIndepSet_precomp_of_bijective hg

variable {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)} {f : forall i, Ω -> β i}

/--
lemma `iIndepFun.precomp` / 引理 `iIndepFun.precomp`

English:
lemma iIndepFun.precomp
  given: (hg : g.Injective) (h : iIndepFun f μ)
  proof: Kernel.iIndepFun.precomp hg h

中文:
引理 iIndepFun.precomp
  条件: (hg : g.单射) (h : iIndepFun f μ)
  证明: Kernel.iIndepFun.precomp hg h
-/
lemma iIndepFun.precomp (hg : g.Injective) (h : iIndepFun f μ) :
    iIndepFun (m := fun i => m (g i)) (fun i => f (g i)) μ :=
  Kernel.iIndepFun.precomp hg h

/--
lemma `iIndepFun.of_precomp` / 引理 `iIndepFun.of_precomp`

English:
lemma iIndepFun.of_precomp
  statement: (hg : g.Surjective)
  proof: Kernel.iIndepFun.of_precomp hg h

中文:
引理 iIndepFun.of_precomp
  结论: (hg : g.满射)
  证明: Kernel.iIndepFun.of_precomp hg h

Depends on / 依赖: iIndepFun
-/
lemma iIndepFun.of_precomp (hg : g.Surjective)
    (h : iIndepFun (m := fun i => m (g i)) (fun i => f (g i)) μ) : iIndepFun f μ :=
  Kernel.iIndepFun.of_precomp hg h

/--
lemma `iIndepFun_precomp_of_bijective` / 引理 `iIndepFun_precomp_of_bijective`

English:
lemma iIndepFun_precomp_of_bijective
  given: (hg : g.Bijective)
  proof: Kernel.iIndepFun_precomp_of_bijective hg

中文:
引理 iIndepFun_precomp_of_bijective
  条件: (hg : g.双射)
  证明: Kernel.iIndepFun_precomp_of_bijective hg

Depends on / 依赖: iIndepFun
-/
lemma iIndepFun_precomp_of_bijective (hg : g.Bijective) :
    iIndepFun (m := fun i => m (g i)) (fun i => f (g i)) μ ↔ iIndepFun f μ :=
  Kernel.iIndepFun_precomp_of_bijective hg

end Definition_lemmas

section Indep

variable {m₁ m₂ m₃ m₄ : MeasurableSpace Ω} (m' : MeasurableSpace Ω)
  {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}

@[symm]
/--
theorem `IndepSets.symm` / 定理 `IndepSets.symm`

English:
theorem IndepSets.symm
  given: {s₁ s₂ : Set (Set Ω)} (h : IndepSets s₁ s₂ μ)
  statement: IndepSets s₂ s₁ μ
  proof: Kernel.IndepSets.symm h

@[symm]

中文:
定理 IndepSets.symm
  条件: {s₁ s₂ : 集合 (集合 Ω)} (h : IndepSets s₁ s₂ μ)
  结论: IndepSets s₂ s₁ μ
  证明: Kernel.IndepSets.symm h

@[symm]

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.symm
-/
theorem IndepSets.symm {s₁ s₂ : Set (Set Ω)} (h : IndepSets s₁ s₂ μ) : IndepSets s₂ s₁ μ :=
  Kernel.IndepSets.symm h

@[symm]
/--
theorem `Indep.symm` / 定理 `Indep.symm`

English:
theorem Indep.symm
  given: (h : Indep m₁ m₂ μ)
  statement: Indep m₂ m₁ μ
  proof: IndepSets.symm h

中文:
定理 Indep.symm
  条件: (h : Indep m₁ m₂ μ)
  结论: Indep m₂ m₁ μ
  证明: IndepSets.symm h

Depends on / 依赖: IndepSets, IndepSets.symm
-/
theorem Indep.symm (h : Indep m₁ m₂ μ) : Indep m₂ m₁ μ := IndepSets.symm h

/--
theorem `indep_bot_right` / 定理 `indep_bot_right`

English:
theorem indep_bot_right
  given: [IsZeroOrProbabilityMeasure μ]
  statement: Indep m' ⊥ μ
  proof: Kernel.indep_bot_right m'

中文:
定理 indep_bot_right
  条件: [是ZeroOrProbabilityMeasure μ]
  结论: Indep m' ⊥ μ
  证明: Kernel.indep_bot_right m'

Depends on / 依赖: Kernel, Kernel.indep_bot_right, indep_bot_right
-/
theorem indep_bot_right [IsZeroOrProbabilityMeasure μ] : Indep m' ⊥ μ :=
  Kernel.indep_bot_right m'

/--
theorem `indep_bot_left` / 定理 `indep_bot_left`

English:
theorem indep_bot_left
  given: [IsZeroOrProbabilityMeasure μ]
  statement: Indep ⊥ m' μ
  proof: (indep_bot_right m').symm

中文:
定理 indep_bot_left
  条件: [是ZeroOrProbabilityMeasure μ]
  结论: Indep ⊥ m' μ
  证明: (indep_bot_right m').symm

Depends on / 依赖: indep_bot_right
-/
theorem indep_bot_left [IsZeroOrProbabilityMeasure μ] : Indep ⊥ m' μ := (indep_bot_right m').symm

/--
theorem `indepSet_empty_right` / 定理 `indepSet_empty_right`

English:
theorem indepSet_empty_right
  given: [IsZeroOrProbabilityMeasure μ] (s : Set Ω)
  statement: IndepSet s ∅ μ
  proof: Kernel.indepSet_empty_right s

中文:
定理 indepSet_empty_right
  条件: [是ZeroOrProbabilityMeasure μ] (s : 集合 Ω)
  结论: IndepSet s ∅ μ
  证明: Kernel.indepSet_empty_right s

Depends on / 依赖: Kernel, Kernel.indepSet_empty_right, indepSet_empty_right
-/
theorem indepSet_empty_right [IsZeroOrProbabilityMeasure μ] (s : Set Ω) : IndepSet s ∅ μ :=
  Kernel.indepSet_empty_right s

/--
theorem `indepSet_empty_left` / 定理 `indepSet_empty_left`

English:
theorem indepSet_empty_left
  given: [IsZeroOrProbabilityMeasure μ] (s : Set Ω)
  statement: IndepSet ∅ s μ
  proof: Kernel.indepSet_empty_left s

中文:
定理 indepSet_empty_left
  条件: [是ZeroOrProbabilityMeasure μ] (s : 集合 Ω)
  结论: IndepSet ∅ s μ
  证明: Kernel.indepSet_empty_left s

Depends on / 依赖: Kernel, Kernel.indepSet_empty_left, indepSet_empty_left
-/
theorem indepSet_empty_left [IsZeroOrProbabilityMeasure μ] (s : Set Ω) : IndepSet ∅ s μ :=
  Kernel.indepSet_empty_left s

/--
theorem `indepSets_of_indepSets_of_le_left` / 定理 `indepSets_of_indepSets_of_le_left`

English:
theorem indepSets_of_indepSets_of_le_left
  statement: {s₁ s₂ s₃ : Set (Set Ω)}
  proof: Kernel.indepSets_of_indepSets_of_le_left h_indep h31

中文:
定理 indepSets_of_indepSets_of_le_left
  结论: {s₁ s₂ s₃ : 集合 (集合 Ω)}
  证明: Kernel.indepSets_of_indepSets_of_le_left h_indep h31

Depends on / 依赖: Kernel, Kernel.indepSets_of_indepSets_of_le_left, h_indep, indepSets_of_indepSets_of_le_left
-/
theorem indepSets_of_indepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : IndepSets s₁ s₂ μ) (h31 : s₃ subseteq s₁) :
    IndepSets s₃ s₂ μ :=
  Kernel.indepSets_of_indepSets_of_le_left h_indep h31

/--
theorem `indepSets_of_indepSets_of_le_right` / 定理 `indepSets_of_indepSets_of_le_right`

English:
theorem indepSets_of_indepSets_of_le_right
  statement: {s₁ s₂ s₃ : Set (Set Ω)}
  proof: Kernel.indepSets_of_indepSets_of_le_right h_indep h32

中文:
定理 indepSets_of_indepSets_of_le_right
  结论: {s₁ s₂ s₃ : 集合 (集合 Ω)}
  证明: Kernel.indepSets_of_indepSets_of_le_right h_indep h32

Depends on / 依赖: Kernel, Kernel.indepSets_of_indepSets_of_le_right, h_indep, indepSets_of_indepSets_of_le_right
-/
theorem indepSets_of_indepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : IndepSets s₁ s₂ μ) (h32 : s₃ subseteq s₂) :
    IndepSets s₁ s₃ μ :=
  Kernel.indepSets_of_indepSets_of_le_right h_indep h32

/--
theorem `indep_of_indep_of_le_left` / 定理 `indep_of_indep_of_le_left`

English:
theorem indep_of_indep_of_le_left
  given: (h_indep : Indep m₁ m₂ μ) (h31 : m₃ <= m₁)
  proof: Kernel.indep_of_indep_of_le_left h_indep h31

中文:
定理 indep_of_indep_of_le_left
  条件: (h_indep : Indep m₁ m₂ μ) (h31 : m₃ <= m₁)
  证明: Kernel.indep_of_indep_of_le_left h_indep h31

Depends on / 依赖: Kernel, Kernel.indep_of_indep_of_le_left, h_indep, indep_of_indep_of_le_left
-/
theorem indep_of_indep_of_le_left (h_indep : Indep m₁ m₂ μ) (h31 : m₃ <= m₁) :
    Indep m₃ m₂ μ :=
  Kernel.indep_of_indep_of_le_left h_indep h31

/--
theorem `indep_of_indep_of_le_right` / 定理 `indep_of_indep_of_le_right`

English:
theorem indep_of_indep_of_le_right
  given: (h_indep : Indep m₁ m₂ μ) (h32 : m₃ <= m₂)
  proof: Kernel.indep_of_indep_of_le_right h_indep h32

中文:
定理 indep_of_indep_of_le_right
  条件: (h_indep : Indep m₁ m₂ μ) (h32 : m₃ <= m₂)
  证明: Kernel.indep_of_indep_of_le_right h_indep h32

Depends on / 依赖: Kernel, Kernel.indep_of_indep_of_le_right, h_indep, indep_of_indep_of_le_right
-/
theorem indep_of_indep_of_le_right (h_indep : Indep m₁ m₂ μ) (h32 : m₃ <= m₂) :
    Indep m₁ m₃ μ :=
  Kernel.indep_of_indep_of_le_right h_indep h32

/--
theorem `indep_of_indep_of_le` / 定理 `indep_of_indep_of_le`

English:
theorem indep_of_indep_of_le
  given: (h_indep : Indep m₁ m₂ μ) (h31 : m₃ <= m₁) (h42 : m₄ <= m₂)
  proof: Kernel.indep_of_indep_of_le h_indep h31 h42

中文:
定理 indep_of_indep_of_le
  条件: (h_indep : Indep m₁ m₂ μ) (h31 : m₃ <= m₁) (h42 : m₄ <= m₂)
  证明: Kernel.indep_of_indep_of_le h_indep h31 h42

Depends on / 依赖: Kernel, Kernel.indep_of_indep_of_le, h_indep, indep_of_indep_of_le
-/
theorem indep_of_indep_of_le (h_indep : Indep m₁ m₂ μ) (h31 : m₃ <= m₁) (h42 : m₄ <= m₂) :
    Indep m₃ m₄ μ :=
  Kernel.indep_of_indep_of_le h_indep h31 h42

/--
theorem `iIndep_of_iIndep_of_le` / 定理 `iIndep_of_iIndep_of_le`

English:
theorem iIndep_of_iIndep_of_le
  statement: {m₁ m₂ : ι -> MeasurableSpace Ω} (h_indep : iIndep m₂ μ)
  proof: Kernel.iIndep_of_iIndep_of_le h_indep h_le

中文:
定理 iIndep_of_iIndep_of_le
  结论: {m₁ m₂ : ι -> 可测空间 Ω} (h_indep : iIndep m₂ μ)
  证明: Kernel.iIndep_of_iIndep_of_le h_indep h_le

Depends on / 依赖: Kernel, Kernel.iIndep_of_iIndep_of_le, h_indep, h_le, iIndep_of_iIndep_of_le
-/
theorem iIndep_of_iIndep_of_le {m₁ m₂ : ι -> MeasurableSpace Ω} (h_indep : iIndep m₂ μ)
    (h_le : forall i, m₁ i <= m₂ i) : iIndep m₁ μ :=
  Kernel.iIndep_of_iIndep_of_le h_indep h_le

/--
theorem `IndepSets.union` / 定理 `IndepSets.union`

English:
theorem IndepSets.union
  given: {s₁ s₂ s' : Set (Set Ω)} (h₁ : IndepSets s₁ s' μ) (h₂ : IndepSets s₂ s' μ)
  proof: Kernel.IndepSets.union h₁ h₂

@[simp]

中文:
定理 IndepSets.union
  条件: {s₁ s₂ s' : 集合 (集合 Ω)} (h₁ : IndepSets s₁ s' μ) (h₂ : IndepSets s₂ s' μ)
  证明: Kernel.IndepSets.union h₁ h₂

@[simp]

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.union
-/
theorem IndepSets.union {s₁ s₂ s' : Set (Set Ω)} (h₁ : IndepSets s₁ s' μ) (h₂ : IndepSets s₂ s' μ) :
    IndepSets (s₁ union s₂) s' μ :=
  Kernel.IndepSets.union h₁ h₂

@[simp]
/--
theorem `IndepSets.union_iff` / 定理 `IndepSets.union_iff`

English:
theorem IndepSets.union_iff
  given: {s₁ s₂ s' : Set (Set Ω)}
  proof: Kernel.IndepSets.union_iff

中文:
定理 IndepSets.union_iff
  条件: {s₁ s₂ s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.union_iff

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.union_iff, union_iff
-/
theorem IndepSets.union_iff {s₁ s₂ s' : Set (Set Ω)} :
    IndepSets (s₁ union s₂) s' μ ↔ IndepSets s₁ s' μ ∧ IndepSets s₂ s' μ :=
  Kernel.IndepSets.union_iff

/--
theorem `IndepSets.iUnion` / 定理 `IndepSets.iUnion`

English:
theorem IndepSets.iUnion
  statement: {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
  proof: Kernel.IndepSets.iUnion hyp

中文:
定理 IndepSets.iUnion
  结论: {s : ι -> 集合 (集合 Ω)} {s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.iUnion hyp

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.iUnion, iUnion
-/
theorem IndepSets.iUnion {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
    (hyp : forall n, IndepSets (s n) s' μ) :
    IndepSets (⋃ n, s n) s' μ :=
  Kernel.IndepSets.iUnion hyp

/--
theorem `IndepSets.biUnion` / 定理 `IndepSets.biUnion`

English:
theorem IndepSets.biUnion
  statement: {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
  proof: Kernel.IndepSets.biUnion hyp

中文:
定理 IndepSets.biUnion
  结论: {s : ι -> 集合 (集合 Ω)} {s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.biUnion hyp

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.biUnion, biUnion
-/
theorem IndepSets.biUnion {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (hyp : forall n in u, IndepSets (s n) s' μ) :
    IndepSets (⋃ n in u, s n) s' μ :=
  Kernel.IndepSets.biUnion hyp

/--
theorem `IndepSets.inter` / 定理 `IndepSets.inter`

English:
theorem IndepSets.inter
  given: {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)) (h₁ : IndepSets s₁ s' μ)
  proof: Kernel.IndepSets.inter s₂ h₁

中文:
定理 IndepSets.inter
  条件: {s₁ s' : 集合 (集合 Ω)} (s₂ : 集合 (集合 Ω)) (h₁ : IndepSets s₁ s' μ)
  证明: Kernel.IndepSets.inter s₂ h₁

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.inter
-/
theorem IndepSets.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)) (h₁ : IndepSets s₁ s' μ) :
    IndepSets (s₁ inter s₂) s' μ :=
  Kernel.IndepSets.inter s₂ h₁

/--
theorem `IndepSets.iInter` / 定理 `IndepSets.iInter`

English:
theorem IndepSets.iInter
  statement: {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
  proof: Kernel.IndepSets.iInter h

中文:
定理 IndepSets.i整数er
  结论: {s : ι -> 集合 (集合 Ω)} {s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.iInter h

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.iInter, iInter
-/
theorem IndepSets.iInter {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
    (h : exists n, IndepSets (s n) s' μ) :
    IndepSets (⋂ n, s n) s' μ :=
  Kernel.IndepSets.iInter h

/--
theorem `IndepSets.bInter` / 定理 `IndepSets.bInter`

English:
theorem IndepSets.bInter
  statement: {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
  proof: Kernel.IndepSets.bInter h

中文:
定理 IndepSets.b整数er
  结论: {s : ι -> 集合 (集合 Ω)} {s' : 集合 (集合 Ω)}
  证明: Kernel.IndepSets.bInter h

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.bInter, bInter
-/
theorem IndepSets.bInter {s : ι -> Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (h : exists n in u, IndepSets (s n) s' μ) :
    IndepSets (⋂ n in u, s n) s' μ :=
  Kernel.IndepSets.bInter h

/--
theorem `indepSets_singleton_iff` / 定理 `indepSets_singleton_iff`

English:
theorem indepSets_singleton_iff
  given: {s t : Set Ω}
  proof: by
  simp only [IndepSets, Kernel.indepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

中文:
定理 indepSets_singleton_iff
  条件: {s t : 集合 Ω}
  证明: by
  simp only [IndepSets, Kernel.indepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

Depends on / 依赖: Filter, Filter.eventually_pure, IndepSets, Kernel, Kernel.const_apply, Kernel.indepSets_singleton_iff, ae_dirac_eq, const_apply, eventually_pure, indepSets_singleton_iff
-/
theorem indepSets_singleton_iff {s t : Set Ω} :
    IndepSets {s} {t} μ ↔ μ (s inter t) = μ s * μ t := by
  simp only [IndepSets, Kernel.indepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

/--
lemma `indepSets_iff_singleton_indepSets` / 引理 `indepSets_iff_singleton_indepSets`

English:
lemma indepSets_iff_singleton_indepSets
  given: {𝒜 ℬ : Set (Set Ω)}
  proof: indepSets_of_indepSets_of_le_left h (Set.singleton_subset_iff.2 hA)
  mpr h := by
    rw [← 𝒜.biUnion_of_singleton]
    exact IndepSets.biUnion h

中文:
引理 indepSets_iff_singleton_indepSets
  条件: {𝒜 ℬ : 集合 (集合 Ω)}
  证明: indepSets_of_indepSets_of_le_left h (Set.singleton_subset_iff.2 hA)
  mpr h := by
    rw [← 𝒜.biUnion_of_singleton]
    exact IndepSets.biUnion h

Depends on / 依赖: Set.singleton_subset_iff, indepSets_of_indepSets_of_le_left, singleton_subset_iff
-/
lemma indepSets_iff_singleton_indepSets {𝒜 ℬ : Set (Set Ω)} :
    IndepSets 𝒜 ℬ μ ↔ forall A in 𝒜, IndepSets {A} ℬ μ where
  mp h A hA := indepSets_of_indepSets_of_le_left h (Set.singleton_subset_iff.2 hA)
  mpr h := by
    rw [← 𝒜.biUnion_of_singleton]
    exact IndepSets.biUnion h

end Indep

/-! ### Deducing `Indep` from `iIndep` -/


section FromIndepToIndep

variable {m : ι -> MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/--
theorem `iIndepSets.indepSets` / 定理 `iIndepSets.indepSets`

English:
theorem iIndepSets.indepSets
  statement: {s : ι -> Set (Set Ω)}
  proof: Kernel.iIndepSets.indepSets h_indep hij

中文:
定理 iIndepSets.indepSets
  结论: {s : ι -> 集合 (集合 Ω)}
  证明: Kernel.iIndepSets.indepSets h_indep hij

Depends on / 依赖: Kernel, Kernel.iIndepSets.indepSets, h_indep, iIndepSets, indepSets
-/
theorem iIndepSets.indepSets {s : ι -> Set (Set Ω)}
    (h_indep : iIndepSets s μ) {i j : ι} (hij : i != j) : IndepSets (s i) (s j) μ :=
  Kernel.iIndepSets.indepSets h_indep hij

/--
theorem `iIndep.indep` / 定理 `iIndep.indep`

English:
theorem iIndep.indep
  proof: Kernel.iIndep.indep h_indep hij

中文:
定理 iIndep.indep
  证明: Kernel.iIndep.indep h_indep hij

Depends on / 依赖: Kernel, Kernel.iIndep.indep, h_indep, iIndep
-/
theorem iIndep.indep
    (h_indep : iIndep m μ) {i j : ι} (hij : i != j) : Indep (m i) (m j) μ :=
  Kernel.iIndep.indep h_indep hij

/--
theorem `iIndepFun.indepFun` / 定理 `iIndepFun.indepFun`

English:
theorem iIndepFun.indepFun
  statement: {β : ι -> Type*}
  proof: Kernel.iIndepFun.indepFun hf_Indep hij

中文:
定理 iIndepFun.indepFun
  结论: {β : ι -> 类型}
  证明: Kernel.iIndepFun.indepFun hf_Indep hij

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun, hf_Indep, iIndepFun, indepFun
-/
theorem iIndepFun.indepFun {β : ι -> Type*}
    {m : forall x, MeasurableSpace (β x)} {f : forall i, Ω -> β i} (hf_Indep : iIndepFun f μ) {i j : ι}
    (hij : i != j) :
    f i ⟂ᵢ[μ] f j :=
  Kernel.iIndepFun.indepFun hf_Indep hij

end FromIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

variable {m : ι -> MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}


/--
theorem `iIndep.iIndepSets` / 定理 `iIndep.iIndepSets`

English:
theorem iIndep.iIndepSets
  proof: Kernel.iIndep.iIndepSets hms h_indep

中文:
定理 iIndep.iIndepSets
  证明: Kernel.iIndep.iIndepSets hms h_indep

Depends on / 依赖: Kernel, Kernel.iIndep.iIndepSets, h_indep, iIndep, iIndepSets
-/
theorem iIndep.iIndepSets
    {s : ι -> Set (Set Ω)} (hms : forall n, m n = generateFrom (s n)) (h_indep : iIndep m μ) :
    iIndepSets s μ :=
  Kernel.iIndep.iIndepSets hms h_indep

/--
theorem `Indep.indepSets` / 定理 `Indep.indepSets`

English:
theorem Indep.indepSets
  statement: {s1 s2 : Set (Set Ω)}
  proof: Kernel.Indep.indepSets h_indep

中文:
定理 Indep.indepSets
  结论: {s1 s2 : 集合 (集合 Ω)}
  证明: Kernel.Indep.indepSets h_indep

Depends on / 依赖: Kernel, Kernel.Indep.indepSets, h_indep, indepSets
-/
theorem Indep.indepSets {s1 s2 : Set (Set Ω)}
    (h_indep : Indep (generateFrom s1) (generateFrom s2) μ) :
    IndepSets s1 s2 μ :=
  Kernel.Indep.indepSets h_indep

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

variable {m : ι -> MeasurableSpace Ω} {m1 m2 _mΩ : MeasurableSpace Ω} {μ : Measure Ω}


/--
theorem `IndepSets.indep` / 定理 `IndepSets.indep`

English:
theorem IndepSets.indep
  statement: [IsZeroOrProbabilityMeasure μ]
  proof: Kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp

中文:
定理 IndepSets.indep
  结论: [是ZeroOrProbabilityMeasure μ]
  证明: Kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.indep
-/
theorem IndepSets.indep [IsZeroOrProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (h1 : m1 <= _mΩ) (h2 : m2 <= _mΩ) (hp1 : IsPiSystem p1)
    (hp2 : IsPiSystem p2) (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSets p1 p2 μ) :
    Indep m1 m2 μ :=
  Kernel.IndepSets.indep h1 h2 hp1 hp2 hpm1 hpm2 hyp

/--
theorem `IndepSets.indep'` / 定理 `IndepSets.indep'`

English:
theorem IndepSets.indep'
  statement: [IsZeroOrProbabilityMeasure μ]
  proof: Kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp

中文:
定理 IndepSets.indep'
  结论: [是ZeroOrProbabilityMeasure μ]
  证明: Kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp

Depends on / 依赖: IndepSets, Kernel, Kernel.IndepSets.indep
-/
theorem IndepSets.indep' [IsZeroOrProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (hp1m : forall s in p1, MeasurableSet s) (hp2m : forall s in p2, MeasurableSet s)
    (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : IndepSets p1 p2 μ) :
    Indep (generateFrom p1) (generateFrom p2) μ :=
  Kernel.IndepSets.indep' hp1m hp2m hp1 hp2 hyp

/--
theorem `indepSets_piiUnionInter_of_disjoint` / 定理 `indepSets_piiUnionInter_of_disjoint`

English:
theorem indepSets_piiUnionInter_of_disjoint
  statement: {s : ι -> Set (Set Ω)}
  proof: Kernel.indepSets_piiUnionInter_of_disjoint h_indep hST

中文:
定理 indepSets_piiUnion整数er_of_disjoint
  结论: {s : ι -> 集合 (集合 Ω)}
  证明: Kernel.indepSets_piiUnionInter_of_disjoint h_indep hST

Depends on / 依赖: Kernel, Kernel.indepSets_piiUnionInter_of_disjoint, h_indep, indepSets_piiUnionInter_of_disjoint
-/
theorem indepSets_piiUnionInter_of_disjoint {s : ι -> Set (Set Ω)}
    {S T : Set ι} (h_indep : iIndepSets s μ) (hST : Disjoint S T) :
    IndepSets (piiUnionInter s S) (piiUnionInter s T) μ :=
  Kernel.indepSets_piiUnionInter_of_disjoint h_indep hST

/--
theorem `iIndepSet.indep_generateFrom_of_disjoint` / 定理 `iIndepSet.indep_generateFrom_of_disjoint`

English:
theorem iIndepSet.indep_generateFrom_of_disjoint
  statement: {s : ι -> Set Ω}
  proof: Kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST

中文:
定理 iIndepSet.indep_generateFrom_of_disjoint
  结论: {s : ι -> 集合 Ω}
  证明: Kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST

Depends on / 依赖: Kernel, Kernel.iIndepSet.indep_generateFrom_of_disjoint, iIndepSet, indep_generateFrom_of_disjoint
-/
theorem iIndepSet.indep_generateFrom_of_disjoint {s : ι -> Set Ω}
    (hsm : forall n, MeasurableSet (s n)) (hs : iIndepSet s μ) (S T : Set ι) (hST : Disjoint S T) :
    Indep (generateFrom { t | exists n in S, s n = t }) (generateFrom { t | exists k in T, s k = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_of_disjoint hsm hs S T hST

/--
theorem `indep_iSup_of_disjoint` / 定理 `indep_iSup_of_disjoint`

English:
theorem indep_iSup_of_disjoint
  proof: Kernel.indep_iSup_of_disjoint h_le h_indep hST

中文:
定理 indep_iSup_of_disjoint
  证明: Kernel.indep_iSup_of_disjoint h_le h_indep hST

Depends on / 依赖: Kernel, Kernel.indep_iSup_of_disjoint, h_indep, h_le, indep_iSup_of_disjoint
-/
theorem indep_iSup_of_disjoint
    (h_le : forall i, m i <= _mΩ) (h_indep : iIndep m μ) {S T : Set ι} (hST : Disjoint S T) :
    Indep (⨆ i in S, m i) (⨆ i in T, m i) μ :=
  Kernel.indep_iSup_of_disjoint h_le h_indep hST

/--
theorem `indep_iSup_of_directed_le` / 定理 `indep_iSup_of_directed_le`

English:
theorem indep_iSup_of_directed_le
  proof: Kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm

中文:
定理 indep_iSup_of_directed_le
  证明: Kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm

Depends on / 依赖: Kernel, Kernel.indep_iSup_of_directed_le, h_indep, h_le, indep_iSup_of_directed_le
-/
theorem indep_iSup_of_directed_le
    [IsZeroOrProbabilityMeasure μ] (h_indep : forall i, Indep (m i) m1 μ)
    (h_le : forall i, m i <= _mΩ) (h_le' : m1 <= _mΩ) (hm : Directed (· <= ·) m) :
    Indep (⨆ i, m i) m1 μ :=
  Kernel.indep_iSup_of_directed_le h_indep h_le h_le' hm

/--
theorem `iIndepSet.indep_generateFrom_lt` / 定理 `iIndepSet.indep_generateFrom_lt`

English:
theorem iIndepSet.indep_generateFrom_lt
  statement: [Preorder ι] {s : ι -> Set Ω}
  proof: Kernel.iIndepSet.indep_generateFrom_lt hsm hs i

中文:
定理 iIndepSet.indep_generateFrom_lt
  结论: [预序 ι] {s : ι -> 集合 Ω}
  证明: Kernel.iIndepSet.indep_generateFrom_lt hsm hs i

Depends on / 依赖: Kernel, Kernel.iIndepSet.indep_generateFrom_lt, iIndepSet, indep_generateFrom_lt
-/
theorem iIndepSet.indep_generateFrom_lt [Preorder ι] {s : ι -> Set Ω}
    (hsm : forall n, MeasurableSet (s n)) (hs : iIndepSet s μ) (i : ι) :
    Indep (generateFrom {s i}) (generateFrom { t | exists j < i, s j = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_lt hsm hs i

/--
theorem `iIndepSet.indep_generateFrom_le` / 定理 `iIndepSet.indep_generateFrom_le`

English:
theorem iIndepSet.indep_generateFrom_le
  statement: [Preorder ι]
  proof: Kernel.iIndepSet.indep_generateFrom_le hsm hs i hk

中文:
定理 iIndepSet.indep_generateFrom_le
  结论: [预序 ι]
  证明: Kernel.iIndepSet.indep_generateFrom_le hsm hs i hk

Depends on / 依赖: Kernel, Kernel.iIndepSet.indep_generateFrom_le, iIndepSet, indep_generateFrom_le
-/
theorem iIndepSet.indep_generateFrom_le [Preorder ι]
    {s : ι -> Set Ω}
    (hsm : forall n, MeasurableSet (s n)) (hs : iIndepSet s μ) (i : ι) {k : ι} (hk : i < k) :
    Indep (generateFrom {s k}) (generateFrom { t | exists j <= i, s j = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_le hsm hs i hk

/--
theorem `iIndepSet.indep_generateFrom_le_nat` / 定理 `iIndepSet.indep_generateFrom_le_nat`

English:
theorem iIndepSet.indep_generateFrom_le_nat
  statement: {s : Nat -> Set Ω}
  proof: Kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n

中文:
定理 iIndepSet.indep_generateFrom_le_nat
  结论: {s : 自然数 -> 集合 Ω}
  证明: Kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n

Depends on / 依赖: Kernel, Kernel.iIndepSet.indep_generateFrom_le_nat, iIndepSet, indep_generateFrom_le_nat
-/
theorem iIndepSet.indep_generateFrom_le_nat {s : Nat -> Set Ω}
    (hsm : forall n, MeasurableSet (s n)) (hs : iIndepSet s μ) (n : Nat) :
    Indep (generateFrom {s (n + 1)}) (generateFrom { t | exists k <= n, s k = t }) μ :=
  Kernel.iIndepSet.indep_generateFrom_le_nat hsm hs n

/--
theorem `indep_iSup_of_monotone` / 定理 `indep_iSup_of_monotone`

English:
theorem indep_iSup_of_monotone
  statement: [SemilatticeSup ι] [IsZeroOrProbabilityMeasure μ]
  proof: Kernel.indep_iSup_of_monotone h_indep h_le h_le' hm

中文:
定理 indep_iSup_of_monotone
  结论: [SemilatticeSup ι] [是ZeroOrProbabilityMeasure μ]
  证明: Kernel.indep_iSup_of_monotone h_indep h_le h_le' hm

Depends on / 依赖: Kernel, Kernel.indep_iSup_of_monotone, h_indep, h_le, indep_iSup_of_monotone
-/
theorem indep_iSup_of_monotone [SemilatticeSup ι] [IsZeroOrProbabilityMeasure μ]
    (h_indep : forall i, Indep (m i) m1 μ) (h_le : forall i, m i <= _mΩ) (h_le' : m1 <= _mΩ) (hm : Monotone m) :
    Indep (⨆ i, m i) m1 μ :=
  Kernel.indep_iSup_of_monotone h_indep h_le h_le' hm

/--
theorem `indep_iSup_of_antitone` / 定理 `indep_iSup_of_antitone`

English:
theorem indep_iSup_of_antitone
  statement: [SemilatticeInf ι] [IsZeroOrProbabilityMeasure μ]
  proof: Kernel.indep_iSup_of_antitone h_indep h_le h_le' hm

中文:
定理 indep_iSup_of_antitone
  结论: [SemilatticeInf ι] [是ZeroOrProbabilityMeasure μ]
  证明: Kernel.indep_iSup_of_antitone h_indep h_le h_le' hm

Depends on / 依赖: Kernel, Kernel.indep_iSup_of_antitone, h_indep, h_le, indep_iSup_of_antitone
-/
theorem indep_iSup_of_antitone [SemilatticeInf ι] [IsZeroOrProbabilityMeasure μ]
    (h_indep : forall i, Indep (m i) m1 μ) (h_le : forall i, m i <= _mΩ) (h_le' : m1 <= _mΩ) (hm : Antitone m) :
    Indep (⨆ i, m i) m1 μ :=
  Kernel.indep_iSup_of_antitone h_indep h_le h_le' hm

/--
theorem `iIndepSets.piiUnionInter_of_notMem` / 定理 `iIndepSets.piiUnionInter_of_notMem`

English:
theorem iIndepSets.piiUnionInter_of_notMem
  statement: {π : ι -> Set (Set Ω)} {a : ι} {S : Finset ι}
  proof: Kernel.iIndepSets.piiUnionInter_of_notMem hp_ind haS

中文:
定理 iIndepSets.piiUnion整数er_of_notMem
  结论: {π : ι -> 集合 (集合 Ω)} {a : ι} {S : 有限集 ι}
  证明: Kernel.iIndepSets.piiUnionInter_of_notMem hp_ind haS

Depends on / 依赖: Kernel, Kernel.iIndepSets.piiUnionInter_of_notMem, hp_ind, iIndepSets, piiUnionInter_of_notMem
-/
theorem iIndepSets.piiUnionInter_of_notMem {π : ι -> Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iIndepSets π μ) (haS : a ∉ S) :
    IndepSets (piiUnionInter π S) (π a) μ :=
  Kernel.iIndepSets.piiUnionInter_of_notMem hp_ind haS

/--
theorem `iIndepSets.iIndep` / 定理 `iIndepSets.iIndep`

English:
theorem iIndepSets.iIndep
  proof: Kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind

中文:
定理 iIndepSets.iIndep
  证明: Kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind

Depends on / 依赖: Kernel, Kernel.iIndepSets.iIndep, h_generate, h_ind, h_le, h_pi, iIndep, iIndepSets
-/
theorem iIndepSets.iIndep
    (h_le : forall i, m i <= _mΩ) (π : ι -> Set (Set Ω)) (h_pi : forall n, IsPiSystem (π n))
    (h_generate : forall i, m i = generateFrom (π i)) (h_ind : iIndepSets π μ) :
    iIndep m μ :=
  Kernel.iIndepSets.iIndep m h_le π h_pi h_generate h_ind

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `IndepSet`, for measurable sets `s, t`.
* `IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `IndepSet s t μ ↔ IndepSets {s} {t} μ`.
-/


variable {m₁ m₂ _mΩ : MeasurableSpace Ω} {μ : Measure Ω} {s t : Set Ω} (S T : Set (Set Ω))

/--
theorem `indepSet_iff_indepSets_singleton` / 定理 `indepSet_iff_indepSets_singleton`

English:
theorem indepSet_iff_indepSets_singleton
  statement: (hs_meas : MeasurableSet s)
  proof: Kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _

中文:
定理 indepSet_iff_indepSets_singleton
  结论: (hs_meas : 可测集 s)
  证明: Kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _

Depends on / 依赖: IndepSet, IndepSets, IsZeroOrProbabilityMeasure, Kernel, Kernel.indepSet_iff_indepSets_singleton, hs_meas, ht_meas, indepSet_iff_indepSets_singleton, volume_tac
-/
theorem indepSet_iff_indepSets_singleton (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by volume_tac)
    [IsZeroOrProbabilityMeasure μ] : IndepSet s t μ ↔ IndepSets {s} {t} μ :=
  Kernel.indepSet_iff_indepSets_singleton hs_meas ht_meas _ _

/--
theorem `indepSet_iff_measure_inter_eq_mul` / 定理 `indepSet_iff_measure_inter_eq_mul`

English:
theorem indepSet_iff_measure_inter_eq_mul
  statement: (hs_meas : MeasurableSet s)
  proof: (indepSet_iff_indepSets_singleton hs_meas ht_meas μ).trans indepSets_singleton_iff

中文:
定理 indepSet_iff_measure_inter_eq_mul
  结论: (hs_meas : 可测集 s)
  证明: (indepSet_iff_indepSets_singleton hs_meas ht_meas μ).trans indepSets_singleton_iff

Depends on / 依赖: IndepSet, IsZeroOrProbabilityMeasure, hs_meas, ht_meas, indepSet_iff_indepSets_singleton, indepSets_singleton_iff, volume_tac
-/
theorem indepSet_iff_measure_inter_eq_mul (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by volume_tac)
    [IsZeroOrProbabilityMeasure μ] : IndepSet s t μ ↔ μ (s inter t) = μ s * μ t :=
  (indepSet_iff_indepSets_singleton hs_meas ht_meas μ).trans indepSets_singleton_iff

/--
lemma `IndepSet.measure_inter_eq_mul` / 引理 `IndepSet.measure_inter_eq_mul`

English:
lemma IndepSet.measure_inter_eq_mul
  given: {μ : Measure Ω} (h : IndepSet s t μ)
  proof: by
  simpa using Kernel.IndepSet.measure_inter_eq_mul _ _ h

中文:
引理 IndepSet.measure_inter_eq_mul
  条件: {μ : 测度 Ω} (h : IndepSet s t μ)
  证明: by
  simpa using Kernel.IndepSet.measure_inter_eq_mul _ _ h

Depends on / 依赖: IndepSet, Kernel, Kernel.IndepSet.measure_inter_eq_mul, measure_inter_eq_mul
-/
lemma IndepSet.measure_inter_eq_mul {μ : Measure Ω} (h : IndepSet s t μ) :
    μ (s inter t) = μ s * μ t := by
  simpa using Kernel.IndepSet.measure_inter_eq_mul _ _ h

/--
theorem `IndepSets.indepSet_of_mem` / 定理 `IndepSets.indepSet_of_mem`

English:
theorem IndepSets.indepSet_of_mem
  statement: (hs : s in S) (ht : t in T)
  proof: Kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep

中文:
定理 IndepSets.indepSet_of_mem
  结论: (hs : s in S) (ht : t in T)
  证明: Kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep

Depends on / 依赖: IndepSet, IndepSets, IsZeroOrProbabilityMeasure, Kernel, Kernel.IndepSets.indepSet_of_mem, h_indep, hs_meas, ht_meas, indepSet_of_mem, volume_tac
-/
theorem IndepSets.indepSet_of_mem (hs : s in S) (ht : t in T)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measure Ω := by volume_tac) [IsZeroOrProbabilityMeasure μ]
    (h_indep : IndepSets S T μ) :
    IndepSet s t μ :=
  Kernel.IndepSets.indepSet_of_mem _ _ hs ht hs_meas ht_meas _ _ h_indep

/--
theorem `Indep.indepSet_of_measurableSet` / 定理 `Indep.indepSet_of_measurableSet`

English:
theorem Indep.indepSet_of_measurableSet
  proof: Kernel.Indep.indepSet_of_measurableSet h_indep hs ht

中文:
定理 Indep.indepSet_of_measurableSet
  证明: Kernel.Indep.indepSet_of_measurableSet h_indep hs ht

Depends on / 依赖: Kernel, Kernel.Indep.indepSet_of_measurableSet, h_indep, indepSet_of_measurableSet
-/
theorem Indep.indepSet_of_measurableSet
    (h_indep : Indep m₁ m₂ μ) {s t : Set Ω} (hs : MeasurableSet[m₁] s) (ht : MeasurableSet[m₂] t) :
    IndepSet s t μ :=
  Kernel.Indep.indepSet_of_measurableSet h_indep hs ht

/--
theorem `indep_iff_forall_indepSet` / 定理 `indep_iff_forall_indepSet`

English:
theorem indep_iff_forall_indepSet
  given: (μ : Measure Ω)
  proof: Kernel.indep_iff_forall_indepSet m₁ m₂ _ _

中文:
定理 indep_iff_对任意_indepSet
  条件: (μ : 测度 Ω)
  证明: Kernel.indep_iff_forall_indepSet m₁ m₂ _ _

Depends on / 依赖: Kernel, Kernel.indep_iff_forall_indepSet, indep_iff_forall_indepSet
-/
theorem indep_iff_forall_indepSet (μ : Measure Ω) :
    Indep m₁ m₂ μ ↔ forall s t, MeasurableSet[m₁] s -> MeasurableSet[m₂] t -> IndepSet s t μ :=
  Kernel.indep_iff_forall_indepSet m₁ m₂ _ _

/--
theorem `iIndep_comap_mem_iff` / 定理 `iIndep_comap_mem_iff`

English:
theorem iIndep_comap_mem_iff
  given: {f : ι -> Set Ω}
  proof: Kernel.iIndep_comap_mem_iff

alias ⟨_, iIndepSet.iIndep_comap_mem⟩ := iIndep_comap_mem_iff

中文:
定理 iIndep_comap_mem_iff
  条件: {f : ι -> 集合 Ω}
  证明: Kernel.iIndep_comap_mem_iff

alias ⟨_, iIndepSet.iIndep_comap_mem⟩ := iIndep_comap_mem_iff

Depends on / 依赖: Kernel, Kernel.iIndep_comap_mem_iff, iIndep_comap_mem_iff
-/
theorem iIndep_comap_mem_iff {f : ι -> Set Ω} :
    iIndep (fun i => MeasurableSpace.comap (· in f i) ⊤) μ ↔ iIndepSet f μ :=
  Kernel.iIndep_comap_mem_iff

alias ⟨_, iIndepSet.iIndep_comap_mem⟩ := iIndep_comap_mem_iff

/--
theorem `iIndepSets_singleton_iff` / 定理 `iIndepSets_singleton_iff`

English:
theorem iIndepSets_singleton_iff
  given: {s : ι -> Set Ω}
  proof: by
  simp_rw [iIndepSets, Kernel.iIndepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

中文:
定理 iIndepSets_singleton_iff
  条件: {s : ι -> 集合 Ω}
  证明: by
  simp_rw [iIndepSets, Kernel.iIndepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

Depends on / 依赖: Filter, Filter.eventually_pure, Kernel, Kernel.const_apply, Kernel.iIndepSets_singleton_iff, ae_dirac_eq, const_apply, eventually_pure, iIndepSets, iIndepSets_singleton_iff, simp_rw
-/
theorem iIndepSets_singleton_iff {s : ι -> Set Ω} :
    iIndepSets (fun i => {s i}) μ ↔ forall t, μ (⋂ i in t, s i) = ∏ i in t, μ (s i) := by
  simp_rw [iIndepSets, Kernel.iIndepSets_singleton_iff, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

/--
theorem `iIndepSet.meas_biInter` / 定理 `iIndepSet.meas_biInter`

English:
theorem iIndepSet.meas_biInter
  given: {f : ι -> Set Ω} (h : iIndepSet f μ) (s : Finset ι)
  proof: by
  simpa using Kernel.iIndepSet.meas_biInter h s

中文:
定理 iIndepSet.meas_bi整数er
  条件: {f : ι -> 集合 Ω} (h : iIndepSet f μ) (s : 有限集 ι)
  证明: by
  simpa using Kernel.iIndepSet.meas_biInter h s

Depends on / 依赖: Kernel, Kernel.iIndepSet.meas_biInter, iIndepSet, meas_biInter
-/
theorem iIndepSet.meas_biInter {f : ι -> Set Ω} (h : iIndepSet f μ) (s : Finset ι) :
    μ (⋂ i in s, f i) = ∏ i in s, μ (f i) := by
  simpa using Kernel.iIndepSet.meas_biInter h s

/--
theorem `iIndepSet_iff_iIndepSets_singleton` / 定理 `iIndepSet_iff_iIndepSets_singleton`

English:
theorem iIndepSet_iff_iIndepSets_singleton
  given: {f : ι -> Set Ω} (hf : forall i, MeasurableSet (f i))
  proof: Kernel.iIndepSet_iff_iIndepSets_singleton hf

中文:
定理 iIndepSet_iff_iIndepSets_singleton
  条件: {f : ι -> 集合 Ω} (hf : 对任意 i, 可测集 (f i))
  证明: Kernel.iIndepSet_iff_iIndepSets_singleton hf

Depends on / 依赖: Kernel, Kernel.iIndepSet_iff_iIndepSets_singleton, iIndepSet_iff_iIndepSets_singleton
-/
theorem iIndepSet_iff_iIndepSets_singleton {f : ι -> Set Ω} (hf : forall i, MeasurableSet (f i)) :
    iIndepSet f μ ↔ iIndepSets (fun i => {f i}) μ :=
  Kernel.iIndepSet_iff_iIndepSets_singleton hf

/--
theorem `iIndepSet_iff_meas_biInter` / 定理 `iIndepSet_iff_meas_biInter`

English:
theorem iIndepSet_iff_meas_biInter
  given: {f : ι -> Set Ω} (hf : forall i, MeasurableSet (f i))
  proof: by
  simp_rw [iIndepSet, Kernel.iIndepSet_iff_meas_biInter hf, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

中文:
定理 iIndepSet_iff_meas_bi整数er
  条件: {f : ι -> 集合 Ω} (hf : 对任意 i, 可测集 (f i))
  证明: by
  simp_rw [iIndepSet, Kernel.iIndepSet_iff_meas_biInter hf, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

Depends on / 依赖: Filter, Filter.eventually_pure, Kernel, Kernel.const_apply, Kernel.iIndepSet_iff_meas_biInter, ae_dirac_eq, const_apply, eventually_pure, iIndepSet, iIndepSet_iff_meas_biInter, simp_rw
-/
theorem iIndepSet_iff_meas_biInter {f : ι -> Set Ω} (hf : forall i, MeasurableSet (f i)) :
    iIndepSet f μ ↔ forall s, μ (⋂ i in s, f i) = ∏ i in s, μ (f i) := by
  simp_rw [iIndepSet, Kernel.iIndepSet_iff_meas_biInter hf, ae_dirac_eq, Filter.eventually_pure,
    Kernel.const_apply]

/--
theorem `iIndepSets.iIndepSet_of_mem` / 定理 `iIndepSets.iIndepSet_of_mem`

English:
theorem iIndepSets.iIndepSet_of_mem
  statement: {π : ι -> Set (Set Ω)} {f : ι -> Set Ω}
  proof: Kernel.iIndepSets.iIndepSet_of_mem hfπ hf hπ

中文:
定理 iIndepSets.iIndepSet_of_mem
  结论: {π : ι -> 集合 (集合 Ω)} {f : ι -> 集合 Ω}
  证明: Kernel.iIndepSets.iIndepSet_of_mem hfπ hf hπ

Depends on / 依赖: Kernel, Kernel.iIndepSets.iIndepSet_of_mem, iIndepSet_of_mem, iIndepSets
-/
theorem iIndepSets.iIndepSet_of_mem {π : ι -> Set (Set Ω)} {f : ι -> Set Ω}
    (hfπ : forall i, f i in π i) (hf : forall i, MeasurableSet (f i))
    (hπ : iIndepSets π μ) : iIndepSet f μ :=
  Kernel.iIndepSets.iIndepSet_of_mem hfπ hf hπ

end IndepSet

section IndepFun

/-! ### Independence of random variables

-/


variable {β β' γ γ' : Type*} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω -> β} {g : Ω -> β'}

/--
theorem `indepFun_iff_measure_inter_preimage_eq_mul` / 定理 `indepFun_iff_measure_inter_preimage_eq_mul`

English:
theorem indepFun_iff_measure_inter_preimage_eq_mul
  statement: {mβ : MeasurableSpace β}
  proof: by
  simp only [IndepFun, Kernel.indepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, Kernel.const_apply]

alias ⟨IndepFun.measure_inter_preimage_eq_mul, _⟩ := indepFun_iff_measure_inter_preimage_eq_mul

中文:
定理 indepFun_iff_measure_inter_preimage_eq_mul
  结论: {mβ : 可测空间 β}
  证明: by
  simp only [IndepFun, Kernel.indepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, Kernel.const_apply]

alias ⟨IndepFun.measure_inter_preimage_eq_mul, _⟩ := indepFun_iff_measure_inter_preimage_eq_mul

Depends on / 依赖: Filter, Filter.eventually_pure, IndepFun, Kernel, Kernel.const_apply, Kernel.indepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq, const_apply, eventually_pure, indepFun_iff_measure_inter_preimage_eq_mul
-/
theorem indepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} :
    f ⟂ᵢ[μ] g ↔
      forall s t, MeasurableSet s -> MeasurableSet t
        -> μ (f ⁻¹' s inter g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
  simp only [IndepFun, Kernel.indepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, Kernel.const_apply]

alias ⟨IndepFun.measure_inter_preimage_eq_mul, _⟩ := indepFun_iff_measure_inter_preimage_eq_mul

/--
theorem `iIndepFun_iff_measure_inter_preimage_eq_mul` / 定理 `iIndepFun_iff_measure_inter_preimage_eq_mul`

English:
theorem iIndepFun_iff_measure_inter_preimage_eq_mul
  statement: {ι : Type*} {β : ι -> Type*}
  proof: by
  simp only [iIndepFun, Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, Kernel.const_apply]

alias ⟨iIndepFun.measure_inter_preimage_eq_mul, _⟩ := iIndepFun_iff_measure_inter_preimage_eq_mul

中文:
定理 iIndepFun_iff_measure_inter_preimage_eq_mul
  结论: {ι : 类型} {β : ι -> 类型}
  证明: by
  simp only [iIndepFun, Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, Kernel.const_apply]

alias ⟨iIndepFun.measure_inter_preimage_eq_mul, _⟩ := iIndepFun_iff_measure_inter_preimage_eq_mul

Depends on / 依赖: Filter, Filter.eventually_pure, Kernel, Kernel.const_apply, Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq, const_apply, eventually_pure, iIndepFun, iIndepFun_iff_measure_inter_preimage_eq_mul
-/
theorem iIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι -> Type*}
    {m : forall x, MeasurableSpace (β x)} {f : forall i, Ω -> β i} :
    iIndepFun f μ ↔
      forall (S : Finset ι) {sets : forall i : ι, Set (β i)} (_H : forall i, i in S -> MeasurableSet[m i] (sets i)),
        μ (⋂ i in S, f i ⁻¹' sets i) = ∏ i in S, μ (f i ⁻¹' sets i) := by
  simp only [iIndepFun, Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul, ae_dirac_eq,
    Filter.eventually_pure, Kernel.const_apply]

alias ⟨iIndepFun.measure_inter_preimage_eq_mul, _⟩ := iIndepFun_iff_measure_inter_preimage_eq_mul

/--
theorem `iIndepFun_congr` / 定理 `iIndepFun_congr`

English:
theorem iIndepFun_congr
  statement: {β : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
  proof: Kernel.iIndepFun_congr' (by simp [h])

alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr

nonrec lemma iIndepFun.comp {β γ : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
    {mγ : forall i, MeasurableSpace (γ i)} {f : forall i, Ω -> β i}
    (h : iIndepFun f μ) (g : forall i, β i -> γ i) (hg : for

中文:
定理 iIndepFun_congr
  结论: {β : ι -> 类型} {mβ : 对任意 i, 可测空间 (β i)}
  证明: Kernel.iIndepFun_congr' (by simp [h])

alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr

nonrec lemma iIndepFun.comp {β γ : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
    {mγ : forall i, MeasurableSpace (γ i)} {f : forall i, Ω -> β i}
    (h : iIndepFun f μ) (g : forall i, β i -> γ i) (hg : for

Depends on / 依赖: Kernel, Kernel.iIndepFun_congr, iIndepFun_congr
-/
theorem iIndepFun_congr {β : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
    {f g : Π i, Ω -> β i} (h : forall i, f i =ᵐ[μ] g i) :
    iIndepFun f μ ↔ iIndepFun g μ := Kernel.iIndepFun_congr' (by simp [h])

alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr

nonrec lemma iIndepFun.comp {β γ : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
    {mγ : forall i, MeasurableSpace (γ i)} {f : forall i, Ω -> β i}
    (h : iIndepFun f μ) (g : forall i, β i -> γ i) (hg : forall i, Measurable (g i)) :
    iIndepFun (fun i => g i ∘ f i) μ := h.comp _ hg

nonrec lemma iIndepFun.comp₀ {β γ : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
    {mγ : forall i, MeasurableSpace (γ i)} {f : forall i, Ω -> β i}
    (h : iIndepFun f μ) (g : forall i, β i -> γ i)
    (hf : forall i, AEMeasurable (f i) μ) (hg : forall i, AEMeasurable (g i) (μ.map (f i))) :
    iIndepFun (fun i => g i ∘ f i) μ := h.comp₀ _ (by simp [hf]) (by simp [hg])

/--
theorem `indepFun_iff_indepSet_preimage` / 定理 `indepFun_iff_indepSet_preimage`

English:
theorem indepFun_iff_indepSet_preimage
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  simp only [IndepFun, IndepSet, Kernel.indepFun_iff_indepSet_preimage hf hg]

中文:
定理 indepFun_iff_indepSet_preimage
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  simp only [IndepFun, IndepSet, Kernel.indepFun_iff_indepSet_preimage hf hg]

Depends on / 依赖: IndepFun, IndepSet, Kernel, Kernel.indepFun_iff_indepSet_preimage, indepFun_iff_indepSet_preimage
-/
theorem indepFun_iff_indepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrProbabilityMeasure μ] (hf : Measurable f) (hg : Measurable g) :
    f ⟂ᵢ[μ] g ↔
      forall s t, MeasurableSet s -> MeasurableSet t -> IndepSet (f ⁻¹' s) (g ⁻¹' t) μ := by
  simp only [IndepFun, IndepSet, Kernel.indepFun_iff_indepSet_preimage hf hg]

/--
theorem `indepFun_iff_map_prod_eq_prod_map_map'` / 定理 `indepFun_iff_map_prod_eq_prod_map_map'`

English:
theorem indepFun_iff_map_prod_eq_prod_map_map'
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : Set β} {t : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      μ (f ⁻¹' s) * μ (g ⁻¹' t) = μ.map f s * μ.map g t ∧
      μ (f ⁻¹' s inter g ⁻¹' t) = μ.map (fun ω => (f ω, g ω)) (s ×ˢ t) :=
    ⟨by rw [Measure.map_apply_of

中文:
定理 indepFun_iff_map_prod_eq_prod_map_map'
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : Set β} {t : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      μ (f ⁻¹' s) * μ (g ⁻¹' t) = μ.map f s * μ.map g t ∧
      μ (f ⁻¹' s inter g ⁻¹' t) = μ.map (fun ω => (f ω, g ω)) (s ×ˢ t) :=
    ⟨by rw [Measure.map_apply_of

Depends on / 依赖: MeasurableSet, Measure, Measure.map_apply_of_aemeasurable, Measure.prod_eq, hf.prodMk, hs.prod, indepFun_iff_measure_inter_preimage_eq_mul, map_apply_of_aemeasurable, prodMk, prod_eq
-/
theorem indepFun_iff_map_prod_eq_prod_map_map' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) :
    f ⟂ᵢ[μ] g ↔ μ.map (fun ω => (f ω, g ω)) = (μ.map f).prod (μ.map g) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : Set β} {t : Set β'} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      μ (f ⁻¹' s) * μ (g ⁻¹' t) = μ.map f s * μ.map g t ∧
      μ (f ⁻¹' s inter g ⁻¹' t) = μ.map (fun ω => (f ω, g ω)) (s ×ˢ t) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hf hs, Measure.map_apply_of_aemeasurable hg ht],
      (Measure.map_apply_of_aemeasurable (hf.prodMk hg) (hs.prod ht)).symm⟩
  constructor
  · refine fun h => (Measure.prod_eq fun s t hs ht => ?_).symm
    rw [← (h₀ hs ht).1]; rw [← (h₀ hs ht).2]; rw [h s t hs ht]
  · intro h s t hs ht
    rw [(h₀ hs ht).1]; rw [(h₀ hs ht).2]; rw [h]; rw [Measure.prod_prod]

/--
theorem `indepFun_iff_map_prod_eq_prod_map_map` / 定理 `indepFun_iff_map_prod_eq_prod_map_map`

English:
theorem indepFun_iff_map_prod_eq_prod_map_map
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  apply indepFun_iff_map_prod_eq_prod_map_map' hf hg <;> apply IsFiniteMeasure.toSigmaFinite

alias ⟨IndepFun.map_prod_eq_prod_map_map, _⟩ := indepFun_iff_map_prod_eq_prod_map_map

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : f ⟂ᵢ[μ] g) : g ⟂ᵢ[μ

中文:
定理 indepFun_iff_map_prod_eq_prod_map_map
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  apply indepFun_iff_map_prod_eq_prod_map_map' hf hg <;> apply IsFiniteMeasure.toSigmaFinite

alias ⟨IndepFun.map_prod_eq_prod_map_map, _⟩ := indepFun_iff_map_prod_eq_prod_map_map

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : f ⟂ᵢ[μ] g) : g ⟂ᵢ[μ

Depends on / 依赖: IsFiniteMeasure, IsFiniteMeasure.toSigmaFinite, indepFun_iff_map_prod_eq_prod_map_map, toSigmaFinite
-/
theorem indepFun_iff_map_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsFiniteMeasure μ] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    f ⟂ᵢ[μ] g ↔ μ.map (fun ω => (f ω, g ω)) = (μ.map f).prod (μ.map g) := by
  apply indepFun_iff_map_prod_eq_prod_map_map' hf hg <;> apply IsFiniteMeasure.toSigmaFinite

alias ⟨IndepFun.map_prod_eq_prod_map_map, _⟩ := indepFun_iff_map_prod_eq_prod_map_map

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : f ⟂ᵢ[μ] g) : g ⟂ᵢ[μ] f := hfg.symm

/--
theorem `IndepFun.congr` / 定理 `IndepFun.congr`

English:
theorem IndepFun.congr
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  refine Kernel.IndepFun.congr' hfg ?_ ?_ <;> simpa

中文:
定理 IndepFun.congr
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  refine Kernel.IndepFun.congr' hfg ?_ ?_ <;> simpa

Depends on / 依赖: IndepFun, Kernel, Kernel.IndepFun.congr
-/
theorem IndepFun.congr {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f' : Ω -> β} {g' : Ω -> β'} (hfg : f ⟂ᵢ[μ] g) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    f' ⟂ᵢ[μ] g' := by
  refine Kernel.IndepFun.congr' hfg ?_ ?_ <;> simpa

section Prod

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] {X : Ω -> 𝓧} {Y : Ω' -> 𝓨}

/--
lemma `indepFun_prod` / 引理 `indepFun_prod`

English:
lemma indepFun_prod
  given: (mX : Measurable X) (mY : Measurable Y)
  proof: by
.2 ?_ refine indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
.symm convert! Measure.map_prod_map μ ν mX mY
  · rw [← Function.comp_def, ← Measure.map_map mX measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul]
  · rw [← Function.comp_def, ← Measure.map_map mY meas

中文:
引理 indepFun_prod
  条件: (mX : 可测 X) (mY : 可测 Y)
  证明: by
.2 ?_ refine indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
.symm convert! Measure.map_prod_map μ ν mX mY
  · rw [← Function.comp_def, ← Measure.map_map mX measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul]
  · rw [← Function.comp_def, ← Measure.map_map mY meas

Depends on / 依赖: Function, Function.comp_def, Measure, Measure.map_fst_prod, Measure.map_map, Measure.map_prod_map, Measure.map_snd_prod, comp_def, convert, fun_prop, indepFun_iff_map_prod_eq_prod_map_map, map_fst_prod, map_map, map_prod_map, map_snd_prod, measurable_fst, measurable_snd, measure_univ, one_smul
-/
lemma indepFun_prod (mX : Measurable X) (mY : Measurable Y) :
    (fun ω => X ω.1) ⟂ᵢ[μ.prod ν] (fun ω => Y ω.2) := by
.2 ?_ refine indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
.symm convert! Measure.map_prod_map μ ν mX mY
  · rw [← Function.comp_def, ← Measure.map_map mX measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul]
  · rw [← Function.comp_def, ← Measure.map_map mY measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul]

/--
lemma `indepFun_prod₀` / 引理 `indepFun_prod₀`

English:
lemma indepFun_prod₀
  given: (mX : AEMeasurable X μ) (mY : AEMeasurable Y ν)
  proof: by
  have : (fun ω => mX.mk X ω.1) ⟂ᵢ[μ.prod ν] (fun ω => mY.mk Y ω.2) :=
    indepFun_prod mX.measurable_mk mY.measurable_mk
  refine this.congr ?_ ?_
  · rw [← Function.comp_def, ← Function.comp_def]
    apply ae_eq_comp
    · exact measurable_fst.aemeasurable
    · rw [measurePreserving_fst.map_e

中文:
引理 indepFun_prod₀
  条件: (mX : 几乎处处可测 X μ) (mY : 几乎处处可测 Y ν)
  证明: by
  have : (fun ω => mX.mk X ω.1) ⟂ᵢ[μ.prod ν] (fun ω => mY.mk Y ω.2) :=
    indepFun_prod mX.measurable_mk mY.measurable_mk
  refine this.congr ?_ ?_
  · rw [← Function.comp_def, ← Function.comp_def]
    apply ae_eq_comp
    · exact measurable_fst.aemeasurable
    · rw [measurePreserving_fst.map_e

Depends on / 依赖: AEMeasurable, AEMeasurable.ae_eq_mk, Function, Function.comp_def, ae_eq_comp, ae_eq_mk, aemeasurable, comp_def, indepFun_prod, mX.measurable_mk, mX.mk, mY.measurable_mk, mY.mk, map_eq, measurable_fst, measurable_fst.aemeasurable, measurable_mk, measurable_snd, measurable_snd.aemeasurable, measurePreserving_fst
-/
lemma indepFun_prod₀ (mX : AEMeasurable X μ) (mY : AEMeasurable Y ν) :
    (fun ω => X ω.1) ⟂ᵢ[μ.prod ν] (fun ω => Y ω.2) := by
  have : (fun ω => mX.mk X ω.1) ⟂ᵢ[μ.prod ν] (fun ω => mY.mk Y ω.2) :=
    indepFun_prod mX.measurable_mk mY.measurable_mk
  refine this.congr ?_ ?_
  · rw [← Function.comp_def, ← Function.comp_def]
    apply ae_eq_comp
    · exact measurable_fst.aemeasurable
    · rw [measurePreserving_fst.map_eq]
      exact (AEMeasurable.ae_eq_mk mX).symm
  · rw [← Function.comp_def, ← Function.comp_def]
    apply ae_eq_comp
    · exact measurable_snd.aemeasurable
    · rw [measurePreserving_snd.map_eq]
      exact (AEMeasurable.ae_eq_mk mY).symm

end Prod

/--
theorem `IndepFun.comp` / 定理 `IndepFun.comp`

English:
theorem IndepFun.comp
  statement: {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
  proof: Kernel.IndepFun.comp hfg hφ hψ

中文:
定理 IndepFun.comp
  结论: {_mβ : 可测空间 β} {_mβ' : 可测空间 β'}
  证明: Kernel.IndepFun.comp hfg hφ hψ

Depends on / 依赖: IndepFun, Kernel, Kernel.IndepFun.comp
-/
theorem IndepFun.comp {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β -> γ} {ψ : β' -> γ'}
    (hfg : f ⟂ᵢ[μ] g) (hφ : Measurable φ) (hψ : Measurable ψ) :
    (φ ∘ f) ⟂ᵢ[μ] ψ ∘ g :=
  Kernel.IndepFun.comp hfg hφ hψ

/--
theorem `IndepFun.comp₀` / 定理 `IndepFun.comp₀`

English:
theorem IndepFun.comp₀
  statement: {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
  proof: Kernel.IndepFun.comp₀ hfg (by simp [hf]) (by simp [hg]) (by simp [hφ]) (by simp [hψ])

中文:
定理 IndepFun.comp₀
  结论: {_mβ : 可测空间 β} {_mβ' : 可测空间 β'}
  证明: Kernel.IndepFun.comp₀ hfg (by simp [hf]) (by simp [hg]) (by simp [hφ]) (by simp [hψ])

Depends on / 依赖: IndepFun, Kernel, Kernel.IndepFun.comp
-/
theorem IndepFun.comp₀ {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β -> γ} {ψ : β' -> γ'}
    (hfg : f ⟂ᵢ[μ] g) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hφ : AEMeasurable φ (μ.map f)) (hψ : AEMeasurable ψ (μ.map g)) :
    (φ ∘ f) ⟂ᵢ[μ] (ψ ∘ g) :=
  Kernel.IndepFun.comp₀ hfg (by simp [hf]) (by simp [hg]) (by simp [hφ]) (by simp [hψ])

/--
lemma `indepFun_const_left` / 引理 `indepFun_const_left`

English:
lemma indepFun_const_left
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: Kernel.indepFun_const_left c X

中文:
引理 indepFun_const_left
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: Kernel.indepFun_const_left c X

Depends on / 依赖: Kernel, Kernel.indepFun_const_left, indepFun_const_left
-/
lemma indepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrProbabilityMeasure μ] (c : β) (X : Ω -> β') :
    (fun _ => c) ⟂ᵢ[μ] X :=
  Kernel.indepFun_const_left c X

/--
lemma `indepFun_const_right` / 引理 `indepFun_const_right`

English:
lemma indepFun_const_right
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: Kernel.indepFun_const_right X c

中文:
引理 indepFun_const_right
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: Kernel.indepFun_const_right X c

Depends on / 依赖: Kernel, Kernel.indepFun_const_right, indepFun_const_right
-/
lemma indepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrProbabilityMeasure μ] (X : Ω -> β) (c : β') :
    X ⟂ᵢ[μ] (fun _ => c) :=
  Kernel.indepFun_const_right X c

/--
theorem `IndepFun.neg_right` / 定理 `IndepFun.neg_right`

English:
theorem IndepFun.neg_right
  statement: {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
  proof: hfg.comp measurable_id measurable_neg

中文:
定理 IndepFun.neg_right
  结论: {_mβ : 可测空间 β} {_mβ' : 可测空间 β'} [取负 β']
  证明: hfg.comp measurable_id measurable_neg

Depends on / 依赖: hfg.comp, measurable_id, measurable_neg
-/
theorem IndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : f ⟂ᵢ[μ] g) :
    f ⟂ᵢ[μ] (-g) := hfg.comp measurable_id measurable_neg

/--
theorem `IndepFun.neg_left` / 定理 `IndepFun.neg_left`

English:
theorem IndepFun.neg_left
  statement: {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
  proof: hfg.comp measurable_neg measurable_id

中文:
定理 IndepFun.neg_left
  结论: {_mβ : 可测空间 β} {_mβ' : 可测空间 β'} [取负 β]
  证明: hfg.comp measurable_neg measurable_id

Depends on / 依赖: hfg.comp, measurable_id, measurable_neg
-/
theorem IndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : f ⟂ᵢ[μ] g) :
    (-f) ⟂ᵢ[μ] g := hfg.comp measurable_neg measurable_id

section iIndepFun
variable {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)} {f : forall i, Ω -> β i}

/--
lemma `iIndepFun.isProbabilityMeasure` / 引理 `iIndepFun.isProbabilityMeasure`

English:
lemma iIndepFun.isProbabilityMeasure
  given: (h : iIndepFun f μ)
  statement: IsProbabilityMeasure μ
  proof: ⟨by simpa using h.meas_biInter (S := ∅) (s := fun _ => univ)⟩

中文:
引理 iIndepFun.isProbabilityMeasure
  条件: (h : iIndepFun f μ)
  结论: 是概率测度 μ
  证明: ⟨by simpa using h.meas_biInter (S := ∅) (s := fun _ => univ)⟩

Depends on / 依赖: h.meas_biInter, meas_biInter
-/
lemma iIndepFun.isProbabilityMeasure (h : iIndepFun f μ) : IsProbabilityMeasure μ :=
  ⟨by simpa using h.meas_biInter (S := ∅) (s := fun _ => univ)⟩

/--
lemma `iIndepFun.indepFun_finset` / 引理 `iIndepFun.indepFun_finset`

English:
lemma iIndepFun.indepFun_finset
  statement: (S T : Finset ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas

中文:
引理 iIndepFun.indepFun_finset
  结论: (S T : 有限集 ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_finset, hf_Indep, hf_meas, iIndepFun, indepFun_finset
-/
lemma iIndepFun.indepFun_finset (S T : Finset ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
    (hf_meas : forall i, Measurable (f i)) :
    IndepFun (fun a (i : S) => f i a) (fun a (i : T) => f i a) μ :=
  Kernel.iIndepFun.indepFun_finset S T hST hf_Indep hf_meas

/--
lemma `iIndepFun.indepFun_finset₀` / 引理 `iIndepFun.indepFun_finset₀`

English:
lemma iIndepFun.indepFun_finset₀
  statement: (S T : Finset ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_finset₀ S T hST hf_Indep (by simp [hf_meas])

中文:
引理 iIndepFun.indepFun_finset₀
  结论: (S T : 有限集 ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_finset₀ S T hST hf_Indep (by simp [hf_meas])

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_finset, hf_Indep, hf_meas, iIndepFun
-/
lemma iIndepFun.indepFun_finset₀ (S T : Finset ι) (hST : Disjoint S T) (hf_Indep : iIndepFun f μ)
    (hf_meas : forall i, AEMeasurable (f i) μ) :
    IndepFun (fun a (i : S) => f i a) (fun a (i : T) => f i a) μ :=
  Kernel.iIndepFun.indepFun_finset₀ S T hST hf_Indep (by simp [hf_meas])

/--
lemma `iIndepFun.indepFun_prodMk` / 引理 `iIndepFun.indepFun_prodMk`

English:
lemma iIndepFun.indepFun_prodMk
  statement: (hf_Indep : iIndepFun f μ) (hf_meas : forall i, Measurable (f i))
  proof: Kernel.iIndepFun.indepFun_prodMk hf_Indep hf_meas i j k hik hjk

中文:
引理 iIndepFun.indepFun_prodMk
  结论: (hf_Indep : iIndepFun f μ) (hf_meas : 对任意 i, 可测 (f i))
  证明: Kernel.iIndepFun.indepFun_prodMk hf_Indep hf_meas i j k hik hjk

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_prodMk, hf_Indep, hf_meas, iIndepFun, indepFun_prodMk
-/
lemma iIndepFun.indepFun_prodMk (hf_Indep : iIndepFun f μ) (hf_meas : forall i, Measurable (f i))
    (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (fun a => (f i a, f j a)) (f k) μ :=
  Kernel.iIndepFun.indepFun_prodMk hf_Indep hf_meas i j k hik hjk

/--
lemma `iIndepFun.indepFun_prodMk₀` / 引理 `iIndepFun.indepFun_prodMk₀`

English:
lemma iIndepFun.indepFun_prodMk₀
  statement: (hf_Indep : iIndepFun f μ) (hf_meas : forall i, AEMeasurable (f i) μ)
  proof: Kernel.iIndepFun.indepFun_prodMk₀ hf_Indep (by simp [hf_meas]) i j k hik hjk

中文:
引理 iIndepFun.indepFun_prodMk₀
  结论: (hf_Indep : iIndepFun f μ) (hf_meas : 对任意 i, 几乎处处可测 (f i) μ)
  证明: Kernel.iIndepFun.indepFun_prodMk₀ hf_Indep (by simp [hf_meas]) i j k hik hjk

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_prodMk, hf_Indep, hf_meas, iIndepFun
-/
lemma iIndepFun.indepFun_prodMk₀ (hf_Indep : iIndepFun f μ) (hf_meas : forall i, AEMeasurable (f i) μ)
    (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (fun a => (f i a, f j a)) (f k) μ :=
  Kernel.iIndepFun.indepFun_prodMk₀ hf_Indep (by simp [hf_meas]) i j k hik hjk

/--
lemma `iIndepFun.indepFun_prodMk_prodMk` / 引理 `iIndepFun.indepFun_prodMk_prodMk`

English:
lemma iIndepFun.indepFun_prodMk_prodMk
  statement: (h_indep : iIndepFun f μ) (hf : forall i, Measurable (f i))
  proof: Kernel.iIndepFun.indepFun_prodMk_prodMk h_indep hf i j k l hik hil hjk hjl

中文:
引理 iIndepFun.indepFun_prodMk_prodMk
  结论: (h_indep : iIndepFun f μ) (hf : 对任意 i, 可测 (f i))
  证明: Kernel.iIndepFun.indepFun_prodMk_prodMk h_indep hf i j k l hik hil hjk hjl

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_prodMk_prodMk, h_indep, iIndepFun, indepFun_prodMk_prodMk
-/
lemma iIndepFun.indepFun_prodMk_prodMk (h_indep : iIndepFun f μ) (hf : forall i, Measurable (f i))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (fun a => (f i a, f j a)) (fun a => (f k a, f l a)) μ :=
  Kernel.iIndepFun.indepFun_prodMk_prodMk h_indep hf i j k l hik hil hjk hjl

/--
lemma `iIndepFun.indepFun_prodMk_prodMk₀` / 引理 `iIndepFun.indepFun_prodMk_prodMk₀`

English:
lemma iIndepFun.indepFun_prodMk_prodMk₀
  statement: (h_indep : iIndepFun f μ) (hf : forall i, AEMeasurable (f i) μ)
  proof: Kernel.iIndepFun.indepFun_prodMk_prodMk₀ h_indep (by simp [hf]) i j k l hik hil hjk hjl

中文:
引理 iIndepFun.indepFun_prodMk_prodMk₀
  结论: (h_indep : iIndepFun f μ) (hf : 对任意 i, 几乎处处可测 (f i) μ)
  证明: Kernel.iIndepFun.indepFun_prodMk_prodMk₀ h_indep (by simp [hf]) i j k l hik hil hjk hjl

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_prodMk_prodMk, h_indep, iIndepFun
-/
lemma iIndepFun.indepFun_prodMk_prodMk₀ (h_indep : iIndepFun f μ) (hf : forall i, AEMeasurable (f i) μ)
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (fun a => (f i a, f j a)) (fun a => (f k a, f l a)) μ :=
  Kernel.iIndepFun.indepFun_prodMk_prodMk₀ h_indep (by simp [hf]) i j k l hik hil hjk hjl

/--
lemma `iIndepFun_iff_finset` / 引理 `iIndepFun_iff_finset`

English:
lemma iIndepFun_iff_finset
  statement: iIndepFun f μ ↔ forall s : Finset ι, iIndepFun (s.restrict f) μ where
  proof: h.precomp (g := ((↑) : s -> ι)) Subtype.val_injective
  mpr h := by
    rw [iIndepFun_iff]
    intro s f hs
    have : ⋂ i in s, f i = ⋂ i : s, f i := by ext; simp
    rw [← Finset.prod_coe_sort]; rw [this]
    exact (h s).meas_iInter fun i => hs i i.2

alias ⟨iIndepFun.restrict, _⟩ := iIndepFun_iff

中文:
引理 iIndepFun_iff_finset
  结论: iIndepFun f μ ↔ 对任意 s : 有限集 ι, iIndepFun (s.restrict f) μ where
  证明: h.precomp (g := ((↑) : s -> ι)) Subtype.val_injective
  mpr h := by
    rw [iIndepFun_iff]
    intro s f hs
    have : ⋂ i in s, f i = ⋂ i : s, f i := by ext; simp
    rw [← Finset.prod_coe_sort]; rw [this]
    exact (h s).meas_iInter fun i => hs i i.2

alias ⟨iIndepFun.restrict, _⟩ := iIndepFun_iff

Depends on / 依赖: Subtype, Subtype.val_injective, h.precomp, precomp, val_injective
-/
lemma iIndepFun_iff_finset : iIndepFun f μ ↔ forall s : Finset ι, iIndepFun (s.restrict f) μ where
  mp h s := h.precomp (g := ((↑) : s -> ι)) Subtype.val_injective
  mpr h := by
    rw [iIndepFun_iff]
    intro s f hs
    have : ⋂ i in s, f i = ⋂ i : s, f i := by ext; simp
    rw [← Finset.prod_coe_sort]; rw [this]
    exact (h s).meas_iInter fun i => hs i i.2

alias ⟨iIndepFun.restrict, _⟩ := iIndepFun_iff_finset

/--
theorem `iIndepFun.map_fun_eq_pi_map` / 定理 `iIndepFun.map_fun_eq_pi_map`

English:
theorem iIndepFun.map_fun_eq_pi_map
  statement: [Fintype ι] {β : ι -> Type*}
  proof: by
  have := h.isProbabilityMeasure
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
  have h₀ {s : forall i, Set (β i)} (hm : forall (i : ι), MeasurableSet (s i)) :
      ∏ i : ι, μ (f i ⁻¹' s i) = ∏ i : ι, μ.map (f i) (s i) ∧
      μ (⋂ i : ι, (f i ⁻¹' s i)) = μ.map (fun ω i => f i ω) (univ

中文:
定理 iIndepFun.map_fun_eq_pi_map
  结论: [有限类型 ι] {β : ι -> 类型}
  证明: by
  have := h.isProbabilityMeasure
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
  have h₀ {s : forall i, Set (β i)} (hm : forall (i : ι), MeasurableSet (s i)) :
      ∏ i : ι, μ (f i ⁻¹' s i) = ∏ i : ι, μ.map (f i) (s i) ∧
      μ (⋂ i : ι, (f i ⁻¹' s i)) = μ.map (fun ω i => f i ω) (univ

Depends on / 依赖: MeasurableSet, Measure, Measure.map_apply_of_aemeasurable, aemeasurable_pi_lambda, h.isProbabilityMeasure, iIndepFun_iff_measure_inter_preimage_eq_mul, isProbabilityMeasure, map_apply_of_aemeasurable, univ.pi, univ_pi
-/
theorem iIndepFun.map_fun_eq_pi_map [Fintype ι] {β : ι -> Type*}
    {m : forall i, MeasurableSpace (β i)} {f : Π i, Ω -> β i}
    (hf : forall i, AEMeasurable (f i) μ) (h : iIndepFun f μ) :
    μ.map (fun ω i => f i ω) = Measure.pi (fun i => μ.map (f i)) := by
  have := h.isProbabilityMeasure
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
  have h₀ {s : forall i, Set (β i)} (hm : forall (i : ι), MeasurableSet (s i)) :
      ∏ i : ι, μ (f i ⁻¹' s i) = ∏ i : ι, μ.map (f i) (s i) ∧
      μ (⋂ i : ι, (f i ⁻¹' s i)) = μ.map (fun ω i => f i ω) (univ.pi s) := by
    constructor
    · congr with x
      rw [Measure.map_apply_of_aemeasurable (hf x) (hm x)]
    · rw [Measure.map_apply_of_aemeasurable (aemeasurable_pi_lambda _ fun x => hf x)
        (.univ_pi hm)]
      congr with x
      simp
  refine (Measure.pi_eq fun h' hm => ?_).symm
  rw [← (h₀ hm).1]; rw [← (h₀ hm).2]
  simpa [hm] using h Finset.univ (sets := h')

/--
theorem `iIndepFun_iff_map_fun_eq_pi_map` / 定理 `iIndepFun_iff_map_fun_eq_pi_map`

English:
theorem iIndepFun_iff_map_fun_eq_pi_map
  statement: [Fintype ι] {β : ι -> Type*}
  proof: by
  refine ⟨iIndepFun.map_fun_eq_pi_map hf, ?_⟩
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : forall i, Set (β i)} (hm : forall (i : ι), MeasurableSet (s i)) :
      ∏ i : ι, μ (f i ⁻¹' s i) = ∏ i : ι, μ.map (f i) (s i) ∧
      μ (⋂ i : ι, (f i ⁻¹' s i)) = μ.map (fun

中文:
定理 iIndepFun_iff_map_fun_eq_pi_map
  结论: [有限类型 ι] {β : ι -> 类型}
  证明: by
  refine ⟨iIndepFun.map_fun_eq_pi_map hf, ?_⟩
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : forall i, Set (β i)} (hm : forall (i : ι), MeasurableSet (s i)) :
      ∏ i : ι, μ (f i ⁻¹' s i) = ∏ i : ι, μ.map (f i) (s i) ∧
      μ (⋂ i : ι, (f i ⁻¹' s i)) = μ.map (fun

Depends on / 依赖: MeasurableSet, Measure, Measure.map_apply_of_aemeasurable, aemeasurable_pi_lambda, classical, iIndepFun, iIndepFun.map_fun_eq_pi_map, iIndepFun_iff_measure_inter_preimage_eq_mul, map_apply_of_aemeasurable, map_fun_eq_pi_map, univ.pi, univ_pi
-/
theorem iIndepFun_iff_map_fun_eq_pi_map [Fintype ι] {β : ι -> Type*}
    {m : forall i, MeasurableSpace (β i)} {f : Π i, Ω -> β i} [IsProbabilityMeasure μ]
    (hf : forall i, AEMeasurable (f i) μ) :
    iIndepFun f μ ↔ μ.map (fun ω i => f i ω) = Measure.pi (fun i => μ.map (f i)) := by
  refine ⟨iIndepFun.map_fun_eq_pi_map hf, ?_⟩
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  have h₀ {s : forall i, Set (β i)} (hm : forall (i : ι), MeasurableSet (s i)) :
      ∏ i : ι, μ (f i ⁻¹' s i) = ∏ i : ι, μ.map (f i) (s i) ∧
      μ (⋂ i : ι, (f i ⁻¹' s i)) = μ.map (fun ω i => f i ω) (univ.pi s) := by
    constructor
    · congr with x
      rw [Measure.map_apply_of_aemeasurable (hf x) (hm x)]
    · rw [Measure.map_apply_of_aemeasurable (aemeasurable_pi_lambda _ fun x => hf x)
        (.univ_pi hm)]
      congr with x
      simp
  intro h S s hs
  specialize h₀ (s := fun i => if i in S then s i else univ)
    fun i => by split_ifs with hiS <;> simp [hiS, hs]
  simp only [apply_ite, preimage_univ, measure_univ, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_ite, Finset.filter_univ_mem, iInter_ite, iInter_univ, inter_univ, h,
    Measure.pi_pi] at h₀
  rw [h₀.2]; rw [← h₀.1]

variable {ι : Type*} [Fintype ι] {Ω : ι -> Type*} {mΩ : forall i, MeasurableSpace (Ω i)}
    {μ : (i : ι) -> Measure (Ω i)} [forall i, IsProbabilityMeasure (μ i)]
    {𝓧 : ι -> Type*} [forall i, MeasurableSpace (𝓧 i)] {X : (i : ι) -> Ω i -> 𝓧 i}

/--
lemma `iIndepFun_pi` / 引理 `iIndepFun_pi`

English:
lemma iIndepFun_pi
  given: (mX : forall i, AEMeasurable (X i) (μ i))
  proof: by
.2 ?_ refine iIndepFun_iff_map_fun_eq_pi_map ?_
  · exact fun i => (mX i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)
  rw [Measure.pi_map_pi mX]
  congr
  ext i : 1
  rw [← (measurePreserving_eval μ i).map_eq]; rw [AEMeasurable.map_map_of_aemeasurable]; rw [Function.com

中文:
引理 iIndepFun_pi
  条件: (mX : 对任意 i, 几乎处处可测 (X i) (μ i))
  证明: by
.2 ?_ refine iIndepFun_iff_map_fun_eq_pi_map ?_
  · exact fun i => (mX i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)
  rw [Measure.pi_map_pi mX]
  congr
  ext i : 1
  rw [← (measurePreserving_eval μ i).map_eq]; rw [AEMeasurable.map_map_of_aemeasurable]; rw [Function.com

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, Function, Function.comp_def, Measure, Measure.pi_map_pi, Measure.quasiMeasurePreserving_eval, aemeasurable, comp_def, comp_quasiMeasurePreserving, iIndepFun_iff_map_fun_eq_pi_map, map_eq, map_map_of_aemeasurable, measurable_pi_apply, measurePreserving_eval, pi_map_pi, quasiMeasurePreserving_eval
-/
lemma iIndepFun_pi (mX : forall i, AEMeasurable (X i) (μ i)) :
    iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ) := by
.2 ?_ refine iIndepFun_iff_map_fun_eq_pi_map ?_
  · exact fun i => (mX i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)
  rw [Measure.pi_map_pi mX]
  congr
  ext i : 1
  rw [← (measurePreserving_eval μ i).map_eq]; rw [AEMeasurable.map_map_of_aemeasurable]; rw [Function.comp_def]
  · rw [(measurePreserving_eval μ i).map_eq]
    exact mX i
  · exact (measurable_pi_apply i).aemeasurable

end iIndepFun

section Mul
variable {β : Type*} {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι -> Ω -> β}

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_left` / 引理 `iIndepFun.indepFun_mul_left`

English:
lemma iIndepFun.indepFun_mul_left
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk

@[to_additive]

中文:
引理 iIndepFun.indepFun_mul_left
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_mul_left, hf_indep, hf_meas, iIndepFun, indepFun_mul_left
-/
lemma iIndepFun.indepFun_mul_left (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (f i * f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_mul_left hf_indep hf_meas i j k hik hjk

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_left₀` / 引理 `iIndepFun.indepFun_mul_left₀`

English:
lemma iIndepFun.indepFun_mul_left₀
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_mul_left₀ hf_indep (by simp [hf_meas]) i j k hik hjk

@[to_additive]

中文:
引理 iIndepFun.indepFun_mul_left₀
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_mul_left₀ hf_indep (by simp [hf_meas]) i j k hik hjk

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_mul_left, hf_indep, hf_meas, iIndepFun
-/
lemma iIndepFun.indepFun_mul_left₀ (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, AEMeasurable (f i) μ) (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (f i * f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_mul_left₀ hf_indep (by simp [hf_meas]) i j k hik hjk

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_right` / 引理 `iIndepFun.indepFun_mul_right`

English:
lemma iIndepFun.indepFun_mul_right
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]

中文:
引理 iIndepFun.indepFun_mul_right
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_mul_right, hf_indep, hf_meas, iIndepFun, indepFun_mul_right
-/
lemma iIndepFun.indepFun_mul_right (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hij : i != j) (hik : i != k) :
    IndepFun (f i) (f j * f k) μ :=
  Kernel.iIndepFun.indepFun_mul_right hf_indep hf_meas i j k hij hik

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_right₀` / 引理 `iIndepFun.indepFun_mul_right₀`

English:
lemma iIndepFun.indepFun_mul_right₀
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_mul_right₀ hf_indep (by simp [hf_meas]) i j k hij hik

@[to_additive]

中文:
引理 iIndepFun.indepFun_mul_right₀
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_mul_right₀ hf_indep (by simp [hf_meas]) i j k hij hik

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_mul_right, hf_indep, hf_meas, iIndepFun
-/
lemma iIndepFun.indepFun_mul_right₀ (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, AEMeasurable (f i) μ) (i j k : ι) (hij : i != j) (hik : i != k) :
    IndepFun (f i) (f j * f k) μ :=
  Kernel.iIndepFun.indepFun_mul_right₀ hf_indep (by simp [hf_meas]) i j k hij hik

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_mul` / 引理 `iIndepFun.indepFun_mul_mul`

English:
lemma iIndepFun.indepFun_mul_mul
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

@[to_additive]

中文:
引理 iIndepFun.indepFun_mul_mul
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_mul_mul, hf_indep, hf_meas, iIndepFun, indepFun_mul_mul
-/
lemma iIndepFun.indepFun_mul_mul (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, Measurable (f i))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (f i * f j) (f k * f l) μ :=
  Kernel.iIndepFun.indepFun_mul_mul hf_indep hf_meas i j k l hik hil hjk hjl

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_mul₀` / 引理 `iIndepFun.indepFun_mul_mul₀`

English:
lemma iIndepFun.indepFun_mul_mul₀
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_mul_mul₀ hf_indep (by simp [hf_meas]) i j k l hik hil hjk hjl

中文:
引理 iIndepFun.indepFun_mul_mul₀
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_mul_mul₀ hf_indep (by simp [hf_meas]) i j k l hik hil hjk hjl

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_mul_mul, hf_indep, hf_meas, iIndepFun
-/
lemma iIndepFun.indepFun_mul_mul₀ (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, AEMeasurable (f i) μ)
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (f i * f j) (f k * f l) μ :=
  Kernel.iIndepFun.indepFun_mul_mul₀ hf_indep (by simp [hf_meas]) i j k l hik hil hjk hjl

end Mul

section Div
variable {β : Type*} {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι -> Ω -> β}

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_left` / 引理 `iIndepFun.indepFun_div_left`

English:
lemma iIndepFun.indepFun_div_left
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]

中文:
引理 iIndepFun.indepFun_div_left
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_div_left, hf_indep, hf_meas, iIndepFun, indepFun_div_left
-/
lemma iIndepFun.indepFun_div_left (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (f i / f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_div_left hf_indep hf_meas i j k hik hjk

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_left₀` / 引理 `iIndepFun.indepFun_div_left₀`

English:
lemma iIndepFun.indepFun_div_left₀
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_div_left₀ hf_indep (by simp [hf_meas]) i j k hik hjk

@[to_additive]

中文:
引理 iIndepFun.indepFun_div_left₀
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_div_left₀ hf_indep (by simp [hf_meas]) i j k hik hjk

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_div_left, hf_indep, hf_meas, iIndepFun
-/
lemma iIndepFun.indepFun_div_left₀ (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, AEMeasurable (f i) μ) (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (f i / f j) (f k) μ :=
  Kernel.iIndepFun.indepFun_div_left₀ hf_indep (by simp [hf_meas]) i j k hik hjk

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_right` / 引理 `iIndepFun.indepFun_div_right`

English:
lemma iIndepFun.indepFun_div_right
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]

中文:
引理 iIndepFun.indepFun_div_right
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_div_right, hf_indep, hf_meas, iIndepFun, indepFun_div_right
-/
lemma iIndepFun.indepFun_div_right (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hij : i != j) (hik : i != k) :
    IndepFun (f i) (f j / f k) μ :=
  Kernel.iIndepFun.indepFun_div_right hf_indep hf_meas i j k hij hik

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_right₀` / 引理 `iIndepFun.indepFun_div_right₀`

English:
lemma iIndepFun.indepFun_div_right₀
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_div_right₀ hf_indep (by simp [hf_meas]) i j k hij hik

@[to_additive]

中文:
引理 iIndepFun.indepFun_div_right₀
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_div_right₀ hf_indep (by simp [hf_meas]) i j k hij hik

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_div_right, hf_indep, hf_meas, iIndepFun
-/
lemma iIndepFun.indepFun_div_right₀ (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, AEMeasurable (f i) μ) (i j k : ι) (hij : i != j) (hik : i != k) :
    IndepFun (f i) (f j / f k) μ :=
  Kernel.iIndepFun.indepFun_div_right₀ hf_indep (by simp [hf_meas]) i j k hij hik

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_div` / 引理 `iIndepFun.indepFun_div_div`

English:
lemma iIndepFun.indepFun_div_div
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

@[to_additive]

中文:
引理 iIndepFun.indepFun_div_div
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_div_div, hf_indep, hf_meas, iIndepFun, indepFun_div_div
-/
lemma iIndepFun.indepFun_div_div (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, Measurable (f i))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (f i / f j) (f k / f l) μ :=
  Kernel.iIndepFun.indepFun_div_div hf_indep hf_meas i j k l hik hil hjk hjl

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_div₀` / 引理 `iIndepFun.indepFun_div_div₀`

English:
lemma iIndepFun.indepFun_div_div₀
  statement: (hf_indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_div_div₀ hf_indep (by simp [hf_meas]) i j k l hik hil hjk hjl

中文:
引理 iIndepFun.indepFun_div_div₀
  结论: (hf_indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_div_div₀ hf_indep (by simp [hf_meas]) i j k l hik hil hjk hjl

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_div_div, hf_indep, hf_meas, iIndepFun
-/
lemma iIndepFun.indepFun_div_div₀ (hf_indep : iIndepFun f μ)
    (hf_meas : forall i, AEMeasurable (f i) μ)
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (f i / f j) (f k / f l) μ :=
  Kernel.iIndepFun.indepFun_div_div₀ hf_indep (by simp [hf_meas]) i j k l hik hil hjk hjl

end Div

section CommMonoid
variable {β : Type*} {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι -> Ω -> β}

@[to_additive]
/--
lemma `iIndepFun.indepFun_finsetProd_of_notMem` / 引理 `iIndepFun.indepFun_finsetProd_of_notMem`

English:
lemma iIndepFun.indepFun_finsetProd_of_notMem
  statement: (hf_Indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_finsetProd_of_notMem hf_Indep hf_meas hi

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem := iIndepFun.indepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMe

中文:
引理 iIndepFun.indepFun_finsetProd_of_notMem
  结论: (hf_Indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_finsetProd_of_notMem hf_Indep hf_meas hi

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem := iIndepFun.indepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMe

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_finsetProd_of_notMem, hf_Indep, hf_meas, iIndepFun, indepFun_finsetProd_of_notMem
-/
lemma iIndepFun.indepFun_finsetProd_of_notMem (hf_Indep : iIndepFun f μ)
    (hf_meas : forall i, Measurable (f i)) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j in s, f j) (f i) μ :=
  Kernel.iIndepFun.indepFun_finsetProd_of_notMem hf_Indep hf_meas hi

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem := iIndepFun.indepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem := iIndepFun.indepFun_finsetProd_of_notMem

@[to_additive]
/--
lemma `iIndepFun.indepFun_finsetProd_of_notMem₀` / 引理 `iIndepFun.indepFun_finsetProd_of_notMem₀`

English:
lemma iIndepFun.indepFun_finsetProd_of_notMem₀
  statement: (hf_Indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_finsetProd_of_notMem₀ hf_Indep (by simp [hf_meas]) hi

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem₀ := iIndepFun.indepFun_finsetSum_of_notMem₀

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finse

中文:
引理 iIndepFun.indepFun_finsetProd_of_notMem₀
  结论: (hf_Indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_finsetProd_of_notMem₀ hf_Indep (by simp [hf_meas]) hi

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem₀ := iIndepFun.indepFun_finsetSum_of_notMem₀

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finse

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_finsetProd_of_notMem, hf_Indep, hf_meas, iIndepFun
-/
lemma iIndepFun.indepFun_finsetProd_of_notMem₀ (hf_Indep : iIndepFun f μ)
    (hf_meas : forall i, AEMeasurable (f i) μ) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j in s, f j) (f i) μ :=
  Kernel.iIndepFun.indepFun_finsetProd_of_notMem₀ hf_Indep (by simp [hf_meas]) hi

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem₀ := iIndepFun.indepFun_finsetSum_of_notMem₀

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem₀ := iIndepFun.indepFun_finsetProd_of_notMem₀

@[to_additive]
/--
lemma `iIndepFun.indepFun_prod_range_succ` / 引理 `iIndepFun.indepFun_prod_range_succ`

English:
lemma iIndepFun.indepFun_prod_range_succ
  statement: {f : Nat -> Ω -> β} (hf_Indep : iIndepFun f μ)
  proof: Kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n

@[to_additive]

中文:
引理 iIndepFun.indepFun_prod_range_succ
  结论: {f : 自然数 -> Ω -> β} (hf_Indep : iIndepFun f μ)
  证明: Kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n

@[to_additive]

Depends on / 依赖: Kernel, Kernel.iIndepFun.indepFun_prod_range_succ, hf_Indep, hf_meas, iIndepFun, indepFun_prod_range_succ
-/
lemma iIndepFun.indepFun_prod_range_succ {f : Nat -> Ω -> β} (hf_Indep : iIndepFun f μ)
    (hf_meas : forall i, Measurable (f i)) (n : Nat) : IndepFun (∏ j in Finset.range n, f j) (f n) μ :=
  Kernel.iIndepFun.indepFun_prod_range_succ hf_Indep hf_meas n

@[to_additive]
/--
lemma `iIndepFun.indepFun_prod_range_succ₀` / 引理 `iIndepFun.indepFun_prod_range_succ₀`

English:
lemma iIndepFun.indepFun_prod_range_succ₀
  statement: {f : Nat -> Ω -> β} (hf_Indep : iIndepFun f μ)
  proof: hf_Indep.indepFun_finsetProd_of_notMem₀ hf_meas (by simp)

中文:
引理 iIndepFun.indepFun_prod_range_succ₀
  结论: {f : 自然数 -> Ω -> β} (hf_Indep : iIndepFun f μ)
  证明: hf_Indep.indepFun_finsetProd_of_notMem₀ hf_meas (by simp)

Depends on / 依赖: hf_Indep, hf_Indep.indepFun_finsetProd_of_notMem, hf_meas
-/
lemma iIndepFun.indepFun_prod_range_succ₀ {f : Nat -> Ω -> β} (hf_Indep : iIndepFun f μ)
    (hf_meas : forall i, AEMeasurable (f i) μ) (n : Nat) :
    IndepFun (∏ j in Finset.range n, f j) (f n) μ :=
  hf_Indep.indepFun_finsetProd_of_notMem₀ hf_meas (by simp)

end CommMonoid

/--
theorem `iIndepSet.iIndepFun_indicator` / 定理 `iIndepSet.iIndepFun_indicator`

English:
theorem iIndepSet.iIndepFun_indicator
  statement: [Zero β] [One β] {m : MeasurableSpace β} {s : ι -> Set Ω}
  proof: Kernel.iIndepSet.iIndepFun_indicator hs

中文:
定理 iIndepSet.iIndepFun_indicator
  结论: [零 β] [幺 β] {m : 可测空间 β} {s : ι -> 集合 Ω}
  证明: Kernel.iIndepSet.iIndepFun_indicator hs

Depends on / 依赖: Kernel, Kernel.iIndepSet.iIndepFun_indicator, iIndepFun_indicator, iIndepSet
-/
theorem iIndepSet.iIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β} {s : ι -> Set Ω}
    (hs : iIndepSet s μ) :
    iIndepFun (fun n => (s n).indicator fun _ω => (1 : β)) μ :=
  Kernel.iIndepSet.iIndepFun_indicator hs

/--
lemma `Indep.indicator_indepFun` / 引理 `Indep.indicator_indepFun`

English:
lemma Indep.indicator_indepFun
  statement: {m : MeasurableSpace Ω} {M 𝓧 : Type*}
  proof: Kernel.Indep.indicator_const_indepFun c hA h

中文:
引理 Indep.indicator_indepFun
  结论: {m : 可测空间 Ω} {M 𝓧 : 类型}
  证明: Kernel.Indep.indicator_const_indepFun c hA h

Depends on / 依赖: Kernel, Kernel.Indep.indicator_const_indepFun, indicator_const_indepFun
-/
lemma Indep.indicator_indepFun {m : MeasurableSpace Ω} {M 𝓧 : Type*}
    [Zero M] [MeasurableSpace M] (c : M) {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω}
    {X : Ω -> 𝓧} (hA : MeasurableSet[m] A) (h : Indep m (m𝓧.comap X) μ) :
    (A.indicator (fun _ => c)) ⟂ᵢ[μ] X :=
  Kernel.Indep.indicator_const_indepFun c hA h

end IndepFun

variable {ι Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {X : ι -> Ω -> α} {Y : ι -> Ω -> β} {f : _ -> Set Ω}
  {t : ι -> Set β} {s : Finset ι}

/--
lemma `cond_iInter` / 引理 `cond_iInter`

English:
lemma cond_iInter
  statement: [Finite ι] (hY : forall i, Measurable (Y i))
  proof: by
  have : IsProbabilityMeasure (μ : Measure Ω) := hindep.isProbabilityMeasure
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' in s then Y i' ⁻¹' t i' inter f i' else Y i' ⁻¹' t i'
  calc
    _ = (μ (⋂ i, Y i ⁻¹' t i))⁻¹ * μ ((⋂ i, Y i ⁻¹' t i) inter ⋂ i in s, f i) := by
      rw [

中文:
引理 cond_i整数er
  结论: [有限 ι] (hY : 对任意 i, 可测 (Y i))
  证明: by
  have : IsProbabilityMeasure (μ : Measure Ω) := hindep.isProbabilityMeasure
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' in s then Y i' ⁻¹' t i' inter f i' else Y i' ⁻¹' t i'
  calc
    _ = (μ (⋂ i, Y i ⁻¹' t i))⁻¹ * μ ((⋂ i, Y i ⁻¹' t i) inter ⋂ i in s, f i) := by
      rw [

Depends on / 依赖: IsProbabilityMeasure, Measure, Set.iInter_ite, Set.iInter_uni, classical, cond_apply, hindep, hindep.isProbabilityMeasure, iInter, iInter_ite, iInter_uni, isProbabilityMeasure, nonempty_fintype
-/
lemma cond_iInter [Finite ι] (hY : forall i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω => (X i ω, Y i ω)) μ)
    (hf : forall i in s, MeasurableSet[mα.comap (X i)] (f i))
    (hy : forall i ∉ s, μ (Y i ⁻¹' t i) != 0) (ht : forall i, MeasurableSet (t i)) :
    μ[⋂ i in s, f i | ⋂ i, Y i ⁻¹' t i] = ∏ i in s, μ[f i | Y i in t i] := by
  have : IsProbabilityMeasure (μ : Measure Ω) := hindep.isProbabilityMeasure
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' in s then Y i' ⁻¹' t i' inter f i' else Y i' ⁻¹' t i'
  calc
    _ = (μ (⋂ i, Y i ⁻¹' t i))⁻¹ * μ ((⋂ i, Y i ⁻¹' t i) inter ⋂ i in s, f i) := by
      rw [cond_apply]; exact .iInter fun i => hY i (ht i)
    _ = (μ (⋂ i, Y i ⁻¹' t i))⁻¹ * μ (⋂ i, g i) := by
      congr
      calc
        _ = (⋂ i, Y i ⁻¹' t i) inter ⋂ i, if i in s then f i else .univ := by
          simp only [Set.iInter_ite, Set.iInter_univ, Set.inter_univ]
        _ = ⋂ i, Y i ⁻¹' t i inter (if i in s then f i else .univ) := by rw [Set.iInter_inter_distrib]
        _ = _ := Set.iInter_congr fun i => by by_cases hi : i in s <;> simp [hi, g]
    _ = (∏ i, μ (Y i ⁻¹' t i))⁻¹ * μ (⋂ i, g i) := by
      rw [hindep.meas_iInter]
      exact fun i => ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp⟩
    _ = (∏ i, μ (Y i ⁻¹' t i))⁻¹ * ∏ i, μ (g i) := by
      rw [hindep.meas_iInter]
      intro i
      by_cases hi : i in s <;> simp only [hi, ↓reduceIte, g]
      · obtain ⟨A, hA, hA'⟩ := hf i hi
        exact .inter ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp⟩
          ⟨A ×ˢ Set.univ, hA.prod .univ, by ext; simp [← hA']⟩
      · exact ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp⟩
    _ = ∏ i, (μ (Y i ⁻¹' t i))⁻¹ * μ (g i) := by
      rw [Finset.prod_mul_distrib]; rw [ENNReal.prod_inv_distrib]
exact fun _ _ i _ _ => .inr measure_ne_top _ _
    _ = ∏ i, if i in s then μ[f i | Y i ⁻¹' t i] else 1 := by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i in s
      · simp only [hi, ↓reduceIte, g, cond_apply (hY i (ht i))]
      · simp only [hi, ↓reduceIte, g, ENNReal.inv_mul_cancel (hy i hi) (measure_ne_top μ _)]
    _ = _ := by simp

/--
lemma `iIndepFun.cond` / 引理 `iIndepFun.cond`

English:
lemma iIndepFun.cond
  statement: [Finite ι] (hY : forall i, Measurable (Y i))
  proof: by
  rw [iIndepFun_iff]
  intro s f hf
  convert! cond_iInter hY hindep hf (fun i _ => hy _) ht using 2 with i hi
  simpa using cond_iInter hY hindep (fun j hj => hf _ <| Finset.mem_singleton.1 hj ▸ hi)
    (fun i _ => hy _) ht

中文:
引理 iIndepFun.cond
  结论: [有限 ι] (hY : 对任意 i, 可测 (Y i))
  证明: by
  rw [iIndepFun_iff]
  intro s f hf
  convert! cond_iInter hY hindep hf (fun i _ => hy _) ht using 2 with i hi
  simpa using cond_iInter hY hindep (fun j hj => hf _ <| Finset.mem_singleton.1 hj ▸ hi)
    (fun i _ => hy _) ht

Depends on / 依赖: Finset, Finset.mem_singleton, cond_iInter, convert, hindep, iIndepFun_iff, mem_singleton
-/
lemma iIndepFun.cond [Finite ι] (hY : forall i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω => (X i ω, Y i ω)) μ)
    (hy : forall i, μ (Y i ⁻¹' t i) != 0) (ht : forall i, MeasurableSet (t i)) :
    iIndepFun X μ[|⋂ i, Y i ⁻¹' t i] := by
  rw [iIndepFun_iff]
  intro s f hf
  convert! cond_iInter hY hindep hf (fun i _ => hy _) ht using 2 with i hi
  simpa using cond_iInter hY hindep (fun j hj => hf _ <| Finset.mem_singleton.1 hj ▸ hi)
    (fun i _ => hy _) ht

section Monoid

variable {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]

@[to_additive]
/--
theorem `IndepFun.map_mul_eq_map_mconv_map₀'` / 定理 `IndepFun.map_mul_eq_map_mconv_map₀'`

English:
theorem IndepFun.map_mul_eq_map_mconv_map₀'
  proof: by
  conv in f * g => change (fun x => x.1 * x.2) ∘ (fun ω => (f ω, g ω))
  rw [← measurable_mul.aemeasurable.map_map_of_aemeasurable (hf.prodMk hg)]; rw [(indepFun_iff_map_prod_eq_prod_map_map' hf hg σf σg).mp hfg]; rw [Measure.mconv]

@[to_additive]

中文:
定理 IndepFun.map_mul_eq_map_mconv_map₀'
  证明: by
  conv in f * g => change (fun x => x.1 * x.2) ∘ (fun ω => (f ω, g ω))
  rw [← measurable_mul.aemeasurable.map_map_of_aemeasurable (hf.prodMk hg)]; rw [(indepFun_iff_map_prod_eq_prod_map_map' hf hg σf σg).mp hfg]; rw [Measure.mconv]

@[to_additive]

Depends on / 依赖: Measure, Measure.mconv, aemeasurable, hf.prodMk, indepFun_iff_map_prod_eq_prod_map_map, map_map_of_aemeasurable, measurable_mul, measurable_mul.aemeasurable.map_map_of_aemeasurable, prodMk
-/
theorem IndepFun.map_mul_eq_map_mconv_map₀'
    {f g : Ω -> M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) := by
  conv in f * g => change (fun x => x.1 * x.2) ∘ (fun ω => (f ω, g ω))
  rw [← measurable_mul.aemeasurable.map_map_of_aemeasurable (hf.prodMk hg)]; rw [(indepFun_iff_map_prod_eq_prod_map_map' hf hg σf σg).mp hfg]; rw [Measure.mconv]

@[to_additive]
/--
theorem `IndepFun.map_mul_eq_map_mconv_map'` / 定理 `IndepFun.map_mul_eq_map_mconv_map'`

English:
theorem IndepFun.map_mul_eq_map_mconv_map'
  proof: hfg.map_mul_eq_map_mconv_map₀' hf.aemeasurable hg.aemeasurable σf σg

@[to_additive]

中文:
定理 IndepFun.map_mul_eq_map_mconv_map'
  证明: hfg.map_mul_eq_map_mconv_map₀' hf.aemeasurable hg.aemeasurable σf σg

@[to_additive]

Depends on / 依赖: IsIntegrallyClosed, aemeasurable, hf.aemeasurable, hfg.map_mul_eq_map_mconv_map, hg.aemeasurable, instIsIntegrallyClosed
-/
theorem IndepFun.map_mul_eq_map_mconv_map'
    {f g : Ω -> M} (hf : Measurable f) (hg : Measurable g)
    (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) :=
  hfg.map_mul_eq_map_mconv_map₀' hf.aemeasurable hg.aemeasurable σf σg

@[to_additive]
/--
theorem `IndepFun.map_mul_eq_map_mconv_map₀` / 定理 `IndepFun.map_mul_eq_map_mconv_map₀`

English:
theorem IndepFun.map_mul_eq_map_mconv_map₀
  proof: by
  apply hfg.map_mul_eq_map_mconv_map₀' hf hg
    <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]

中文:
定理 IndepFun.map_mul_eq_map_mconv_map₀
  证明: by
  apply hfg.map_mul_eq_map_mconv_map₀' hf hg
    <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]

Depends on / 依赖: IsFiniteMeasure, IsFiniteMeasure.toSigmaFinite, hfg.map_mul_eq_map_mconv_map, toSigmaFinite
-/
theorem IndepFun.map_mul_eq_map_mconv_map₀
    [IsFiniteMeasure μ] {f g : Ω -> M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) := by
  apply hfg.map_mul_eq_map_mconv_map₀' hf hg
    <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]
/--
theorem `IndepFun.map_mul_eq_map_mconv_map` / 定理 `IndepFun.map_mul_eq_map_mconv_map`

English:
theorem IndepFun.map_mul_eq_map_mconv_map
  proof: hfg.map_mul_eq_map_mconv_map₀ hf.aemeasurable hg.aemeasurable

中文:
定理 IndepFun.map_mul_eq_map_mconv_map
  证明: hfg.map_mul_eq_map_mconv_map₀ hf.aemeasurable hg.aemeasurable

Depends on / 依赖: aemeasurable, hf.aemeasurable, hfg.map_mul_eq_map_mconv_map, hg.aemeasurable
-/
theorem IndepFun.map_mul_eq_map_mconv_map
    [IsFiniteMeasure μ] {f g : Ω -> M} (hf : Measurable f) (hg : Measurable g)
    (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g) :=
  hfg.map_mul_eq_map_mconv_map₀ hf.aemeasurable hg.aemeasurable

end Monoid

end ProbabilityTheory
