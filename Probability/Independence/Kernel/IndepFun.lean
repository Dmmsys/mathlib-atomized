/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Kernel.Indep
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Independence of random variables with respect to a kernel and a measure

A family of random variables is independent if the corresponding `σ`-algebras are independent.
Independence of families of sets and `σ`-algebras is covered in the `Indep` file.
This file deals with independence of random variables specifically.

Note that we define independence with respect to a kernel and a measure. This notion of independence
is a generalization of both independence and conditional independence.
For conditional independence, `κ` is the conditional kernel `ProbabilityTheory.condExpKernel` and
`μ` is the ambient measure. For (non-conditional) independence, `κ = Kernel.const Unit μ` and the
measure is the Dirac measure on `Unit`.

## Main definition

* `ProbabilityTheory.Kernel.iIndepFun`: independence of a family of functions (random variables).
  Variant for two functions: `ProbabilityTheory.Kernel.IndepFun`.
-/

@[expose] public section

open Set MeasureTheory MeasurableSpace

namespace ProbabilityTheory.Kernel

variable {α Ω ι β β' γ γ' : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α} {f : Ω -> β} {g : Ω -> β'}

section Definitions

/--
Definition of `iIndepFun` / `iIndepFun` 的定义

English:
definition iIndepFun
  signature: {β : ι -> Type*} [m : forall x : ι, MeasurableSpace (β x)]
  body: iIndep (m := fun x => MeasurableSpace.comap (f x) (m x)) κ μ

中文:
定义 iIndepFun
  签名: {β : ι -> 类型} [m : 对任意 x : ι, 可测空间 (β x)]
  定义体: iIndep (m := fun x => MeasurableSpace.comap (f x) (m x)) κ μ

Depends on / 依赖: MeasurableSpace, MeasurableSpace.comap, iIndep, volume_tac
-/
def iIndepFun {β : ι -> Type*} [m : forall x : ι, MeasurableSpace (β x)]
    (f : forall x : ι, Ω -> β x) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndep (m := fun x => MeasurableSpace.comap (f x) (m x)) κ μ

/--
Definition of `IndepFun` / `IndepFun` 的定义

English:
definition IndepFun
  signature: [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
  body: Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) κ μ

中文:
定义 IndepFun
  签名: [mβ : 可测空间 β] [mγ : 可测空间 γ]
  定义体: Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) κ μ

Depends on / 依赖: MeasurableSpace, MeasurableSpace.comap, volume_tac
-/
def IndepFun [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω -> β) (g : Ω -> γ) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) κ μ

end Definitions

section ByDefinition

variable {β : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
  {_mα : MeasurableSpace α} {m : ι -> MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α}
  {π : ι -> Set (Set Ω)} {s : ι -> Set Ω} {S : Finset ι} {f : forall x : ι, Ω -> β x}
  {s1 s2 : Set (Set Ω)} {ι' : Type*} {g : ι' -> ι}

/--
lemma `iIndepFun_zero_right` / 引理 `iIndepFun_zero_right`

English:
lemma iIndepFun_zero_right
  statement: {β : ι -> Type*} {m : forall x : ι, MeasurableSpace (β x)}
  proof: by simp [iIndepFun]

中文:
引理 iIndepFun_zero_right
  结论: {β : ι -> 类型} {m : 对任意 x : ι, 可测空间 (β x)}
  证明: by simp [iIndepFun]
-/
@[simp] lemma iIndepFun_zero_right {β : ι -> Type*} {m : forall x : ι, MeasurableSpace (β x)}
    {f : forall x : ι, Ω -> β x} : iIndepFun f κ 0 := by simp [iIndepFun]

/--
lemma `indepFun_zero_right` / 引理 `indepFun_zero_right`

English:
lemma indepFun_zero_right
  statement: {β} [MeasurableSpace β] [MeasurableSpace γ]
  proof: by simp [IndepFun]

中文:
引理 indepFun_zero_right
  结论: {β} [可测空间 β] [可测空间 γ]
  证明: by simp [IndepFun]
-/
@[simp] lemma indepFun_zero_right {β} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω -> β} {g : Ω -> γ} : IndepFun f g κ 0 := by simp [IndepFun]

/--
lemma `indepFun_zero_left` / 引理 `indepFun_zero_left`

English:
lemma indepFun_zero_left
  statement: {β} [MeasurableSpace β] [MeasurableSpace γ]
  proof: by simp [IndepFun]

中文:
引理 indepFun_zero_left
  结论: {β} [可测空间 β] [可测空间 γ]
  证明: by simp [IndepFun]
-/
@[simp] lemma indepFun_zero_left {β} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω -> β} {g : Ω -> γ} : IndepFun f g (0 : Kernel α Ω) μ := by simp [IndepFun]

/--
lemma `iIndepFun_congr` / 引理 `iIndepFun_congr`

English:
lemma iIndepFun_congr
  statement: {β : ι -> Type*} {m : forall x : ι, MeasurableSpace (β x)}
  proof: iIndep_congr h

alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr

中文:
引理 iIndepFun_congr
  结论: {β : ι -> 类型} {m : 对任意 x : ι, 可测空间 (β x)}
  证明: iIndep_congr h

alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr

Depends on / 依赖: iIndep_congr
-/
lemma iIndepFun_congr {β : ι -> Type*} {m : forall x : ι, MeasurableSpace (β x)}
    {f : forall x : ι, Ω -> β x} (h : κ =ᵐ[μ] η) : iIndepFun f κ μ ↔ iIndepFun f η μ :=
  iIndep_congr h

alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr

/--
lemma `indepFun_congr` / 引理 `indepFun_congr`

English:
lemma indepFun_congr
  statement: {β} [MeasurableSpace β] [MeasurableSpace γ]
  proof: indep_congr h

alias ⟨IndepFun.congr, _⟩ := indepFun_congr

@[nontriviality, simp]

中文:
引理 indepFun_congr
  结论: {β} [可测空间 β] [可测空间 γ]
  证明: indep_congr h

alias ⟨IndepFun.congr, _⟩ := indepFun_congr

@[nontriviality, simp]

Depends on / 依赖: indep_congr
-/
lemma indepFun_congr {β} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω -> β} {g : Ω -> γ} (h : κ =ᵐ[μ] η) : IndepFun f g κ μ ↔ IndepFun f g η μ :=
  indep_congr h

alias ⟨IndepFun.congr, _⟩ := indepFun_congr

@[nontriviality, simp]
/--
lemma `iIndepFun.of_subsingleton` / 引理 `iIndepFun.of_subsingleton`

English:
lemma iIndepFun.of_subsingleton
  statement: [Subsingleton ι] {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)}
  proof: by
  simp [iIndepFun]

中文:
引理 iIndepFun.of_subsingleton
  结论: [子单例 ι] {β : ι -> 类型} {m : 对任意 i, 可测空间 (β i)}
  证明: by
  simp [iIndepFun]
-/
lemma iIndepFun.of_subsingleton [Subsingleton ι] {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)}
    {f : forall i, Ω -> β i} [IsMarkovKernel κ] : iIndepFun f κ μ := by
  simp [iIndepFun]

/--
lemma `iIndepFun.iIndep` / 引理 `iIndepFun.iIndep`

English:
lemma iIndepFun.iIndep
  given: (hf : iIndepFun f κ μ)
  proof: hf

中文:
引理 iIndepFun.iIndep
  条件: (hf : iIndepFun f κ μ)
  证明: hf
-/
protected lemma iIndepFun.iIndep (hf : iIndepFun f κ μ) :
    iIndep (fun x => (mβ x).comap (f x)) κ μ := hf

/--
lemma `iIndepFun.ae_isProbabilityMeasure` / 引理 `iIndepFun.ae_isProbabilityMeasure`

English:
lemma iIndepFun.ae_isProbabilityMeasure
  given: (h : iIndepFun f κ μ)
  proof: h.iIndep.ae_isProbabilityMeasure

中文:
引理 iIndepFun.ae_isProbabilityMeasure
  条件: (h : iIndepFun f κ μ)
  证明: h.iIndep.ae_isProbabilityMeasure

Depends on / 依赖: ae_isProbabilityMeasure, h.iIndep.ae_isProbabilityMeasure, iIndep
-/
lemma iIndepFun.ae_isProbabilityMeasure (h : iIndepFun f κ μ) :
    forallᵐ a ∂μ, IsProbabilityMeasure (κ a) :=
  h.iIndep.ae_isProbabilityMeasure

/--
lemma `iIndepFun.meas_biInter` / 引理 `iIndepFun.meas_biInter`

English:
lemma iIndepFun.meas_biInter
  statement: (hf : iIndepFun f κ μ)
  proof: hf.iIndep.meas_biInter hs

中文:
引理 iIndepFun.meas_bi整数er
  结论: (hf : iIndepFun f κ μ)
  证明: hf.iIndep.meas_biInter hs
-/
lemma iIndepFun.meas_biInter (hf : iIndepFun f κ μ)
    (hs : forall i, i in S -> MeasurableSet[(mβ i).comap (f i)] (s i)) :
    forallᵐ a ∂μ, κ a (⋂ i in S, s i) = ∏ i in S, κ a (s i) := hf.iIndep.meas_biInter hs

/--
lemma `iIndepFun.meas_iInter` / 引理 `iIndepFun.meas_iInter`

English:
lemma iIndepFun.meas_iInter
  statement: [Fintype ι] (hf : iIndepFun f κ μ)
  proof: hf.iIndep.meas_iInter hs

中文:
引理 iIndepFun.meas_i整数er
  结论: [有限类型 ι] (hf : iIndepFun f κ μ)
  证明: hf.iIndep.meas_iInter hs
-/
lemma iIndepFun.meas_iInter [Fintype ι] (hf : iIndepFun f κ μ)
    (hs : forall i, MeasurableSet[(mβ i).comap (f i)] (s i)) :
    forallᵐ a ∂μ, κ a (⋂ i, s i) = ∏ i, κ a (s i) := hf.iIndep.meas_iInter hs

/--
lemma `IndepFun.meas_inter` / 引理 `IndepFun.meas_inter`

English:
lemma IndepFun.meas_inter
  statement: {β} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
  proof: hfg _ _ hs ht

中文:
引理 IndepFun.meas_inter
  结论: {β} [mβ : 可测空间 β] [mγ : 可测空间 γ]
  证明: hfg _ _ hs ht
-/
lemma IndepFun.meas_inter {β} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    {f : Ω -> β} {g : Ω -> γ} (hfg : IndepFun f g κ μ)
    {s t : Set Ω} (hs : MeasurableSet[mβ.comap f] s) (ht : MeasurableSet[mγ.comap g] t) :
    forallᵐ a ∂μ, κ a (s inter t) = κ a s * κ a t := hfg _ _ hs ht

/--
lemma `iIndepFun.precomp` / 引理 `iIndepFun.precomp`

English:
lemma iIndepFun.precomp
  given: (hg : Function.Injective g) (h : iIndepFun f κ μ)
  proof: iIndep.precomp hg h

中文:
引理 iIndepFun.precomp
  条件: (hg : 函数.单射 g) (h : iIndepFun f κ μ)
  证明: iIndep.precomp hg h
-/
lemma iIndepFun.precomp (hg : Function.Injective g) (h : iIndepFun f κ μ) :
    iIndepFun (fun i => f (g i)) κ μ :=
  iIndep.precomp hg h

/--
lemma `iIndepFun.of_precomp` / 引理 `iIndepFun.of_precomp`

English:
lemma iIndepFun.of_precomp
  given: (hg : Function.Surjective g) (h : iIndepFun (fun i => f (g i)) κ μ)
  proof: iIndep.of_precomp hg h

中文:
引理 iIndepFun.of_precomp
  条件: (hg : 函数.满射 g) (h : iIndepFun (fun i => f (g i)) κ μ)
  证明: iIndep.of_precomp hg h
-/
lemma iIndepFun.of_precomp (hg : Function.Surjective g) (h : iIndepFun (fun i => f (g i)) κ μ) :
    iIndepFun f κ μ :=
  iIndep.of_precomp hg h

/--
lemma `iIndepFun_precomp_of_bijective` / 引理 `iIndepFun_precomp_of_bijective`

English:
lemma iIndepFun_precomp_of_bijective
  given: (hg : Function.Bijective g)
  proof: ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

中文:
引理 iIndepFun_precomp_of_bijective
  条件: (hg : 函数.双射 g)
  证明: ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

Depends on / 依赖: hg.injective, hg.surjective, injective, of_precomp, precomp, surjective
-/
lemma iIndepFun_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepFun (fun i => f (g i)) κ μ ↔ iIndepFun f κ μ :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

end ByDefinition

/--
theorem `iIndepFun.indepFun` / 定理 `iIndepFun.indepFun`

English:
theorem iIndepFun.indepFun
  statement: {β : ι -> Type*} {m : forall x, MeasurableSpace (β x)} {f : forall i, Ω -> β i}
  proof: hf_Indep.indep hij

中文:
定理 iIndepFun.indepFun
  结论: {β : ι -> 类型} {m : 对任意 x, 可测空间 (β x)} {f : 对任意 i, Ω -> β i}
  证明: hf_Indep.indep hij
-/
theorem iIndepFun.indepFun {β : ι -> Type*} {m : forall x, MeasurableSpace (β x)} {f : forall i, Ω -> β i}
    (hf_Indep : iIndepFun f κ μ) {i j : ι} (hij : i != j) : IndepFun (f i) (f j) κ μ :=
  hf_Indep.indep hij

/--
theorem `indepFun_iff_measure_inter_preimage_eq_mul` / 定理 `indepFun_iff_measure_inter_preimage_eq_mul`

English:
theorem indepFun_iff_measure_inter_preimage_eq_mul
  statement: {mβ : MeasurableSpace β}
  proof: by
  constructor <;> intro h
  · refine fun s t hs ht => h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩; exact h s t hs ht

alias ⟨IndepFun.measure_inter_preimage_eq_mul, _⟩ := indepFun_iff_measure_inter_preimage_eq_mul

中文:
定理 indepFun_iff_measure_inter_preimage_eq_mul
  结论: {mβ : 可测空间 β}
  证明: by
  constructor <;> intro h
  · refine fun s t hs ht => h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩; exact h s t hs ht

alias ⟨IndepFun.measure_inter_preimage_eq_mul, _⟩ := indepFun_iff_measure_inter_preimage_eq_mul
-/
theorem indepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} :
    IndepFun f g κ μ ↔
      forall s t, MeasurableSet s -> MeasurableSet t
        -> forallᵐ a ∂μ, κ a (f ⁻¹' s inter g ⁻¹' t) = κ a (f ⁻¹' s) * κ a (g ⁻¹' t) := by
  constructor <;> intro h
  · refine fun s t hs ht => h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩; exact h s t hs ht

alias ⟨IndepFun.measure_inter_preimage_eq_mul, _⟩ := indepFun_iff_measure_inter_preimage_eq_mul

/--
theorem `iIndepFun_iff_measure_inter_preimage_eq_mul` / 定理 `iIndepFun_iff_measure_inter_preimage_eq_mul`

English:
theorem iIndepFun_iff_measure_inter_preimage_eq_mul
  statement: {ι : Type*} {β : ι -> Type*}
  proof: by
  refine ⟨fun h S sets h_meas => h _ fun i hi_mem => ⟨sets i, h_meas i hi_mem, rfl⟩, ?_⟩
  intro h S setsΩ h_meas
  classical
  let setsβ : forall i : ι, Set (β i) := fun i =>
    dite (i in S) (fun hi_mem => (h_meas i hi_mem).choose) fun _ => Set.univ
  have h_measβ : forall i in S, MeasurableSet[m i] (setsβ i) := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).choose_spec.1
  have h_preim : forall i in S, setsΩ i = f i ⁻¹' setsβ i := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).choose_spec.2.symm
  simp_all

alias ⟨iIndepFun.measure_inter_preimage_eq_mul, _⟩ := iIndepFun_iff_measure_inter_preimage_eq_mul

中文:
定理 iIndepFun_iff_measure_inter_preimage_eq_mul
  结论: {ι : 类型} {β : ι -> 类型}
  证明: by
  refine ⟨fun h S sets h_meas => h _ fun i hi_mem => ⟨sets i, h_meas i hi_mem, rfl⟩, ?_⟩
  intro h S setsΩ h_meas
  classical
  let setsβ : forall i : ι, Set (β i) := fun i =>
    dite (i in S) (fun hi_mem => (h_meas i hi_mem).choose) fun _ => Set.univ
  have h_measβ : forall i in S, MeasurableSet[m i] (setsβ i) := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).choose_spec.1
  have h_preim : forall i in S, setsΩ i = f i ⁻¹' setsβ i := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).choose_spec.2.symm
  simp_all

alias ⟨iIndepFun.measure_inter_preimage_eq_mul, _⟩ := iIndepFun_iff_measure_inter_preimage_eq_mul

Depends on / 依赖: MeasurableSet, Set.univ, choose_spec, classical, dif_pos, h_meas, h_preim, hi_me, hi_mem, simp_rw
-/
theorem iIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι -> Type*}
    (m : forall x, MeasurableSpace (β x)) (f : forall i, Ω -> β i) :
    iIndepFun f κ μ ↔
      forall (S : Finset ι) {sets : forall i : ι, Set (β i)} (_H : forall i, i in S -> MeasurableSet[m i] (sets i)),
        forallᵐ a ∂μ, κ a (⋂ i in S, (f i) ⁻¹' (sets i)) = ∏ i in S, κ a ((f i) ⁻¹' (sets i)) := by
  refine ⟨fun h S sets h_meas => h _ fun i hi_mem => ⟨sets i, h_meas i hi_mem, rfl⟩, ?_⟩
  intro h S setsΩ h_meas
  classical
  let setsβ : forall i : ι, Set (β i) := fun i =>
    dite (i in S) (fun hi_mem => (h_meas i hi_mem).choose) fun _ => Set.univ
  have h_measβ : forall i in S, MeasurableSet[m i] (setsβ i) := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).choose_spec.1
  have h_preim : forall i in S, setsΩ i = f i ⁻¹' setsβ i := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).choose_spec.2.symm
  simp_all

alias ⟨iIndepFun.measure_inter_preimage_eq_mul, _⟩ := iIndepFun_iff_measure_inter_preimage_eq_mul

/--
theorem `iIndepFun.congr'` / 定理 `iIndepFun.congr'`

English:
theorem iIndepFun.congr'
  statement: {β : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
  proof: by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro S sets hmeas
  have : forallᵐ a ∂μ, forall i in S, f i =ᵐ[κ a] g i :=
    (ae_ball_iff (Finset.countable_toSet S)).2 (fun i hi => h i)
  filter_upwards [this, hf S hmeas] with a ha h'a
  have A i (hi : i in S) : (κ a) (g i ⁻¹' sets i) = (κ a) (f i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [ha i hi] with ω hω
    change (g i ω in sets i) = (f i ω in sets i)
    simp [hω]
  have B : (κ a) (⋂ i in S, g i ⁻¹' sets i) = (κ a) (⋂ i in S, f i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [(ae_ball_iff (Finset.countable_toSet S)).2 ha] with ω hω
    change (ω in ⋂ i in S, g i ⁻¹' sets i) = (ω in ⋂ i in S, f i ⁻¹' sets i)
    simp +contextual [hω]
  convert! h'a using 2 with i hi
  exact A i hi

中文:
定理 iIndepFun.congr'
  结论: {β : ι -> 类型} {mβ : 对任意 i, 可测空间 (β i)}
  证明: by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro S sets hmeas
  have : forallᵐ a ∂μ, forall i in S, f i =ᵐ[κ a] g i :=
    (ae_ball_iff (Finset.countable_toSet S)).2 (fun i hi => h i)
  filter_upwards [this, hf S hmeas] with a ha h'a
  have A i (hi : i in S) : (κ a) (g i ⁻¹' sets i) = (κ a) (f i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [ha i hi] with ω hω
    change (g i ω in sets i) = (f i ω in sets i)
    simp [hω]
  have B : (κ a) (⋂ i in S, g i ⁻¹' sets i) = (κ a) (⋂ i in S, f i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [(ae_ball_iff (Finset.countable_toSet S)).2 ha] with ω hω
    change (ω in ⋂ i in S, g i ⁻¹' sets i) = (ω in ⋂ i in S, f i ⁻¹' sets i)
    simp +contextual [hω]
  convert! h'a using 2 with i hi
  exact A i hi

Depends on / 依赖: Finset, Finset.countable_toSet, ae_ball_iff, countable_toSet, filter_upwards, iIndepFun_iff_measure_inter_preimage_eq_mul, measure_congr
-/
theorem iIndepFun.congr' {β : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
    {f g : Π i, Ω -> β i} (hf : iIndepFun f κ μ)
    (h : forall i, forallᵐ a ∂μ, f i =ᵐ[κ a] g i) :
    iIndepFun g κ μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro S sets hmeas
  have : forallᵐ a ∂μ, forall i in S, f i =ᵐ[κ a] g i :=
    (ae_ball_iff (Finset.countable_toSet S)).2 (fun i hi => h i)
  filter_upwards [this, hf S hmeas] with a ha h'a
  have A i (hi : i in S) : (κ a) (g i ⁻¹' sets i) = (κ a) (f i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [ha i hi] with ω hω
    change (g i ω in sets i) = (f i ω in sets i)
    simp [hω]
  have B : (κ a) (⋂ i in S, g i ⁻¹' sets i) = (κ a) (⋂ i in S, f i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [(ae_ball_iff (Finset.countable_toSet S)).2 ha] with ω hω
    change (ω in ⋂ i in S, g i ⁻¹' sets i) = (ω in ⋂ i in S, f i ⁻¹' sets i)
    simp +contextual [hω]
  convert! h'a using 2 with i hi
  exact A i hi

/--
theorem `iIndepFun_congr'` / 定理 `iIndepFun_congr'`

English:
theorem iIndepFun_congr'
  statement: {β : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
  proof: h'.congr' h
  mpr h' := by
    refine h'.congr' fun i => ?_
    filter_upwards [h i] with a ha using ha.symm

中文:
定理 iIndepFun_congr'
  结论: {β : ι -> 类型} {mβ : 对任意 i, 可测空间 (β i)}
  证明: h'.congr' h
  mpr h' := by
    refine h'.congr' fun i => ?_
    filter_upwards [h i] with a ha using ha.symm
-/
theorem iIndepFun_congr' {β : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
    {f g : Π i, Ω -> β i} (h : forall i, forallᵐ a ∂μ, f i =ᵐ[κ a] g i) :
    iIndepFun f κ μ ↔ iIndepFun g κ μ where
  mp h' := h'.congr' h
  mpr h' := by
    refine h'.congr' fun i => ?_
    filter_upwards [h i] with a ha using ha.symm

/--
lemma `iIndepFun.comp` / 引理 `iIndepFun.comp`

English:
lemma iIndepFun.comp
  statement: {β γ : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
  proof: by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  refine fun t s hs => ?_
  have := h t (sets := fun i => g i ⁻¹' (s i)) (fun i a => hg i (hs i a))
  filter_upwards [this] with a ha
  simp_rw [Set.preimage_comp]
  exact ha

中文:
引理 iIndepFun.comp
  结论: {β γ : ι -> 类型} {mβ : 对任意 i, 可测空间 (β i)}
  证明: by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  refine fun t s hs => ?_
  have := h t (sets := fun i => g i ⁻¹' (s i)) (fun i a => hg i (hs i a))
  filter_upwards [this] with a ha
  simp_rw [Set.preimage_comp]
  exact ha

Depends on / 依赖: Set.preimage_comp, filter_upwards, iIndepFun_iff_measure_inter_preimage_eq_mul, preimage_comp, simp_rw
-/
lemma iIndepFun.comp {β γ : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
    {mγ : forall i, MeasurableSpace (γ i)} {f : forall i, Ω -> β i}
    (h : iIndepFun f κ μ) (g : forall i, β i -> γ i) (hg : forall i, Measurable (g i)) :
    iIndepFun (fun i => g i ∘ f i) κ μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  refine fun t s hs => ?_
  have := h t (sets := fun i => g i ⁻¹' (s i)) (fun i a => hg i (hs i a))
  filter_upwards [this] with a ha
  simp_rw [Set.preimage_comp]
  exact ha

/--
lemma `iIndepFun.comp₀` / 引理 `iIndepFun.comp₀`

English:
lemma iIndepFun.comp₀
  statement: {β γ : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
  proof: by
  have h : iIndepFun (fun i => ((hg i).mk (g i)) ∘ f i) κ μ :=
    iIndepFun.comp h (fun i => (hg i).mk (g i)) fun i => (hg i).measurable_mk
  have h_ae i := ae_of_ae_map (hf i) (hg i).ae_eq_mk.symm
  exact iIndepFun.congr' h fun i => Measure.ae_ae_of_ae_comp (h_ae i)

中文:
引理 iIndepFun.comp₀
  结论: {β γ : ι -> 类型} {mβ : 对任意 i, 可测空间 (β i)}
  证明: by
  have h : iIndepFun (fun i => ((hg i).mk (g i)) ∘ f i) κ μ :=
    iIndepFun.comp h (fun i => (hg i).mk (g i)) fun i => (hg i).measurable_mk
  have h_ae i := ae_of_ae_map (hf i) (hg i).ae_eq_mk.symm
  exact iIndepFun.congr' h fun i => Measure.ae_ae_of_ae_comp (h_ae i)

Depends on / 依赖: Measure, Measure.ae_ae_of_ae_comp, ae_ae_of_ae_comp, ae_eq_mk, ae_eq_mk.symm, ae_of_ae_map, h_ae, iIndepFun, iIndepFun.comp, iIndepFun.congr, measurable_mk
-/
lemma iIndepFun.comp₀ {β γ : ι -> Type*} {mβ : forall i, MeasurableSpace (β i)}
    {mγ : forall i, MeasurableSpace (γ i)} {f : forall i, Ω -> β i}
    (h : iIndepFun f κ μ) (g : forall i, β i -> γ i)
    (hf : forall i, AEMeasurable (f i) (κ ∘ₘ μ)) (hg : forall i, AEMeasurable (g i) ((κ ∘ₘ μ).map (f i))) :
    iIndepFun (fun i => g i ∘ f i) κ μ := by
  have h : iIndepFun (fun i => ((hg i).mk (g i)) ∘ f i) κ μ :=
    iIndepFun.comp h (fun i => (hg i).mk (g i)) fun i => (hg i).measurable_mk
  have h_ae i := ae_of_ae_map (hf i) (hg i).ae_eq_mk.symm
  exact iIndepFun.congr' h fun i => Measure.ae_ae_of_ae_comp (h_ae i)

/--
theorem `indepFun_iff_indepSet_preimage` / 定理 `indepFun_iff_indepSet_preimage`

English:
theorem indepFun_iff_indepSet_preimage
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  refine indepFun_iff_measure_inter_preimage_eq_mul.trans ?_
  constructor <;> intro h s t hs ht <;> specialize h s t hs ht
  · rwa [indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) κ μ]
  · rwa [← indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) κ μ]

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : IndepFun f g κ μ) : IndepFun g f κ μ := hfg.symm

中文:
定理 indepFun_iff_indepSet_preimage
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  refine indepFun_iff_measure_inter_preimage_eq_mul.trans ?_
  constructor <;> intro h s t hs ht <;> specialize h s t hs ht
  · rwa [indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) κ μ]
  · rwa [← indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) κ μ]

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : IndepFun f g κ μ) : IndepFun g f κ μ := hfg.symm

Depends on / 依赖: indepFun_iff_measure_inter_preimage_eq_mul, indepFun_iff_measure_inter_preimage_eq_mul.trans, indepSet_iff_measure_inter_eq_mul, specialize
-/
theorem indepFun_iff_indepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrMarkovKernel κ] (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g κ μ ↔
      forall s t, MeasurableSet s -> MeasurableSet t -> IndepSet (f ⁻¹' s) (g ⁻¹' t) κ μ := by
  refine indepFun_iff_measure_inter_preimage_eq_mul.trans ?_
  constructor <;> intro h s t hs ht <;> specialize h s t hs ht
  · rwa [indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) κ μ]
  · rwa [← indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) κ μ]

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : IndepFun f g κ μ) : IndepFun g f κ μ := hfg.symm

/--
theorem `IndepFun.congr'` / 定理 `IndepFun.congr'`

English:
theorem IndepFun.congr'
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg'
  have h1 : f ⁻¹' A =ᵐ[κ a] f' ⁻¹' A := hf'.fun_comp (· in A)
  have h2 : g ⁻¹' B =ᵐ[κ a] g' ⁻¹' B := hg'.fun_comp (· in B)
  rwa [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]

中文:
定理 IndepFun.congr'
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg'
  have h1 : f ⁻¹' A =ᵐ[κ a] f' ⁻¹' A := hf'.fun_comp (· in A)
  have h2 : g ⁻¹' B =ᵐ[κ a] g' ⁻¹' B := hg'.fun_comp (· in B)
  rwa [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]

Depends on / 依赖: filter_upwards, fun_comp, h1.inter, measure_congr
-/
theorem IndepFun.congr' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f' : Ω -> β} {g' : Ω -> β'} (hfg : IndepFun f g κ μ)
    (hf : forallᵐ a ∂μ, f =ᵐ[κ a] f') (hg : forallᵐ a ∂μ, g =ᵐ[κ a] g') :
    IndepFun f' g' κ μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg'
  have h1 : f ⁻¹' A =ᵐ[κ a] f' ⁻¹' A := hf'.fun_comp (· in A)
  have h2 : g ⁻¹' B =ᵐ[κ a] g' ⁻¹' B := hg'.fun_comp (· in B)
  rwa [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]

/--
theorem `IndepFun.comp` / 定理 `IndepFun.comp`

English:
theorem IndepFun.comp
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, Set.preimage_comp.symm⟩
  · exact ⟨ψ ⁻¹' B, hψ hB, Set.preimage_comp.symm⟩

中文:
定理 IndepFun.comp
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, Set.preimage_comp.symm⟩
  · exact ⟨ψ ⁻¹' B, hψ hB, Set.preimage_comp.symm⟩
-/
theorem IndepFun.comp {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {φ : β -> γ} {ψ : β' -> γ'}
    (hfg : IndepFun f g κ μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (φ ∘ f) (ψ ∘ g) κ μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, Set.preimage_comp.symm⟩
  · exact ⟨ψ ⁻¹' B, hψ hB, Set.preimage_comp.symm⟩

/--
theorem `IndepFun.comp₀` / 定理 `IndepFun.comp₀`

English:
theorem IndepFun.comp₀
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  have h : IndepFun ((hφ.mk φ) ∘ f) ((hψ.mk ψ) ∘ g) κ μ := by
    refine IndepFun.comp hfg hφ.measurable_mk hψ.measurable_mk
  have hφ_ae := ae_of_ae_map hf hφ.ae_eq_mk
  have hψ_ae := ae_of_ae_map hg hψ.ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hφ_ae)] with a haφ
    filter_upwards [haφ] with ω hωφ
    simp [hωφ]
  · filter_upwards [Measure.ae_ae_of_ae_comp (hψ_ae)] with a haψ
    filter_upwards [haψ] with ω hωψ
    simp [hωψ]

中文:
定理 IndepFun.comp₀
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  have h : IndepFun ((hφ.mk φ) ∘ f) ((hψ.mk ψ) ∘ g) κ μ := by
    refine IndepFun.comp hfg hφ.measurable_mk hψ.measurable_mk
  have hφ_ae := ae_of_ae_map hf hφ.ae_eq_mk
  have hψ_ae := ae_of_ae_map hg hψ.ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hφ_ae)] with a haφ
    filter_upwards [haφ] with ω hωφ
    simp [hωφ]
  · filter_upwards [Measure.ae_ae_of_ae_comp (hψ_ae)] with a haψ
    filter_upwards [haψ] with ω hωψ
    simp [hωψ]
-/
theorem IndepFun.comp₀ {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {φ : β -> γ} {ψ : β' -> γ'}
    (hfg : IndepFun f g κ μ)
    (hf : AEMeasurable f (κ ∘ₘ μ)) (hg : AEMeasurable g (κ ∘ₘ μ))
    (hφ : AEMeasurable φ ((κ ∘ₘ μ).map f)) (hψ : AEMeasurable ψ ((κ ∘ₘ μ).map g)) :
    IndepFun (φ ∘ f) (ψ ∘ g) κ μ := by
  have h : IndepFun ((hφ.mk φ) ∘ f) ((hψ.mk ψ) ∘ g) κ μ := by
    refine IndepFun.comp hfg hφ.measurable_mk hψ.measurable_mk
  have hφ_ae := ae_of_ae_map hf hφ.ae_eq_mk
  have hψ_ae := ae_of_ae_map hg hψ.ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hφ_ae)] with a haφ
    filter_upwards [haφ] with ω hωφ
    simp [hωφ]
  · filter_upwards [Measure.ae_ae_of_ae_comp (hψ_ae)] with a haψ
    filter_upwards [haψ] with ω hωψ
    simp [hωψ]

/--
lemma `indepFun_const_left` / 引理 `indepFun_const_left`

English:
lemma indepFun_const_left
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: by
  rw [IndepFun]; rw [MeasurableSpace.comap_const]
  exact indep_bot_left _

中文:
引理 indepFun_const_left
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: by
  rw [IndepFun]; rw [MeasurableSpace.comap_const]
  exact indep_bot_left _

Depends on / 依赖: IndepFun, MeasurableSpace, MeasurableSpace.comap_const, comap_const, indep_bot_left
-/
lemma indepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrMarkovKernel κ] (c : β') (X : Ω -> β) :
    IndepFun (fun _ => c) X κ μ := by
  rw [IndepFun]; rw [MeasurableSpace.comap_const]
  exact indep_bot_left _

/--
lemma `indepFun_const_right` / 引理 `indepFun_const_right`

English:
lemma indepFun_const_right
  statement: {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
  proof: (indepFun_const_left c X).symm

中文:
引理 indepFun_const_right
  结论: {mβ : 可测空间 β} {mβ' : 可测空间 β'}
  证明: (indepFun_const_left c X).symm

Depends on / 依赖: indepFun_const_left
-/
lemma indepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrMarkovKernel κ] (X : Ω -> β) (c : β') :
    IndepFun X (fun _ => c) κ μ :=
  (indepFun_const_left c X).symm

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
-/
theorem IndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : IndepFun f g κ μ) :
    IndepFun f (-g) κ μ := hfg.comp measurable_id measurable_neg

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
-/
theorem IndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : IndepFun f g κ μ) :
    IndepFun (-f) g κ μ := hfg.comp measurable_neg measurable_id

/--
theorem `indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map` / 定理 `indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map`

English:
theorem indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
  proof: by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Measure.ext_prod₃_iff]
    intro u s t hu hs ht
    rw [Measure.compProd_apply (hu.prod (hs.prod ht))]; rw [Measure.compProd_apply (hu.prod (hs.prod ht))]
    refine lintegral_congr_ae ?_
    have h_set_eq ω : Prod.mk ω ⁻¹' u ×ˢ s ×ˢ t = if ω in u then s ×ˢ t else ∅ := by ext; simp
    simp_rw [h_set_eq]
    filter_upwards [h s t hs ht] with ω hω
    by_cases hωu : ω in u
    swap; · simp [hωu]
    simp only [hωu, ↓reduceIte]
    rw [map_apply _ (by fun_prop)]; rw [Measure.map_apply (by fun_prop) (hs.prod ht)]; rw [mk_preimage_prod]; rw [hω]; rw [prod_apply_prod]; rw [map_apply' _ (by fun_prop)]; rw [map_apply' _ (by fun_prop)]
    exacts [ht, hs]
  · intro s t hs ht
    rw [Measure.ext_prod₃_iff] at h
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite ?_ ?_ ?_
    · exact Kernel.measurable_coe _ ((hf hs).inter (hg ht))
    · exact (Kernel.measurable_coe _ (hf hs)).mul (Kernel.measurable_coe _ (hg ht))
    intro u hu hμu
    specialize h hu hs ht
    rw [Measure.compProd_apply_prod hu (hs.prod ht)]; rw [Measure.compProd_apply_prod hu (hs.prod ht)] at h
    convert! h with ω ω
    · rw [map_apply' _ (by fun_prop) _ (hs.prod ht), mk_preimage_prod]
    · rw [prod_apply_prod, map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ ht]

中文:
定理 indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
  证明: by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Measure.ext_prod₃_iff]
    intro u s t hu hs ht
    rw [Measure.compProd_apply (hu.prod (hs.prod ht))]; rw [Measure.compProd_apply (hu.prod (hs.prod ht))]
    refine lintegral_congr_ae ?_
    have h_set_eq ω : Prod.mk ω ⁻¹' u ×ˢ s ×ˢ t = if ω in u then s ×ˢ t else ∅ := by ext; simp
    simp_rw [h_set_eq]
    filter_upwards [h s t hs ht] with ω hω
    by_cases hωu : ω in u
    swap; · simp [hωu]
    simp only [hωu, ↓reduceIte]
    rw [map_apply _ (by fun_prop)]; rw [Measure.map_apply (by fun_prop) (hs.prod ht)]; rw [mk_preimage_prod]; rw [hω]; rw [prod_apply_prod]; rw [map_apply' _ (by fun_prop)]; rw [map_apply' _ (by fun_prop)]
    exacts [ht, hs]
  · intro s t hs ht
    rw [Measure.ext_prod₃_iff] at h
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite ?_ ?_ ?_
    · exact Kernel.measurable_coe _ ((hf hs).inter (hg ht))
    · exact (Kernel.measurable_coe _ (hf hs)).mul (Kernel.measurable_coe _ (hg ht))
    intro u hu hμu
    specialize h hu hs ht
    rw [Measure.compProd_apply_prod hu (hs.prod ht)]; rw [Measure.compProd_apply_prod hu (hs.prod ht)] at h
    convert! h with ω ω
    · rw [map_apply' _ (by fun_prop) _ (hs.prod ht), mk_preimage_prod]
    · rw [prod_apply_prod, map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ ht]

Depends on / 依赖: Measure, Measure.compProd_apply, Measure.ext_prod, Prod.mk, classical, compProd_apply, filter_upwards, h_set_eq, hs.prod, hu.prod, indepFun_iff_measure_inter_preimage_eq_mul, lintegral_congr_ae, reduceIte, simp_rw
-/
theorem indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] {f : Ω -> β} {g : Ω -> γ}
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g κ μ ↔ μ otimesₘ κ.map (fun ω => (f ω, g ω)) = μ otimesₘ (κ.map f ×ₖ κ.map g) := by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Measure.ext_prod₃_iff]
    intro u s t hu hs ht
    rw [Measure.compProd_apply (hu.prod (hs.prod ht))]; rw [Measure.compProd_apply (hu.prod (hs.prod ht))]
    refine lintegral_congr_ae ?_
    have h_set_eq ω : Prod.mk ω ⁻¹' u ×ˢ s ×ˢ t = if ω in u then s ×ˢ t else ∅ := by ext; simp
    simp_rw [h_set_eq]
    filter_upwards [h s t hs ht] with ω hω
    by_cases hωu : ω in u
    swap; · simp [hωu]
    simp only [hωu, ↓reduceIte]
    rw [map_apply _ (by fun_prop)]; rw [Measure.map_apply (by fun_prop) (hs.prod ht)]; rw [mk_preimage_prod]; rw [hω]; rw [prod_apply_prod]; rw [map_apply' _ (by fun_prop)]; rw [map_apply' _ (by fun_prop)]
    exacts [ht, hs]
  · intro s t hs ht
    rw [Measure.ext_prod₃_iff] at h
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite ?_ ?_ ?_
    · exact Kernel.measurable_coe _ ((hf hs).inter (hg ht))
    · exact (Kernel.measurable_coe _ (hf hs)).mul (Kernel.measurable_coe _ (hg ht))
    intro u hu hμu
    specialize h hu hs ht
    rw [Measure.compProd_apply_prod hu (hs.prod ht)]; rw [Measure.compProd_apply_prod hu (hs.prod ht)] at h
    convert! h with ω ω
    · rw [map_apply' _ (by fun_prop) _ (hs.prod ht), mk_preimage_prod]
    · rw [prod_apply_prod, map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ ht]

section iIndepFun
variable {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)} {f : forall i, Ω -> β i}


/--
theorem `iIndepFun.indepFun_finset` / 定理 `iIndepFun.indepFun_finset`

English:
theorem iIndepFun.indepFun_finset
  statement: (S T : Finset ι) (hST : Disjoint S T)
  proof: by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : exists (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel hf_Indep.ae_isProbabilityMeasure hμ
  apply IndepFun.congr (Filter.EventuallyEq.symm η_eq)
  -- We introduce π-systems, built from the π-system of boxes which generates `MeasurableSpace.pi`.
  let πSβ := Set.pi (Set.univ : Set S) ''
    Set.pi (Set.univ : Set S) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πS := { s : Set Ω | exists t in πSβ, (fun a (i : S) => f i a) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπS_gen : (MeasurableSpace.pi.comap fun a (i : S) => f i a) = generateFrom πS := by
    rw [generateFrom_pi.symm]; rw [comap_generateFrom]
    congr
  let πTβ := Set.pi (Set.univ : Set T) ''
      Set.pi (Set.univ : Set T) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πT := { s : Set Ω | exists t in πTβ, (fun a (i : T) => f i a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπT_gen : (MeasurableSpace.pi.comap fun a (i : T) => f i a) = generateFrom πT := by
    rw [generateFrom_pi.symm]; rw [comap_generateFrom]
    congr
  -- To prove independence, we prove independence of the generating π-systems.
  refine IndepSets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i))
    (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i)) hπS_pi hπT_pi hπS_gen hπT_gen
    ?_
  rintro _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at hs1 ht1
  rw [← hs2]; rw [← ht2]
  classical
  let sets_s' : forall i : ι, Set (β i) := fun i =>
    dite (i in S) (fun hi => sets_s ⟨i, hi⟩) fun _ => Set.univ
  have h_sets_s'_eq : forall {i} (hi : i in S), sets_s' i = sets_s ⟨i, hi⟩ := by
    intro i hi; simp_rw [sets_s', dif_pos hi]
  have h_sets_s'_univ : forall {i} (_hi : i in T), sets_s' i = Set.univ := by
    intro i hi; simp_rw [sets_s', dif_neg (Finset.disjoint_right.mp hST hi)]
  let sets_t' : forall i : ι, Set (β i) := fun i =>
    dite (i in T) (fun hi => sets_t ⟨i, hi⟩) fun _ => Set.univ
  have h_sets_t'_univ : forall {i} (_hi : i in S), sets_t' i = Set.univ := by
    intro i hi; simp_rw [sets_t', dif_neg (Finset.disjoint_left.mp hST hi)]
  have h_meas_s' : forall i in S, MeasurableSet (sets_s' i) := by
    intro i hi; rw [h_sets_s'_eq hi]; exact hs1 _
  have h_meas_t' : forall i in T, MeasurableSet (sets_t' i) := by
    intro i hi; simp_rw [sets_t', dif_pos hi]; exact ht1 _
  have h_eq_inter_S : (fun (ω : Ω) (i : ↥S) =>
    f (↑i) ω) ⁻¹' Set.pi Set.univ sets_s = ⋂ i in S, f i ⁻¹' sets_s' i := by
    ext1 x
    simp_rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    grind
  have h_eq_inter_T : (fun (ω : Ω) (i : ↥T) => f (↑i) ω) ⁻¹' Set.pi Set.univ sets_t
    = ⋂ i in T, f i ⁻¹' sets_t' i := by
    ext1 x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    constructor <;> intro h
    · intro i hi; simp_rw [sets_t', dif_pos hi]; exact h ⟨i, hi⟩
    · rintro ⟨i, hi⟩; specialize h i hi; simp_rw [sets_t', dif_pos hi] at h; exact h
  replace hf_Indep := hf_Indep.congr η_eq
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf_Indep
  have h_Inter_inter :
    ((⋂ i in S, f i ⁻¹' sets_s' i) inter ⋂ i in T, f i ⁻¹' sets_t' i) =
      ⋂ i in S union T, f i ⁻¹' (sets_s' i inter sets_t' i) := by
    ext1 x
    simp_rw [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
    constructor <;> intro h
    · grind
    · exact ⟨fun i hi => (h i (Or.inl hi)).1, fun i hi => (h i (Or.inr hi)).2⟩
  have h_meas_inter : forall i in S union T, MeasurableSet (sets_s' i inter sets_t' i) := by
    intro i hi_mem
    rw [Finset.mem_union] at hi_mem
    rcases hi_mem with hi_mem | hi_mem
    · rw [h_sets_t'_univ hi_mem, Set.inter_univ]
      exact h_meas_s' i hi_mem
    · rw [h_sets_s'_univ hi_mem, Set.univ_inter]
      exact h_meas_t' i hi_mem
  filter_upwards [hf_Indep S h_meas_s', hf_Indep T h_meas_t', hf_Indep (S union T) h_meas_inter]
    with a h_indepS h_indepT h_indepST
  rw [h_eq_inter_S]; rw [h_eq_inter_T]; rw [h_indepS]; rw [h_indepT]; rw [h_Inter_inter]; rw [h_indepST]; rw [Finset.prod_union hST]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [h_sets_t'_univ hi]; rw [Set.inter_univ]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [h_sets_s'_univ hi]; rw [Set.univ_inter]

中文:
定理 iIndepFun.indepFun_finset
  结论: (S T : 有限集 ι) (hST : Disjoint S T)
  证明: by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : exists (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel hf_Indep.ae_isProbabilityMeasure hμ
  apply IndepFun.congr (Filter.EventuallyEq.symm η_eq)
  -- We introduce π-systems, built from the π-system of boxes which generates `MeasurableSpace.pi`.
  let πSβ := Set.pi (Set.univ : Set S) ''
    Set.pi (Set.univ : Set S) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πS := { s : Set Ω | exists t in πSβ, (fun a (i : S) => f i a) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπS_gen : (MeasurableSpace.pi.comap fun a (i : S) => f i a) = generateFrom πS := by
    rw [generateFrom_pi.symm]; rw [comap_generateFrom]
    congr
  let πTβ := Set.pi (Set.univ : Set T) ''
      Set.pi (Set.univ : Set T) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πT := { s : Set Ω | exists t in πTβ, (fun a (i : T) => f i a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπT_gen : (MeasurableSpace.pi.comap fun a (i : T) => f i a) = generateFrom πT := by
    rw [generateFrom_pi.symm]; rw [comap_generateFrom]
    congr
  -- To prove independence, we prove independence of the generating π-systems.
  refine IndepSets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i))
    (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i)) hπS_pi hπT_pi hπS_gen hπT_gen
    ?_
  rintro _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at hs1 ht1
  rw [← hs2]; rw [← ht2]
  classical
  let sets_s' : forall i : ι, Set (β i) := fun i =>
    dite (i in S) (fun hi => sets_s ⟨i, hi⟩) fun _ => Set.univ
  have h_sets_s'_eq : forall {i} (hi : i in S), sets_s' i = sets_s ⟨i, hi⟩ := by
    intro i hi; simp_rw [sets_s', dif_pos hi]
  have h_sets_s'_univ : forall {i} (_hi : i in T), sets_s' i = Set.univ := by
    intro i hi; simp_rw [sets_s', dif_neg (Finset.disjoint_right.mp hST hi)]
  let sets_t' : forall i : ι, Set (β i) := fun i =>
    dite (i in T) (fun hi => sets_t ⟨i, hi⟩) fun _ => Set.univ
  have h_sets_t'_univ : forall {i} (_hi : i in S), sets_t' i = Set.univ := by
    intro i hi; simp_rw [sets_t', dif_neg (Finset.disjoint_left.mp hST hi)]
  have h_meas_s' : forall i in S, MeasurableSet (sets_s' i) := by
    intro i hi; rw [h_sets_s'_eq hi]; exact hs1 _
  have h_meas_t' : forall i in T, MeasurableSet (sets_t' i) := by
    intro i hi; simp_rw [sets_t', dif_pos hi]; exact ht1 _
  have h_eq_inter_S : (fun (ω : Ω) (i : ↥S) =>
    f (↑i) ω) ⁻¹' Set.pi Set.univ sets_s = ⋂ i in S, f i ⁻¹' sets_s' i := by
    ext1 x
    simp_rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    grind
  have h_eq_inter_T : (fun (ω : Ω) (i : ↥T) => f (↑i) ω) ⁻¹' Set.pi Set.univ sets_t
    = ⋂ i in T, f i ⁻¹' sets_t' i := by
    ext1 x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    constructor <;> intro h
    · intro i hi; simp_rw [sets_t', dif_pos hi]; exact h ⟨i, hi⟩
    · rintro ⟨i, hi⟩; specialize h i hi; simp_rw [sets_t', dif_pos hi] at h; exact h
  replace hf_Indep := hf_Indep.congr η_eq
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf_Indep
  have h_Inter_inter :
    ((⋂ i in S, f i ⁻¹' sets_s' i) inter ⋂ i in T, f i ⁻¹' sets_t' i) =
      ⋂ i in S union T, f i ⁻¹' (sets_s' i inter sets_t' i) := by
    ext1 x
    simp_rw [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
    constructor <;> intro h
    · grind
    · exact ⟨fun i hi => (h i (Or.inl hi)).1, fun i hi => (h i (Or.inr hi)).2⟩
  have h_meas_inter : forall i in S union T, MeasurableSet (sets_s' i inter sets_t' i) := by
    intro i hi_mem
    rw [Finset.mem_union] at hi_mem
    rcases hi_mem with hi_mem | hi_mem
    · rw [h_sets_t'_univ hi_mem, Set.inter_univ]
      exact h_meas_s' i hi_mem
    · rw [h_sets_s'_univ hi_mem, Set.univ_inter]
      exact h_meas_t' i hi_mem
  filter_upwards [hf_Indep S h_meas_s', hf_Indep T h_meas_t', hf_Indep (S union T) h_meas_inter]
    with a h_indepS h_indepT h_indepST
  rw [h_eq_inter_S]; rw [h_eq_inter_T]; rw [h_indepS]; rw [h_indepT]; rw [h_Inter_inter]; rw [h_indepST]; rw [Finset.prod_union hST]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [h_sets_t'_univ hi]; rw [Set.inter_univ]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [h_sets_s'_univ hi]; rw [Set.univ_inter]
-/
theorem iIndepFun.indepFun_finset (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : forall i, Measurable (f i)) :
    IndepFun (fun a (i : S) => f i a) (fun a (i : T) => f i a) κ μ := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : exists (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel hf_Indep.ae_isProbabilityMeasure hμ
  apply IndepFun.congr (Filter.EventuallyEq.symm η_eq)
  -- We introduce π-systems, built from the π-system of boxes which generates `MeasurableSpace.pi`.
  let πSβ := Set.pi (Set.univ : Set S) ''
    Set.pi (Set.univ : Set S) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πS := { s : Set Ω | exists t in πSβ, (fun a (i : S) => f i a) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπS_gen : (MeasurableSpace.pi.comap fun a (i : S) => f i a) = generateFrom πS := by
    rw [generateFrom_pi.symm]; rw [comap_generateFrom]
    congr
  let πTβ := Set.pi (Set.univ : Set T) ''
      Set.pi (Set.univ : Set T) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πT := { s : Set Ω | exists t in πTβ, (fun a (i : T) => f i a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπT_gen : (MeasurableSpace.pi.comap fun a (i : T) => f i a) = generateFrom πT := by
    rw [generateFrom_pi.symm]; rw [comap_generateFrom]
    congr
  -- To prove independence, we prove independence of the generating π-systems.
  refine IndepSets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i))
    (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i)) hπS_pi hπT_pi hπS_gen hπT_gen
    ?_
  rintro _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at hs1 ht1
  rw [← hs2]; rw [← ht2]
  classical
  let sets_s' : forall i : ι, Set (β i) := fun i =>
    dite (i in S) (fun hi => sets_s ⟨i, hi⟩) fun _ => Set.univ
  have h_sets_s'_eq : forall {i} (hi : i in S), sets_s' i = sets_s ⟨i, hi⟩ := by
    intro i hi; simp_rw [sets_s', dif_pos hi]
  have h_sets_s'_univ : forall {i} (_hi : i in T), sets_s' i = Set.univ := by
    intro i hi; simp_rw [sets_s', dif_neg (Finset.disjoint_right.mp hST hi)]
  let sets_t' : forall i : ι, Set (β i) := fun i =>
    dite (i in T) (fun hi => sets_t ⟨i, hi⟩) fun _ => Set.univ
  have h_sets_t'_univ : forall {i} (_hi : i in S), sets_t' i = Set.univ := by
    intro i hi; simp_rw [sets_t', dif_neg (Finset.disjoint_left.mp hST hi)]
  have h_meas_s' : forall i in S, MeasurableSet (sets_s' i) := by
    intro i hi; rw [h_sets_s'_eq hi]; exact hs1 _
  have h_meas_t' : forall i in T, MeasurableSet (sets_t' i) := by
    intro i hi; simp_rw [sets_t', dif_pos hi]; exact ht1 _
  have h_eq_inter_S : (fun (ω : Ω) (i : ↥S) =>
    f (↑i) ω) ⁻¹' Set.pi Set.univ sets_s = ⋂ i in S, f i ⁻¹' sets_s' i := by
    ext1 x
    simp_rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    grind
  have h_eq_inter_T : (fun (ω : Ω) (i : ↥T) => f (↑i) ω) ⁻¹' Set.pi Set.univ sets_t
    = ⋂ i in T, f i ⁻¹' sets_t' i := by
    ext1 x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    constructor <;> intro h
    · intro i hi; simp_rw [sets_t', dif_pos hi]; exact h ⟨i, hi⟩
    · rintro ⟨i, hi⟩; specialize h i hi; simp_rw [sets_t', dif_pos hi] at h; exact h
  replace hf_Indep := hf_Indep.congr η_eq
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf_Indep
  have h_Inter_inter :
    ((⋂ i in S, f i ⁻¹' sets_s' i) inter ⋂ i in T, f i ⁻¹' sets_t' i) =
      ⋂ i in S union T, f i ⁻¹' (sets_s' i inter sets_t' i) := by
    ext1 x
    simp_rw [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
    constructor <;> intro h
    · grind
    · exact ⟨fun i hi => (h i (Or.inl hi)).1, fun i hi => (h i (Or.inr hi)).2⟩
  have h_meas_inter : forall i in S union T, MeasurableSet (sets_s' i inter sets_t' i) := by
    intro i hi_mem
    rw [Finset.mem_union] at hi_mem
    rcases hi_mem with hi_mem | hi_mem
    · rw [h_sets_t'_univ hi_mem, Set.inter_univ]
      exact h_meas_s' i hi_mem
    · rw [h_sets_s'_univ hi_mem, Set.univ_inter]
      exact h_meas_t' i hi_mem
  filter_upwards [hf_Indep S h_meas_s', hf_Indep T h_meas_t', hf_Indep (S union T) h_meas_inter]
    with a h_indepS h_indepT h_indepST
  rw [h_eq_inter_S]; rw [h_eq_inter_T]; rw [h_indepS]; rw [h_indepT]; rw [h_Inter_inter]; rw [h_indepST]; rw [Finset.prod_union hST]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [h_sets_t'_univ hi]; rw [Set.inter_univ]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [h_sets_s'_univ hi]; rw [Set.univ_inter]

/--
theorem `iIndepFun.indepFun_finset₀` / 定理 `iIndepFun.indepFun_finset₀`

English:
theorem iIndepFun.indepFun_finset₀
  statement: (S T : Finset ι) (hST : Disjoint S T)
  proof: by
  have h : IndepFun (fun a (i : S) => (hf_meas i).mk (f i) a)
      (fun a (i : T) => (hf_meas i).mk (f i) a) κ μ := by
    refine iIndepFun.indepFun_finset S T hST ?_ fun i => (hf_meas i).measurable_mk
    exact iIndepFun.congr' hf_Indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · have : forallᵐ (a : α) ∂μ, forall (i : S), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with b hb
    ext i
    exact (hb i).symm
  · have : forallᵐ (a : α) ∂μ, forall (i : T), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with b hb
    ext i
    exact (hb i).symm

中文:
定理 iIndepFun.indepFun_finset₀
  结论: (S T : 有限集 ι) (hST : Disjoint S T)
  证明: by
  have h : IndepFun (fun a (i : S) => (hf_meas i).mk (f i) a)
      (fun a (i : T) => (hf_meas i).mk (f i) a) κ μ := by
    refine iIndepFun.indepFun_finset S T hST ?_ fun i => (hf_meas i).measurable_mk
    exact iIndepFun.congr' hf_Indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · have : forallᵐ (a : α) ∂μ, forall (i : S), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with b hb
    ext i
    exact (hb i).symm
  · have : forallᵐ (a : α) ∂μ, forall (i : T), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with b hb
    ext i
    exact (hb i).symm
-/
theorem iIndepFun.indepFun_finset₀ (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ)) :
    IndepFun (fun a (i : S) => f i a) (fun a (i : T) => f i a) κ μ := by
  have h : IndepFun (fun a (i : S) => (hf_meas i).mk (f i) a)
      (fun a (i : T) => (hf_meas i).mk (f i) a) κ μ := by
    refine iIndepFun.indepFun_finset S T hST ?_ fun i => (hf_meas i).measurable_mk
    exact iIndepFun.congr' hf_Indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · have : forallᵐ (a : α) ∂μ, forall (i : S), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with b hb
    ext i
    exact (hb i).symm
  · have : forallᵐ (a : α) ∂μ, forall (i : T), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with b hb
    ext i
    exact (hb i).symm

/--
theorem `iIndepFun.indepFun_prodMk` / 定理 `iIndepFun.indepFun_prodMk`

English:
theorem iIndepFun.indepFun_prodMk
  statement: (hf_Indep : iIndepFun f κ μ)
  proof: by
  classical
  have h_right :
      f k = (fun p : forall j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩) ∘
        fun a (j : ({k} : Finset ι)) => f j a :=
    rfl
  have h_meas_right : Measurable fun p : forall j : ({k} : Finset ι),
      β j => p ⟨k, Finset.mem_singleton_self k⟩ :=
    measurable_pi_apply _
  let s : Finset ι := {i, j}
  have h_left : (fun ω => (f i ω, f j ω)) = (fun p : forall l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) ∘
        fun a (j : s) => f j a := by
    ext1 a
    simp only
    constructor
  have h_meas_left : Measurable fun p : forall l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) :=
    Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  rw [h_left]; rw [h_right]
  refine (hf_Indep.indepFun_finset s {k} ?_ hf_meas).comp h_meas_left h_meas_right
  rw [Finset.disjoint_singleton_right]
  simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hik.symm, hjk.symm⟩

中文:
定理 iIndepFun.indepFun_prodMk
  结论: (hf_Indep : iIndepFun f κ μ)
  证明: by
  classical
  have h_right :
      f k = (fun p : forall j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩) ∘
        fun a (j : ({k} : Finset ι)) => f j a :=
    rfl
  have h_meas_right : Measurable fun p : forall j : ({k} : Finset ι),
      β j => p ⟨k, Finset.mem_singleton_self k⟩ :=
    measurable_pi_apply _
  let s : Finset ι := {i, j}
  have h_left : (fun ω => (f i ω, f j ω)) = (fun p : forall l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) ∘
        fun a (j : s) => f j a := by
    ext1 a
    simp only
    constructor
  have h_meas_left : Measurable fun p : forall l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) :=
    Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  rw [h_left]; rw [h_right]
  refine (hf_Indep.indepFun_finset s {k} ?_ hf_meas).comp h_meas_left h_meas_right
  rw [Finset.disjoint_singleton_right]
  simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hik.symm, hjk.symm⟩
-/
theorem iIndepFun.indepFun_prodMk (hf_Indep : iIndepFun f κ μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (fun a => (f i a, f j a)) (f k) κ μ := by
  classical
  have h_right :
      f k = (fun p : forall j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩) ∘
        fun a (j : ({k} : Finset ι)) => f j a :=
    rfl
  have h_meas_right : Measurable fun p : forall j : ({k} : Finset ι),
      β j => p ⟨k, Finset.mem_singleton_self k⟩ :=
    measurable_pi_apply _
  let s : Finset ι := {i, j}
  have h_left : (fun ω => (f i ω, f j ω)) = (fun p : forall l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) ∘
        fun a (j : s) => f j a := by
    ext1 a
    simp only
    constructor
  have h_meas_left : Measurable fun p : forall l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) :=
    Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  rw [h_left]; rw [h_right]
  refine (hf_Indep.indepFun_finset s {k} ?_ hf_meas).comp h_meas_left h_meas_right
  rw [Finset.disjoint_singleton_right]
  simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hik.symm, hjk.symm⟩

/--
theorem `iIndepFun.indepFun_prodMk₀` / 定理 `iIndepFun.indepFun_prodMk₀`

English:
theorem iIndepFun.indepFun_prodMk₀
  statement: (hf_Indep : iIndepFun f κ μ)
  proof: by
  have h : IndepFun (fun a => ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      ((hf_meas k).mk (f k)) κ μ := by
    refine iIndepFun.indepFun_prodMk ?_ (fun i => (hf_meas i).measurable_mk) _ _ _ hik hjk
    exact iIndepFun.congr' hf_Indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas j).ae_eq_mk] with a hi hj
    filter_upwards [hi, hj] with ω hωi hωj
    rw [← hωi]; rw [← hωj]
  · exact Measure.ae_ae_of_ae_comp (hf_meas k).ae_eq_mk.symm

中文:
定理 iIndepFun.indepFun_prodMk₀
  结论: (hf_Indep : iIndepFun f κ μ)
  证明: by
  have h : IndepFun (fun a => ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      ((hf_meas k).mk (f k)) κ μ := by
    refine iIndepFun.indepFun_prodMk ?_ (fun i => (hf_meas i).measurable_mk) _ _ _ hik hjk
    exact iIndepFun.congr' hf_Indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas j).ae_eq_mk] with a hi hj
    filter_upwards [hi, hj] with ω hωi hωj
    rw [← hωi]; rw [← hωj]
  · exact Measure.ae_ae_of_ae_comp (hf_meas k).ae_eq_mk.symm
-/
theorem iIndepFun.indepFun_prodMk₀ (hf_Indep : iIndepFun f κ μ)
    (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (fun a => (f i a, f j a)) (f k) κ μ := by
  have h : IndepFun (fun a => ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      ((hf_meas k).mk (f k)) κ μ := by
    refine iIndepFun.indepFun_prodMk ?_ (fun i => (hf_meas i).measurable_mk) _ _ _ hik hjk
    exact iIndepFun.congr' hf_Indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas j).ae_eq_mk] with a hi hj
    filter_upwards [hi, hj] with ω hωi hωj
    rw [← hωi]; rw [← hωj]
  · exact Measure.ae_ae_of_ae_comp (hf_meas k).ae_eq_mk.symm

open Finset in
/--
lemma `iIndepFun.indepFun_prodMk_prodMk` / 引理 `iIndepFun.indepFun_prodMk_prodMk`

English:
lemma iIndepFun.indepFun_prodMk_prodMk
  statement: (hf_indep : iIndepFun f κ μ)
  proof: by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (hf_indep.indepFun_finset {i, j} {k, l} (by aesop) hf_meas).comp (hg i j) (hg k l)

中文:
引理 iIndepFun.indepFun_prodMk_prodMk
  结论: (hf_indep : iIndepFun f κ μ)
  证明: by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (hf_indep.indepFun_finset {i, j} {k, l} (by aesop) hf_meas).comp (hg i j) (hg k l)
-/
lemma iIndepFun.indepFun_prodMk_prodMk (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, Measurable (f i))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (fun a => (f i a, f j a)) (fun a => (f k a, f l a)) κ μ := by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (hf_indep.indepFun_finset {i, j} {k, l} (by aesop) hf_meas).comp (hg i j) (hg k l)

/--
theorem `iIndepFun.indepFun_prodMk_prodMk₀` / 定理 `iIndepFun.indepFun_prodMk_prodMk₀`

English:
theorem iIndepFun.indepFun_prodMk_prodMk₀
  statement: (hf_indep : iIndepFun f κ μ)
  proof: by
  have h : IndepFun (fun a => ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      (fun a => ((hf_meas k).mk (f k) a, (hf_meas l).mk (f l) a)) κ μ := by
    refine iIndepFun.indepFun_prodMk_prodMk ?_ (fun i => (hf_meas i).measurable_mk) _ _ _ _ hik hil
      hjk hjl
    exact iIndepFun.congr' hf_indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas j).ae_eq_mk] with a hi hj
    filter_upwards [hi, hj] with ω hωi hωj
    rw [← hωi]; rw [← hωj]
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas k).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas l).ae_eq_mk] with a hk hl
    filter_upwards [hk, hl] with ω hωk hωl
    rw [← hωk]; rw [← hωl]

中文:
定理 iIndepFun.indepFun_prodMk_prodMk₀
  结论: (hf_indep : iIndepFun f κ μ)
  证明: by
  have h : IndepFun (fun a => ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      (fun a => ((hf_meas k).mk (f k) a, (hf_meas l).mk (f l) a)) κ μ := by
    refine iIndepFun.indepFun_prodMk_prodMk ?_ (fun i => (hf_meas i).measurable_mk) _ _ _ _ hik hil
      hjk hjl
    exact iIndepFun.congr' hf_indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas j).ae_eq_mk] with a hi hj
    filter_upwards [hi, hj] with ω hωi hωj
    rw [← hωi]; rw [← hωj]
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas k).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas l).ae_eq_mk] with a hk hl
    filter_upwards [hk, hl] with ω hωk hωl
    rw [← hωk]; rw [← hωl]
-/
theorem iIndepFun.indepFun_prodMk_prodMk₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (fun a => (f i a, f j a)) (fun a => (f k a, f l a)) κ μ := by
  have h : IndepFun (fun a => ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      (fun a => ((hf_meas k).mk (f k) a, (hf_meas l).mk (f l) a)) κ μ := by
    refine iIndepFun.indepFun_prodMk_prodMk ?_ (fun i => (hf_meas i).measurable_mk) _ _ _ _ hik hil
      hjk hjl
    exact iIndepFun.congr' hf_indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas j).ae_eq_mk] with a hi hj
    filter_upwards [hi, hj] with ω hωi hωj
    rw [← hωi]; rw [← hωj]
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas k).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas l).ae_eq_mk] with a hk hl
    filter_upwards [hk, hl] with ω hωk hωl
    rw [← hωk]; rw [← hωl]

end iIndepFun

section Mul
variable {β : Type*} {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι -> Ω -> β}

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_left` / 引理 `iIndepFun.indepFun_mul_left`

English:
lemma iIndepFun.indepFun_mul_left
  statement: (hf_indep : iIndepFun f κ μ)
  proof: by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]

中文:
引理 iIndepFun.indepFun_mul_left
  结论: (hf_indep : iIndepFun f κ μ)
  证明: by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
-/
lemma iIndepFun.indepFun_mul_left (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (f i * f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_left₀` / 引理 `iIndepFun.indepFun_mul_left₀`

English:
lemma iIndepFun.indepFun_mul_left₀
  statement: (hf_indep : iIndepFun f κ μ)
  proof: by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk₀ hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]

中文:
引理 iIndepFun.indepFun_mul_left₀
  结论: (hf_indep : iIndepFun f κ μ)
  证明: by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk₀ hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
-/
lemma iIndepFun.indepFun_mul_left₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (f i * f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk₀ hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_right` / 引理 `iIndepFun.indepFun_mul_right`

English:
lemma iIndepFun.indepFun_mul_right
  statement: (hf_indep : iIndepFun f κ μ)
  proof: (hf_indep.indepFun_mul_left hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]

中文:
引理 iIndepFun.indepFun_mul_right
  结论: (hf_indep : iIndepFun f κ μ)
  证明: (hf_indep.indepFun_mul_left hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
-/
lemma iIndepFun.indepFun_mul_right (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hij : i != j) (hik : i != k) :
    IndepFun (f i) (f j * f k) κ μ :=
  (hf_indep.indepFun_mul_left hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_right₀` / 引理 `iIndepFun.indepFun_mul_right₀`

English:
lemma iIndepFun.indepFun_mul_right₀
  statement: (hf_indep : iIndepFun f κ μ)
  proof: (hf_indep.indepFun_mul_left₀ hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]

中文:
引理 iIndepFun.indepFun_mul_right₀
  结论: (hf_indep : iIndepFun f κ μ)
  证明: (hf_indep.indepFun_mul_left₀ hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
-/
lemma iIndepFun.indepFun_mul_right₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hij : i != j) (hik : i != k) :
    IndepFun (f i) (f j * f k) κ μ :=
  (hf_indep.indepFun_mul_left₀ hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_mul` / 引理 `iIndepFun.indepFun_mul_mul`

English:
lemma iIndepFun.indepFun_mul_mul
  statement: (hf_indep : iIndepFun f κ μ)
  proof: (hf_indep.indepFun_prodMk_prodMk hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

@[to_additive]

中文:
引理 iIndepFun.indepFun_mul_mul
  结论: (hf_indep : iIndepFun f κ μ)
  证明: (hf_indep.indepFun_prodMk_prodMk hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

@[to_additive]
-/
lemma iIndepFun.indepFun_mul_mul (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, Measurable (f i))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (f i * f j) (f k * f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

@[to_additive]
/--
lemma `iIndepFun.indepFun_mul_mul₀` / 引理 `iIndepFun.indepFun_mul_mul₀`

English:
lemma iIndepFun.indepFun_mul_mul₀
  statement: (hf_indep : iIndepFun f κ μ)
  proof: (hf_indep.indepFun_prodMk_prodMk₀ hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

中文:
引理 iIndepFun.indepFun_mul_mul₀
  结论: (hf_indep : iIndepFun f κ μ)
  证明: (hf_indep.indepFun_prodMk_prodMk₀ hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul
-/
lemma iIndepFun.indepFun_mul_mul₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (f i * f j) (f k * f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk₀ hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

end Mul

section Div
variable {β : Type*} {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι -> Ω -> β}

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_left` / 引理 `iIndepFun.indepFun_div_left`

English:
lemma iIndepFun.indepFun_div_left
  statement: (hf_indep : iIndepFun f κ μ)
  proof: by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]

中文:
引理 iIndepFun.indepFun_div_left
  结论: (hf_indep : iIndepFun f κ μ)
  证明: by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
-/
lemma iIndepFun.indepFun_div_left (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (f i / f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_left₀` / 引理 `iIndepFun.indepFun_div_left₀`

English:
lemma iIndepFun.indepFun_div_left₀
  statement: (hf_indep : iIndepFun f κ μ)
  proof: by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk₀ hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]

中文:
引理 iIndepFun.indepFun_div_left₀
  结论: (hf_indep : iIndepFun f κ μ)
  证明: by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk₀ hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
-/
lemma iIndepFun.indepFun_div_left₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hik : i != k) (hjk : j != k) :
    IndepFun (f i / f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk₀ hf_meas i j k hik hjk
  simpa using! this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_right` / 引理 `iIndepFun.indepFun_div_right`

English:
lemma iIndepFun.indepFun_div_right
  statement: (hf_indep : iIndepFun f κ μ)
  proof: (hf_indep.indepFun_div_left hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]

中文:
引理 iIndepFun.indepFun_div_right
  结论: (hf_indep : iIndepFun f κ μ)
  证明: (hf_indep.indepFun_div_left hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
-/
lemma iIndepFun.indepFun_div_right (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, Measurable (f i)) (i j k : ι) (hij : i != j) (hik : i != k) :
    IndepFun (f i) (f j / f k) κ μ :=
  (hf_indep.indepFun_div_left hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_right₀` / 引理 `iIndepFun.indepFun_div_right₀`

English:
lemma iIndepFun.indepFun_div_right₀
  statement: (hf_indep : iIndepFun f κ μ)
  proof: (hf_indep.indepFun_div_left₀ hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]

中文:
引理 iIndepFun.indepFun_div_right₀
  结论: (hf_indep : iIndepFun f κ μ)
  证明: (hf_indep.indepFun_div_left₀ hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
-/
lemma iIndepFun.indepFun_div_right₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hij : i != j) (hik : i != k) :
    IndepFun (f i) (f j / f k) κ μ :=
  (hf_indep.indepFun_div_left₀ hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_div` / 引理 `iIndepFun.indepFun_div_div`

English:
lemma iIndepFun.indepFun_div_div
  statement: (hf_indep : iIndepFun f κ μ)
  proof: (hf_indep.indepFun_prodMk_prodMk hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

@[to_additive]

中文:
引理 iIndepFun.indepFun_div_div
  结论: (hf_indep : iIndepFun f κ μ)
  证明: (hf_indep.indepFun_prodMk_prodMk hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

@[to_additive]
-/
lemma iIndepFun.indepFun_div_div (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, Measurable (f i))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (f i / f j) (f k / f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

@[to_additive]
/--
lemma `iIndepFun.indepFun_div_div₀` / 引理 `iIndepFun.indepFun_div_div₀`

English:
lemma iIndepFun.indepFun_div_div₀
  statement: (hf_indep : iIndepFun f κ μ)
  proof: (hf_indep.indepFun_prodMk_prodMk₀ hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

中文:
引理 iIndepFun.indepFun_div_div₀
  结论: (hf_indep : iIndepFun f κ μ)
  证明: (hf_indep.indepFun_prodMk_prodMk₀ hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div
-/
lemma iIndepFun.indepFun_div_div₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ))
    (i j k l : ι) (hik : i != k) (hil : i != l) (hjk : j != k) (hjl : j != l) :
    IndepFun (f i / f j) (f k / f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk₀ hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

end Div

section CommMonoid
variable {β : Type*} {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι -> Ω -> β}

@[to_additive]
/--
theorem `iIndepFun.indepFun_finsetProd_of_notMem` / 定理 `iIndepFun.indepFun_finsetProd_of_notMem`

English:
theorem iIndepFun.indepFun_finsetProd_of_notMem
  statement: (hf_Indep : iIndepFun f κ μ)
  proof: by
  have h_right : f i =
    (fun p : ({i} : Finset ι) -> β => p ⟨i, Finset.mem_singleton_self i⟩) ∘
    fun a (j : ({i} : Finset ι)) => f j a := rfl
  have h_meas_right : Measurable fun p : ({i} : Finset ι) -> β =>
      p ⟨i, Finset.mem_singleton_self i⟩ := measurable_pi_apply _
  have h_left : ∏ j in s, f j = (fun p : s -> β => ∏ j, p j) ∘ fun a (j : s) => f j a := by
    ext1 a
    simp only [Function.comp_apply]
    have : (∏ j : ↥s, f (↑j) a) = (∏ j : ↥s, f ↑j) a := by rw [Finset.prod_apply]
    rw [this]; rw [Finset.prod_coe_sort]
  have h_meas_left : Measurable fun p : s -> β => ∏ j, p j :=
    Finset.univ.measurable_fun_prod fun (j : ↥s) (_H : j in Finset.univ) => measurable_pi_apply j
  rw [h_left]; rw [h_right]
  exact
    (hf_Indep.indepFun_finset s {i} (Finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp
      h_meas_left h_meas_right

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem := iIndepFun.indepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem := iIndepFun.indepFun_finsetProd_of_notMem

@[to_additive]

中文:
定理 iIndepFun.indepFun_finsetProd_of_notMem
  结论: (hf_Indep : iIndepFun f κ μ)
  证明: by
  have h_right : f i =
    (fun p : ({i} : Finset ι) -> β => p ⟨i, Finset.mem_singleton_self i⟩) ∘
    fun a (j : ({i} : Finset ι)) => f j a := rfl
  have h_meas_right : Measurable fun p : ({i} : Finset ι) -> β =>
      p ⟨i, Finset.mem_singleton_self i⟩ := measurable_pi_apply _
  have h_left : ∏ j in s, f j = (fun p : s -> β => ∏ j, p j) ∘ fun a (j : s) => f j a := by
    ext1 a
    simp only [Function.comp_apply]
    have : (∏ j : ↥s, f (↑j) a) = (∏ j : ↥s, f ↑j) a := by rw [Finset.prod_apply]
    rw [this]; rw [Finset.prod_coe_sort]
  have h_meas_left : Measurable fun p : s -> β => ∏ j, p j :=
    Finset.univ.measurable_fun_prod fun (j : ↥s) (_H : j in Finset.univ) => measurable_pi_apply j
  rw [h_left]; rw [h_right]
  exact
    (hf_Indep.indepFun_finset s {i} (Finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp
      h_meas_left h_meas_right

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem := iIndepFun.indepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem := iIndepFun.indepFun_finsetProd_of_notMem

@[to_additive]
-/
theorem iIndepFun.indepFun_finsetProd_of_notMem (hf_Indep : iIndepFun f κ μ)
    (hf_meas : forall i, Measurable (f i)) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j in s, f j) (f i) κ μ := by
  have h_right : f i =
    (fun p : ({i} : Finset ι) -> β => p ⟨i, Finset.mem_singleton_self i⟩) ∘
    fun a (j : ({i} : Finset ι)) => f j a := rfl
  have h_meas_right : Measurable fun p : ({i} : Finset ι) -> β =>
      p ⟨i, Finset.mem_singleton_self i⟩ := measurable_pi_apply _
  have h_left : ∏ j in s, f j = (fun p : s -> β => ∏ j, p j) ∘ fun a (j : s) => f j a := by
    ext1 a
    simp only [Function.comp_apply]
    have : (∏ j : ↥s, f (↑j) a) = (∏ j : ↥s, f ↑j) a := by rw [Finset.prod_apply]
    rw [this]; rw [Finset.prod_coe_sort]
  have h_meas_left : Measurable fun p : s -> β => ∏ j, p j :=
    Finset.univ.measurable_fun_prod fun (j : ↥s) (_H : j in Finset.univ) => measurable_pi_apply j
  rw [h_left]; rw [h_right]
  exact
    (hf_Indep.indepFun_finset s {i} (Finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp
      h_meas_left h_meas_right

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem := iIndepFun.indepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem := iIndepFun.indepFun_finsetProd_of_notMem

@[to_additive]
/--
theorem `iIndepFun.indepFun_finsetProd_of_notMem₀` / 定理 `iIndepFun.indepFun_finsetProd_of_notMem₀`

English:
theorem iIndepFun.indepFun_finsetProd_of_notMem₀
  statement: (hf_Indep : iIndepFun f κ μ)
  proof: by
  have h : IndepFun (∏ j in s, (hf_meas j).mk (f j)) ((hf_meas i).mk (f i)) κ μ := by
    refine iIndepFun.indepFun_finsetProd_of_notMem ?_ (fun i => (hf_meas i).measurable_mk) hi
    exact iIndepFun.congr' hf_Indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · have : forallᵐ a ∂μ, forall (i : s), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with ω hω
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => (hω ⟨i, hi⟩).symm
  · exact Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk.symm

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem₀ := iIndepFun.indepFun_finsetSum_of_notMem₀

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem₀ := iIndepFun.indepFun_finsetProd_of_notMem₀


@[to_additive]

中文:
定理 iIndepFun.indepFun_finsetProd_of_notMem₀
  结论: (hf_Indep : iIndepFun f κ μ)
  证明: by
  have h : IndepFun (∏ j in s, (hf_meas j).mk (f j)) ((hf_meas i).mk (f i)) κ μ := by
    refine iIndepFun.indepFun_finsetProd_of_notMem ?_ (fun i => (hf_meas i).measurable_mk) hi
    exact iIndepFun.congr' hf_Indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · have : forallᵐ a ∂μ, forall (i : s), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with ω hω
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => (hω ⟨i, hi⟩).symm
  · exact Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk.symm

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem₀ := iIndepFun.indepFun_finsetSum_of_notMem₀

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem₀ := iIndepFun.indepFun_finsetProd_of_notMem₀


@[to_additive]
-/
theorem iIndepFun.indepFun_finsetProd_of_notMem₀ (hf_Indep : iIndepFun f κ μ)
    (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ)) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j in s, f j) (f i) κ μ := by
  have h : IndepFun (∏ j in s, (hf_meas j).mk (f j)) ((hf_meas i).mk (f i)) κ μ := by
    refine iIndepFun.indepFun_finsetProd_of_notMem ?_ (fun i => (hf_meas i).measurable_mk) hi
    exact iIndepFun.congr' hf_Indep fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · have : forallᵐ a ∂μ, forall (i : s), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i => Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with ω hω
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => (hω ⟨i, hi⟩).symm
  · exact Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk.symm

@[deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_sum_of_notMem₀ := iIndepFun.indepFun_finsetSum_of_notMem₀

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iIndepFun.indepFun_finset_prod_of_notMem₀ := iIndepFun.indepFun_finsetProd_of_notMem₀


@[to_additive]
/--
theorem `iIndepFun.indepFun_prod_range_succ` / 定理 `iIndepFun.indepFun_prod_range_succ`

English:
theorem iIndepFun.indepFun_prod_range_succ
  statement: {f : Nat -> Ω -> β}
  proof: hf_Indep.indepFun_finsetProd_of_notMem hf_meas Finset.notMem_range_self

@[to_additive]

中文:
定理 iIndepFun.indepFun_prod_range_succ
  结论: {f : 自然数 -> Ω -> β}
  证明: hf_Indep.indepFun_finsetProd_of_notMem hf_meas Finset.notMem_range_self

@[to_additive]
-/
theorem iIndepFun.indepFun_prod_range_succ {f : Nat -> Ω -> β}
    (hf_Indep : iIndepFun f κ μ) (hf_meas : forall i, Measurable (f i)) (n : Nat) :
    IndepFun (∏ j in Finset.range n, f j) (f n) κ μ :=
  hf_Indep.indepFun_finsetProd_of_notMem hf_meas Finset.notMem_range_self

@[to_additive]
/--
theorem `iIndepFun.indepFun_prod_range_succ₀` / 定理 `iIndepFun.indepFun_prod_range_succ₀`

English:
theorem iIndepFun.indepFun_prod_range_succ₀
  statement: {f : Nat -> Ω -> β}
  proof: hf_Indep.indepFun_finsetProd_of_notMem₀ hf_meas Finset.notMem_range_self

中文:
定理 iIndepFun.indepFun_prod_range_succ₀
  结论: {f : 自然数 -> Ω -> β}
  证明: hf_Indep.indepFun_finsetProd_of_notMem₀ hf_meas Finset.notMem_range_self
-/
theorem iIndepFun.indepFun_prod_range_succ₀ {f : Nat -> Ω -> β}
    (hf_Indep : iIndepFun f κ μ) (hf_meas : forall i, AEMeasurable (f i) (κ ∘ₘ μ)) (n : Nat) :
    IndepFun (∏ j in Finset.range n, f j) (f n) κ μ :=
  hf_Indep.indepFun_finsetProd_of_notMem₀ hf_meas Finset.notMem_range_self

end CommMonoid

/--
theorem `iIndepSet.iIndepFun_indicator` / 定理 `iIndepSet.iIndepFun_indicator`

English:
theorem iIndepSet.iIndepFun_indicator
  statement: [Zero β] [One β] {m : MeasurableSpace β} {s : ι -> Set Ω}
  proof: by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  rintro S π _hπ
  simp_rw [Set.indicator_const_preimage_eq_union]
  apply hs _ fun i _hi => ?_
  have hsi : MeasurableSet[generateFrom {s i}] (s i) :=
    measurableSet_generateFrom (Set.mem_singleton _)
  refine
    MeasurableSet.union (MeasurableSet.ite' (fun _ => hsi) fun _ => ?_)
      (MeasurableSet.ite' (fun _ => hsi.compl) fun _ => ?_)
  · exact @MeasurableSet.empty _ (generateFrom {s i})
  · exact @MeasurableSet.empty _ (generateFrom {s i})

中文:
定理 iIndepSet.iIndepFun_indicator
  结论: [零 β] [幺 β] {m : 可测空间 β} {s : ι -> 集合 Ω}
  证明: by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  rintro S π _hπ
  simp_rw [Set.indicator_const_preimage_eq_union]
  apply hs _ fun i _hi => ?_
  have hsi : MeasurableSet[generateFrom {s i}] (s i) :=
    measurableSet_generateFrom (Set.mem_singleton _)
  refine
    MeasurableSet.union (MeasurableSet.ite' (fun _ => hsi) fun _ => ?_)
      (MeasurableSet.ite' (fun _ => hsi.compl) fun _ => ?_)
  · exact @MeasurableSet.empty _ (generateFrom {s i})
  · exact @MeasurableSet.empty _ (generateFrom {s i})
-/
theorem iIndepSet.iIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β} {s : ι -> Set Ω}
    (hs : iIndepSet s κ μ) :
    iIndepFun (fun n => (s n).indicator fun _ω => (1 : β)) κ μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  rintro S π _hπ
  simp_rw [Set.indicator_const_preimage_eq_union]
  apply hs _ fun i _hi => ?_
  have hsi : MeasurableSet[generateFrom {s i}] (s i) :=
    measurableSet_generateFrom (Set.mem_singleton _)
  refine
    MeasurableSet.union (MeasurableSet.ite' (fun _ => hsi) fun _ => ?_)
      (MeasurableSet.ite' (fun _ => hsi.compl) fun _ => ?_)
  · exact @MeasurableSet.empty _ (generateFrom {s i})
  · exact @MeasurableSet.empty _ (generateFrom {s i})

/--
lemma `Indep.indicator_const_indepFun` / 引理 `Indep.indicator_const_indepFun`

English:
lemma Indep.indicator_const_indepFun
  statement: {m : MeasurableSpace Ω} {M 𝓧 : Type*}
  proof: indep_of_indep_of_le_left h (measurable_const.indicator hA).comap_le

中文:
引理 Indep.indicator_const_indepFun
  结论: {m : 可测空间 Ω} {M 𝓧 : 类型}
  证明: indep_of_indep_of_le_left h (measurable_const.indicator hA).comap_le

Depends on / 依赖: comap_le, indep_of_indep_of_le_left, indicator, measurable_const, measurable_const.indicator
-/
lemma Indep.indicator_const_indepFun {m : MeasurableSpace Ω} {M 𝓧 : Type*}
    [Zero M] [MeasurableSpace M] (c : M) {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω}
    {X : Ω -> 𝓧} (hA : MeasurableSet[m] A) (h : Indep m (m𝓧.comap X) κ μ) :
    IndepFun (A.indicator (fun _ => c)) X κ μ :=
  indep_of_indep_of_le_left h (measurable_const.indicator hA).comap_le

variable {mβ : MeasurableSpace β} {X : ι -> Ω -> α} {Y : ι -> Ω -> β}
  {f : _ -> Set Ω} {t : ι -> Set β} {s : Finset ι}

/--
lemma `iIndepFun.cond_iInter` / 引理 `iIndepFun.cond_iInter`

English:
lemma iIndepFun.cond_iInter
  statement: [Finite ι] (hY : forall i, Measurable (Y i))
  proof: by
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' in s then Y i' ⁻¹' t i' inter f i' else Y i' ⁻¹' t i'
  have hYt i : MeasurableSet[(mα.prod mβ).comap fun ω => (X i ω, Y i ω)] (Y i ⁻¹' t i) :=
    ⟨.univ ×ˢ t i, .prod .univ (ht _), by ext; simp⟩
  have hg i : MeasurableSet[(mα.prod mβ).comap fun ω => (X i ω, Y i ω)] (g i) := by
    by_cases hi : i in s <;> simp only [hi, ↓reduceIte, g]
    · obtain ⟨A, hA, hA'⟩ := hf i hi
      exact (hYt _).inter ⟨A ×ˢ .univ, hA.prod .univ, by ext; simp [← hA']⟩
    · exact hYt _
  filter_upwards [hy, hindep.ae_isProbabilityMeasure, hindep.meas_iInter hYt, hindep.meas_iInter hg]
    with a hy _ hYt hg
  calc
    _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a ((⋂ i, Y i ⁻¹' t i) inter ⋂ i in s, f i) := by
      rw [cond_apply]; exact .iInter fun i => hY i (ht i)
    _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
      congr 2
      calc
        _ = (⋂ i, Y i ⁻¹' t i) inter ⋂ i, if i in s then f i else .univ := by
          congr 1
          simp only [Set.iInter_ite, Set.iInter_univ, Set.inter_univ]
        _ = ⋂ i, Y i ⁻¹' t i inter (if i in s then f i else .univ) := by rw [Set.iInter_inter_distrib]
        _ = _ := Set.iInter_congr fun i => by by_cases hi : i in s <;> simp [hi, g]
    _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
      rw [hYt]
    _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * ∏ i, κ a (g i) := by
      rw [hg]
    _ = ∏ i, (κ a (Y i ⁻¹' t i))⁻¹ * κ a (g i) := by
      rw [Finset.prod_mul_distrib]; rw [ENNReal.prod_inv_distrib]
exact fun _ _ i _ _ => .inr measure_ne_top _ _
    _ = ∏ i, if i in s then (κ a)[f i | Y i ⁻¹' t i] else 1 := by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i in s
      · simp only [hi, ↓reduceIte, g, cond_apply (hY i (ht i))]
      · simp only [hi, ↓reduceIte, g, ENNReal.inv_mul_cancel (hy i hi) (measure_ne_top _ _)]
    _ = _ := by simp

中文:
引理 iIndepFun.cond_i整数er
  结论: [有限 ι] (hY : 对任意 i, 可测 (Y i))
  证明: by
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' in s then Y i' ⁻¹' t i' inter f i' else Y i' ⁻¹' t i'
  have hYt i : MeasurableSet[(mα.prod mβ).comap fun ω => (X i ω, Y i ω)] (Y i ⁻¹' t i) :=
    ⟨.univ ×ˢ t i, .prod .univ (ht _), by ext; simp⟩
  have hg i : MeasurableSet[(mα.prod mβ).comap fun ω => (X i ω, Y i ω)] (g i) := by
    by_cases hi : i in s <;> simp only [hi, ↓reduceIte, g]
    · obtain ⟨A, hA, hA'⟩ := hf i hi
      exact (hYt _).inter ⟨A ×ˢ .univ, hA.prod .univ, by ext; simp [← hA']⟩
    · exact hYt _
  filter_upwards [hy, hindep.ae_isProbabilityMeasure, hindep.meas_iInter hYt, hindep.meas_iInter hg]
    with a hy _ hYt hg
  calc
    _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a ((⋂ i, Y i ⁻¹' t i) inter ⋂ i in s, f i) := by
      rw [cond_apply]; exact .iInter fun i => hY i (ht i)
    _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
      congr 2
      calc
        _ = (⋂ i, Y i ⁻¹' t i) inter ⋂ i, if i in s then f i else .univ := by
          congr 1
          simp only [Set.iInter_ite, Set.iInter_univ, Set.inter_univ]
        _ = ⋂ i, Y i ⁻¹' t i inter (if i in s then f i else .univ) := by rw [Set.iInter_inter_distrib]
        _ = _ := Set.iInter_congr fun i => by by_cases hi : i in s <;> simp [hi, g]
    _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
      rw [hYt]
    _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * ∏ i, κ a (g i) := by
      rw [hg]
    _ = ∏ i, (κ a (Y i ⁻¹' t i))⁻¹ * κ a (g i) := by
      rw [Finset.prod_mul_distrib]; rw [ENNReal.prod_inv_distrib]
exact fun _ _ i _ _ => .inr measure_ne_top _ _
    _ = ∏ i, if i in s then (κ a)[f i | Y i ⁻¹' t i] else 1 := by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i in s
      · simp only [hi, ↓reduceIte, g, cond_apply (hY i (ht i))]
      · simp only [hi, ↓reduceIte, g, ENNReal.inv_mul_cancel (hy i hi) (measure_ne_top _ _)]
    _ = _ := by simp

Depends on / 依赖: MeasurableSet, classical, hA.prod, nonempty_fintype, reduceIte
-/
lemma iIndepFun.cond_iInter [Finite ι] (hY : forall i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω => (X i ω, Y i ω)) κ μ)
    (hf : forall i in s, MeasurableSet[mα.comap (X i)] (f i))
    (hy : forallᵐ a ∂μ, forall i ∉ s, κ a (Y i ⁻¹' t i) != 0) (ht : forall i, MeasurableSet (t i)) :
    forallᵐ a ∂μ, (κ a)[⋂ i in s, f i | ⋂ i, Y i ⁻¹' t i] = ∏ i in s, (κ a)[f i | Y i in t i] := by
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' in s then Y i' ⁻¹' t i' inter f i' else Y i' ⁻¹' t i'
  have hYt i : MeasurableSet[(mα.prod mβ).comap fun ω => (X i ω, Y i ω)] (Y i ⁻¹' t i) :=
    ⟨.univ ×ˢ t i, .prod .univ (ht _), by ext; simp⟩
  have hg i : MeasurableSet[(mα.prod mβ).comap fun ω => (X i ω, Y i ω)] (g i) := by
    by_cases hi : i in s <;> simp only [hi, ↓reduceIte, g]
    · obtain ⟨A, hA, hA'⟩ := hf i hi
      exact (hYt _).inter ⟨A ×ˢ .univ, hA.prod .univ, by ext; simp [← hA']⟩
    · exact hYt _
  filter_upwards [hy, hindep.ae_isProbabilityMeasure, hindep.meas_iInter hYt, hindep.meas_iInter hg]
    with a hy _ hYt hg
  calc
    _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a ((⋂ i, Y i ⁻¹' t i) inter ⋂ i in s, f i) := by
      rw [cond_apply]; exact .iInter fun i => hY i (ht i)
    _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
      congr 2
      calc
        _ = (⋂ i, Y i ⁻¹' t i) inter ⋂ i, if i in s then f i else .univ := by
          congr 1
          simp only [Set.iInter_ite, Set.iInter_univ, Set.inter_univ]
        _ = ⋂ i, Y i ⁻¹' t i inter (if i in s then f i else .univ) := by rw [Set.iInter_inter_distrib]
        _ = _ := Set.iInter_congr fun i => by by_cases hi : i in s <;> simp [hi, g]
    _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
      rw [hYt]
    _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * ∏ i, κ a (g i) := by
      rw [hg]
    _ = ∏ i, (κ a (Y i ⁻¹' t i))⁻¹ * κ a (g i) := by
      rw [Finset.prod_mul_distrib]; rw [ENNReal.prod_inv_distrib]
exact fun _ _ i _ _ => .inr measure_ne_top _ _
    _ = ∏ i, if i in s then (κ a)[f i | Y i ⁻¹' t i] else 1 := by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i in s
      · simp only [hi, ↓reduceIte, g, cond_apply (hY i (ht i))]
      · simp only [hi, ↓reduceIte, g, ENNReal.inv_mul_cancel (hy i hi) (measure_ne_top _ _)]
    _ = _ := by simp

-- TODO: We can't state `Kernel.iIndepFun.cond` (the `Kernel` analogue of
-- `ProbabilityTheory.iIndepFun.cond`) because we don't have a version of `ProbabilityTheory.cond`
-- for kernels

end ProbabilityTheory.Kernel
