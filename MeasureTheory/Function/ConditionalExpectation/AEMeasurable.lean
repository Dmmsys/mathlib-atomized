/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-! # Functions a.e. measurable with respect to a sub-σ-algebra

A function `f` verifies `AEStronglyMeasurable[m] f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `AEStronglyMeasurable`, but the
`MeasurableSpace` structures used for the measurability statement and for the measure are
different.

We define `lpMeas F 𝕜 m p μ`, the subspace of `Lp F p μ` containing functions `f` verifying
`AEStronglyMeasurable[m] f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-strongly
measurable function.

## Main statements

We define an `IsometryEquiv` between `lpMeasSubgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of `lpMeas`.

`Lp.induction_stronglyMeasurable` (see also `MemLp.induction_stronglyMeasurable`):
To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.

-/

@[expose] public section


open TopologicalSpace Filter

open scoped ENNReal MeasureTheory

namespace MeasureTheory

/--
theorem `ae_eq_trim_iff_of_aestronglyMeasurable` / 定理 `ae_eq_trim_iff_of_aestronglyMeasurable`

English:
theorem ae_eq_trim_iff_of_aestronglyMeasurable
  statement: {α β} [TopologicalSpace β] [MetrizableSpace β]
  proof: (hfm.stronglyMeasurable_mk.ae_eq_trim_iff hm hgm.stronglyMeasurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h =>
      hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩

中文:
定理 ae_eq_trim_iff_of_aestronglyMeasurable
  结论: {α β} [TopologicalSpace β] [MetrizableSpace β]
  证明: (hfm.stronglyMeasurable_mk.ae_eq_trim_iff hm hgm.stronglyMeasurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h =>
      hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩

Depends on / 依赖: ae_eq_mk, ae_eq_trim_iff, h.trans, hfm.ae_eq_mk.symm.trans, hfm.ae_eq_mk.trans, hfm.stronglyMeasurable_mk.ae_eq_trim_iff, hgm.ae_eq_mk, hgm.ae_eq_mk.symm, hgm.stronglyMeasurable_mk, stronglyMeasurable_mk
-/
theorem ae_eq_trim_iff_of_aestronglyMeasurable {α β} [TopologicalSpace β] [MetrizableSpace β]
    {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α -> β} (hm : m <= m0)
    (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) :
    hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
  (hfm.stronglyMeasurable_mk.ae_eq_trim_iff hm hgm.stronglyMeasurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h =>
      hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩

/--
theorem `AEStronglyMeasurable.comp_ae_measurable'` / 定理 `AEStronglyMeasurable.comp_ae_measurable'`

English:
theorem AEStronglyMeasurable.comp_ae_measurable'
  statement: {α β γ : Type*} [TopologicalSpace β]
  proof: ⟨hf.mk f ∘ g, hf.stronglyMeasurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl),
    ae_eq_comp hg hf.ae_eq_mk⟩

中文:
定理 AEStronglyMeasurable.comp_ae_measurable'
  结论: {α β γ : 类型} [TopologicalSpace β]
  证明: ⟨hf.mk f ∘ g, hf.stronglyMeasurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl),
    ae_eq_comp hg hf.ae_eq_mk⟩

Depends on / 依赖: ae_eq_comp, ae_eq_mk, comp_measurable, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.comp_measurable, le_rfl, measurable_iff_comap_le, measurable_iff_comap_le.mpr, stronglyMeasurable_mk
-/
theorem AEStronglyMeasurable.comp_ae_measurable' {α β γ : Type*} [TopologicalSpace β]
    {mα : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {μ : Measure γ} {g : γ -> α}
    (hf : AEStronglyMeasurable f (μ.map g)) (hg : AEMeasurable g μ) :
    AEStronglyMeasurable[mα.comap g] (f ∘ g) μ :=
  ⟨hf.mk f ∘ g, hf.stronglyMeasurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl),
    ae_eq_comp hg hf.ae_eq_mk⟩

variable {α F 𝕜 : Type*} {p : Real>=0∞} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section LpMeas

/-! ## The subset `lpMeas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/


variable (F)

/--
Definition of `lpMeasSubgroup` / `lpMeasSubgroup` 的定义

English:
definition lpMeasSubgroup
  signature: (m : MeasurableSpace α) [MeasurableSpace α] (p : Real>=0∞) (μ : Measure α)
  body: {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
  zero_mem' := ⟨(0 : α -> F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  neg_mem' {f} hf := AEStronglyMeasurable.congr hf.neg (Lp.coeFn_neg f).symm

中文:
定义 lpMeasSubgroup
  签名: (m : MeasurableSpace α) [MeasurableSpace α] (p : 实数>=0∞) (μ : Measure α)
  定义体: {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
  zero_mem' := ⟨(0 : α -> F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  neg_mem' {f} hf := AEStronglyMeasurable.congr hf.neg (Lp.coeFn_neg f).symm

Depends on / 依赖: AEStronglyMeasurable, relIndex_adjoinNegOne_ne_zero
-/
def lpMeasSubgroup (m : MeasurableSpace α) [MeasurableSpace α] (p : Real>=0∞) (μ : Measure α) :
    AddSubgroup (Lp F p μ) where
  carrier := {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
  zero_mem' := ⟨(0 : α -> F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  neg_mem' {f} hf := AEStronglyMeasurable.congr hf.neg (Lp.coeFn_neg f).symm

variable (𝕜)

/--
Definition of `lpMeas` / `lpMeas` 的定义

English:
definition lpMeas
  signature: (m : MeasurableSpace α) [MeasurableSpace α] (p : Real>=0∞) (μ : Measure α)
  body: {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
  zero_mem' := ⟨(0 : α -> F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  smul_mem' c f hf := (hf.const_smul c).congr (Lp.coeFn_smul c f).symm

中文:
定义 lpMeas
  签名: (m : MeasurableSpace α) [MeasurableSpace α] (p : 实数>=0∞) (μ : Measure α)
  定义体: {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
  zero_mem' := ⟨(0 : α -> F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  smul_mem' c f hf := (hf.const_smul c).congr (Lp.coeFn_smul c f).symm

Depends on / 依赖: AEStronglyMeasurable
-/
def lpMeas (m : MeasurableSpace α) [MeasurableSpace α] (p : Real>=0∞) (μ : Measure α) :
    Submodule 𝕜 (Lp F p μ) where
  carrier := {f : Lp F p μ | AEStronglyMeasurable[m] f μ}
  zero_mem' := ⟨(0 : α -> F), @stronglyMeasurable_zero _ _ m _ _, Lp.coeFn_zero _ _ _⟩
  add_mem' {f g} hf hg := (hf.add hg).congr (Lp.coeFn_add f g).symm
  smul_mem' c f hf := (hf.const_smul c).congr (Lp.coeFn_smul c f).symm

variable {F 𝕜}

/--
theorem `mem_lpMeasSubgroup_iff_aestronglyMeasurable` / 定理 `mem_lpMeasSubgroup_iff_aestronglyMeasurable`

English:
theorem mem_lpMeasSubgroup_iff_aestronglyMeasurable
  statement: {m m0 : MeasurableSpace α} {μ : Measure α}
  proof: by
  rw [← AddSubgroup.mem_carrier]; rw [lpMeasSubgroup]; rw [Set.mem_ofPred_eq]

中文:
定理 mem_lpMeasSubgroup_iff_aestronglyMeasurable
  结论: {m m0 : MeasurableSpace α} {μ : Measure α}
  证明: by
  rw [← AddSubgroup.mem_carrier]; rw [lpMeasSubgroup]; rw [Set.mem_ofPred_eq]

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_carrier, Set.mem_ofPred_eq, lpMeasSubgroup, mem_carrier, mem_ofPred_eq
-/
theorem mem_lpMeasSubgroup_iff_aestronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : Lp F p μ} : f in lpMeasSubgroup F m p μ ↔ AEStronglyMeasurable[m] f μ := by
  rw [← AddSubgroup.mem_carrier]; rw [lpMeasSubgroup]; rw [Set.mem_ofPred_eq]

/--
theorem `mem_lpMeas_iff_aestronglyMeasurable` / 定理 `mem_lpMeas_iff_aestronglyMeasurable`

English:
theorem mem_lpMeas_iff_aestronglyMeasurable
  statement: {m m0 : MeasurableSpace α} {μ : Measure α}
  proof: by
  rw [← SetLike.mem_coe]; rw [← Submodule.mem_carrier]; rw [lpMeas]; rw [Set.mem_ofPred_eq]

中文:
定理 mem_lpMeas_iff_aestronglyMeasurable
  结论: {m m0 : MeasurableSpace α} {μ : Measure α}
  证明: by
  rw [← SetLike.mem_coe]; rw [← Submodule.mem_carrier]; rw [lpMeas]; rw [Set.mem_ofPred_eq]

Depends on / 依赖: Set.mem_ofPred_eq, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_carrier, lpMeas, mem_carrier, mem_coe, mem_ofPred_eq
-/
theorem mem_lpMeas_iff_aestronglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : Lp F p μ} : f in lpMeas F 𝕜 m p μ ↔ AEStronglyMeasurable[m] f μ := by
  rw [← SetLike.mem_coe]; rw [← Submodule.mem_carrier]; rw [lpMeas]; rw [Set.mem_ofPred_eq]

/--
theorem `lpMeas.aestronglyMeasurable` / 定理 `lpMeas.aestronglyMeasurable`

English:
theorem lpMeas.aestronglyMeasurable
  statement: {m _ : MeasurableSpace α} {μ : Measure α}
  proof: mem_lpMeas_iff_aestronglyMeasurable.mp f.mem

中文:
定理 lpMeas.aestronglyMeasurable
  结论: {m _ : MeasurableSpace α} {μ : Measure α}
  证明: mem_lpMeas_iff_aestronglyMeasurable.mp f.mem

Depends on / 依赖: Subgroup, Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff, f.mem, hasDetPlusMinusOne_adjoinNegOne_iff, mem_lpMeas_iff_aestronglyMeasurable, mem_lpMeas_iff_aestronglyMeasurable.mp
-/
theorem lpMeas.aestronglyMeasurable {m _ : MeasurableSpace α} {μ : Measure α}
    (f : lpMeas F 𝕜 m p μ) : AEStronglyMeasurable[m] (f : α -> F) μ :=
  mem_lpMeas_iff_aestronglyMeasurable.mp f.mem

/--
theorem `mem_lpMeas_self` / 定理 `mem_lpMeas_self`

English:
theorem mem_lpMeas_self
  given: {m0 : MeasurableSpace α} (μ : Measure α) (f : Lp F p μ)
  proof: mem_lpMeas_iff_aestronglyMeasurable.mpr (Lp.aestronglyMeasurable f)

中文:
定理 mem_lpMeas_self
  条件: {m0 : MeasurableSpace α} (μ : Measure α) (f : Lp F p μ)
  证明: mem_lpMeas_iff_aestronglyMeasurable.mpr (Lp.aestronglyMeasurable f)

Depends on / 依赖: Fact.out, Lp.aestronglyMeasurable, Subgroup, Subgroup.hasDetOne_adjoinNegOne_iff, aestronglyMeasurable, hasDetOne_adjoinNegOne_iff, mem_lpMeas_iff_aestronglyMeasurable, mem_lpMeas_iff_aestronglyMeasurable.mpr
-/
theorem mem_lpMeas_self {m0 : MeasurableSpace α} (μ : Measure α) (f : Lp F p μ) :
    f in lpMeas F 𝕜 m0 p μ :=
  mem_lpMeas_iff_aestronglyMeasurable.mpr (Lp.aestronglyMeasurable f)

/--
theorem `mem_lpMeas_indicatorConstLp` / 定理 `mem_lpMeas_indicatorConstLp`

English:
theorem mem_lpMeas_indicatorConstLp
  statement: {m m0 : MeasurableSpace α} (hm : m <= m0) {μ : Measure α}
  proof: ⟨s.indicator fun _ : α => c, (@stronglyMeasurable_const _ _ m _ _).indicator hs,
    indicatorConstLp_coeFn⟩

中文:
定理 mem_lpMeas_indicatorConstLp
  结论: {m m0 : MeasurableSpace α} (hm : m <= m0) {μ : Measure α}
  证明: ⟨s.indicator fun _ : α => c, (@stronglyMeasurable_const _ _ m _ _).indicator hs,
    indicatorConstLp_coeFn⟩

Depends on / 依赖: indicator, indicatorConstLp_coeFn, s.indicator, stronglyMeasurable_const
-/
theorem mem_lpMeas_indicatorConstLp {m m0 : MeasurableSpace α} (hm : m <= m0) {μ : Measure α}
    {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s != ∞) {c : F} :
    indicatorConstLp p (hm s hs) hμs c in lpMeas F 𝕜 m p μ :=
  ⟨s.indicator fun _ : α => c, (@stronglyMeasurable_const _ _ m _ _).indicator hs,
    indicatorConstLp_coeFn⟩

section CompleteSubspace

/-! ## The subspace `lpMeas` is complete.

We define an `IsometryEquiv` between `lpMeasSubgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`lpMeasSubgroup` (and `lpMeas`). -/


variable {m m0 : MeasurableSpace α} {μ : Measure α}

/--
theorem `memLp_trim_of_mem_lpMeasSubgroup` / 定理 `memLp_trim_of_mem_lpMeasSubgroup`

English:
theorem memLp_trim_of_mem_lpMeasSubgroup
  statement: (hm : m <= m0) (f : Lp F p μ)
  proof: by
  have hf : AEStronglyMeasurable[m] f μ :=
    mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp hf_meas
  change MemLp (hf.mk f) p (μ.trim hm)
  refine ⟨hf.stronglyMeasurable_mk.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_trim hm hf.stronglyMeasurable_mk]; rw [eLpNorm_congr_ae hf.ae_eq_mk.symm]
  exact

中文:
定理 memLp_trim_of_mem_lpMeasSubgroup
  结论: (hm : m <= m0) (f : Lp F p μ)
  证明: by
  have hf : AEStronglyMeasurable[m] f μ :=
    mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp hf_meas
  change MemLp (hf.mk f) p (μ.trim hm)
  refine ⟨hf.stronglyMeasurable_mk.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_trim hm hf.stronglyMeasurable_mk]; rw [eLpNorm_congr_ae hf.ae_eq_mk.symm]
  exact

Depends on / 依赖: AEStronglyMeasurable, Lp.eLpNorm_lt_top, ae_eq_mk, aestronglyMeasurable, eLpNorm_congr_ae, eLpNorm_lt_top, eLpNorm_trim, hf.ae_eq_mk.symm, hf.mk, hf.stronglyMeasurable_mk, hf.stronglyMeasurable_mk.aestronglyMeasurable, hf_meas, mem_lpMeasSubgroup_iff_aestronglyMeasurable, mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp, stronglyMeasurable_mk
-/
theorem memLp_trim_of_mem_lpMeasSubgroup (hm : m <= m0) (f : Lp F p μ)
    (hf_meas : f in lpMeasSubgroup F m p μ) :
    MemLp (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp hf_meas).choose p (μ.trim hm) := by
  have hf : AEStronglyMeasurable[m] f μ :=
    mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp hf_meas
  change MemLp (hf.mk f) p (μ.trim hm)
  refine ⟨hf.stronglyMeasurable_mk.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_trim hm hf.stronglyMeasurable_mk]; rw [eLpNorm_congr_ae hf.ae_eq_mk.symm]
  exact Lp.eLpNorm_lt_top f

/--
theorem `mem_lpMeasSubgroup_toLp_of_trim` / 定理 `mem_lpMeasSubgroup_toLp_of_trim`

English:
theorem mem_lpMeasSubgroup_toLp_of_trim
  given: (hm : m <= m0) (f : Lp F p (μ.trim hm))
  proof: by
  let hf_mem_ℒp := memLp_of_memLp_trim hm (Lp.memLp f)
  rw [mem_lpMeasSubgroup_iff_aestronglyMeasurable]
  refine AEStronglyMeasurable.congr ?_ (MemLp.coeFn_toLp hf_mem_ℒp).symm
  exact (Lp.aestronglyMeasurable f).of_trim hm

中文:
定理 mem_lpMeasSubgroup_toLp_of_trim
  条件: (hm : m <= m0) (f : Lp F p (μ.trim hm))
  证明: by
  let hf_mem_ℒp := memLp_of_memLp_trim hm (Lp.memLp f)
  rw [mem_lpMeasSubgroup_iff_aestronglyMeasurable]
  refine AEStronglyMeasurable.congr ?_ (MemLp.coeFn_toLp hf_mem_ℒp).symm
  exact (Lp.aestronglyMeasurable f).of_trim hm

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.congr, Lp.aestronglyMeasurable, Lp.memLp, MemLp.coeFn_toLp, ModularForm, ModularForm.funLike, aestronglyMeasurable, coeFn_toLp, funLike, memLp_of_memLp_trim, mem_lpMeasSubgroup_iff_aestronglyMeasurable, of_trim
-/
theorem mem_lpMeasSubgroup_toLp_of_trim (hm : m <= m0) (f : Lp F p (μ.trim hm)) :
    (memLp_of_memLp_trim hm (Lp.memLp f)).toLp f in lpMeasSubgroup F m p μ := by
  let hf_mem_ℒp := memLp_of_memLp_trim hm (Lp.memLp f)
  rw [mem_lpMeasSubgroup_iff_aestronglyMeasurable]
  refine AEStronglyMeasurable.congr ?_ (MemLp.coeFn_toLp hf_mem_ℒp).symm
  exact (Lp.aestronglyMeasurable f).of_trim hm

variable (F p μ)

/--
Definition of `lpMeasSubgroupToLpTrim` / `lpMeasSubgroupToLpTrim` 的定义

English:
definition lpMeasSubgroupToLpTrim
  signature: (hm : m <= m0) (f : lpMeasSubgroup F m p μ)
  body: MemLp.toLp (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose
    (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)

中文:
定义 lpMeasSubgroupToLpTrim
  签名: (hm : m <= m0) (f : lpMeasSubgroup F m p μ)
  定义体: MemLp.toLp (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose
    (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)

Depends on / 依赖: MemLp.toLp, ModularForm, ModularForm.instModularFormClass, f.mem, instModularFormClass, memLp_trim_of_mem_lpMeasSubgroup, mem_lpMeasSubgroup_iff_aestronglyMeasurable, mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp
-/
noncomputable def lpMeasSubgroupToLpTrim (hm : m <= m0) (f : lpMeasSubgroup F m p μ) :
    Lp F p (μ.trim hm) :=
  MemLp.toLp (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose
    (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)

variable (𝕜) in
/--
Definition of `lpMeasToLpTrim` / `lpMeasToLpTrim` 的定义

English:
definition lpMeasToLpTrim
  signature: (hm : m <= m0) (f : lpMeas F 𝕜 m p μ)
  body: MemLp.toLp (mem_lpMeas_iff_aestronglyMeasurable.mp f.mem).choose
    (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)

中文:
定义 lpMeasToLpTrim
  签名: (hm : m <= m0) (f : lpMeas F 𝕜 m p μ)
  定义体: MemLp.toLp (mem_lpMeas_iff_aestronglyMeasurable.mp f.mem).choose
    (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)

Depends on / 依赖: MemLp.toLp, f.mem, memLp_trim_of_mem_lpMeasSubgroup, mem_lpMeas_iff_aestronglyMeasurable, mem_lpMeas_iff_aestronglyMeasurable.mp
-/
noncomputable def lpMeasToLpTrim (hm : m <= m0) (f : lpMeas F 𝕜 m p μ) : Lp F p (μ.trim hm) :=
  MemLp.toLp (mem_lpMeas_iff_aestronglyMeasurable.mp f.mem).choose
    (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem)

/--
Definition of `lpTrimToLpMeasSubgroup` / `lpTrimToLpMeasSubgroup` 的定义

English:
definition lpTrimToLpMeasSubgroup
  signature: (hm : m <= m0) (f : Lp F p (μ.trim hm))
  body: ⟨(memLp_of_memLp_trim hm (Lp.memLp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩

中文:
定义 lpTrimToLpMeasSubgroup
  签名: (hm : m <= m0) (f : Lp F p (μ.trim hm))
  定义体: ⟨(memLp_of_memLp_trim hm (Lp.memLp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩

Depends on / 依赖: CuspForm, CuspForm.funLike, FunLike, Lp.memLp, funLike, memLp_of_memLp_trim, mem_lpMeasSubgroup_toLp_of_trim
-/
noncomputable def lpTrimToLpMeasSubgroup (hm : m <= m0) (f : Lp F p (μ.trim hm)) :
    lpMeasSubgroup F m p μ :=
  ⟨(memLp_of_memLp_trim hm (Lp.memLp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩

variable (𝕜) in
/--
Definition of `lpTrimToLpMeas` / `lpTrimToLpMeas` 的定义

English:
definition lpTrimToLpMeas
  signature: (hm : m <= m0) (f : Lp F p (μ.trim hm))
  body: ⟨(memLp_of_memLp_trim hm (Lp.memLp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩

中文:
定义 lpTrimToLpMeas
  签名: (hm : m <= m0) (f : Lp F p (μ.trim hm))
  定义体: ⟨(memLp_of_memLp_trim hm (Lp.memLp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩

Depends on / 依赖: CuspForm, CuspFormClass, CuspFormClass.cuspForm, Lp.memLp, cuspForm, memLp_of_memLp_trim, mem_lpMeasSubgroup_toLp_of_trim
-/
noncomputable def lpTrimToLpMeas (hm : m <= m0) (f : Lp F p (μ.trim hm)) : lpMeas F 𝕜 m p μ :=
  ⟨(memLp_of_memLp_trim hm (Lp.memLp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩

variable {F p μ}

/--
theorem `lpMeasSubgroupToLpTrim_ae_eq` / 定理 `lpMeasSubgroupToLpTrim_ae_eq`

English:
theorem lpMeasSubgroupToLpTrim_ae_eq
  given: (hm : m <= m0) (f : lpMeasSubgroup F m p μ)
  proof: (ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose_spec.2.symm

中文:
定理 lpMeasSubgroupToLpTrim_ae_eq
  条件: (hm : m <= m0) (f : lpMeasSubgroup F m p μ)
  证明: (ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose_spec.2.symm

Depends on / 依赖: MemLp.coeFn_toLp, ae_eq_of_ae_eq_trim, choose_spec, coeFn_toLp, f.mem, memLp_trim_of_mem_lpMeasSubgroup, mem_lpMeasSubgroup_iff_aestronglyMeasurable, mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp
-/
theorem lpMeasSubgroupToLpTrim_ae_eq (hm : m <= m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose_spec.2.symm

/--
theorem `lpTrimToLpMeasSubgroup_ae_eq` / 定理 `lpTrimToLpMeasSubgroup_ae_eq`

English:
theorem lpTrimToLpMeasSubgroup_ae_eq
  given: (hm : m <= m0) (f : Lp F p (μ.trim hm))
  proof: MemLp.coeFn_toLp (memLp_of_memLp_trim hm (Lp.memLp f))

中文:
定理 lpTrimToLpMeasSubgroup_ae_eq
  条件: (hm : m <= m0) (f : Lp F p (μ.trim hm))
  证明: MemLp.coeFn_toLp (memLp_of_memLp_trim hm (Lp.memLp f))

Depends on / 依赖: Lp.memLp, MemLp.coeFn_toLp, coeFn_toLp, memLp_of_memLp_trim
-/
theorem lpTrimToLpMeasSubgroup_ae_eq (hm : m <= m0) (f : Lp F p (μ.trim hm)) :
    lpTrimToLpMeasSubgroup F p μ hm f =ᵐ[μ] f :=
  MemLp.coeFn_toLp (memLp_of_memLp_trim hm (Lp.memLp f))

/--
theorem `lpMeasToLpTrim_ae_eq` / 定理 `lpMeasToLpTrim_ae_eq`

English:
theorem lpMeasToLpTrim_ae_eq
  given: (hm : m <= m0) (f : lpMeas F 𝕜 m p μ)
  proof: (ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose_spec.2.symm

中文:
定理 lpMeasToLpTrim_ae_eq
  条件: (hm : m <= m0) (f : lpMeas F 𝕜 m p μ)
  证明: (ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose_spec.2.symm

Depends on / 依赖: MemLp.coeFn_toLp, ae_eq_of_ae_eq_trim, choose_spec, coeFn_toLp, f.mem, memLp_trim_of_mem_lpMeasSubgroup, mem_lpMeasSubgroup_iff_aestronglyMeasurable, mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp
-/
theorem lpMeasToLpTrim_ae_eq (hm : m <= m0) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp (memLp_trim_of_mem_lpMeasSubgroup hm f.1 f.mem))).trans
    (mem_lpMeasSubgroup_iff_aestronglyMeasurable.mp f.mem).choose_spec.2.symm

/--
theorem `lpTrimToLpMeas_ae_eq` / 定理 `lpTrimToLpMeas_ae_eq`

English:
theorem lpTrimToLpMeas_ae_eq
  given: (hm : m <= m0) (f : Lp F p (μ.trim hm))
  proof: MemLp.coeFn_toLp (memLp_of_memLp_trim hm (Lp.memLp f))

中文:
定理 lpTrimToLpMeas_ae_eq
  条件: (hm : m <= m0) (f : Lp F p (μ.trim hm))
  证明: MemLp.coeFn_toLp (memLp_of_memLp_trim hm (Lp.memLp f))

Depends on / 依赖: Lp.memLp, MemLp.coeFn_toLp, coeFn_toLp, memLp_of_memLp_trim
-/
theorem lpTrimToLpMeas_ae_eq (hm : m <= m0) (f : Lp F p (μ.trim hm)) :
    lpTrimToLpMeas F 𝕜 p μ hm f =ᵐ[μ] f :=
  MemLp.coeFn_toLp (memLp_of_memLp_trim hm (Lp.memLp f))

/--
theorem `lpMeasSubgroupToLpTrim_right_inv` / 定理 `lpMeasSubgroupToLpTrim_right_inv`

English:
theorem lpMeasSubgroupToLpTrim_right_inv
  given: (hm : m <= m0)
  proof: by
  intro f
  ext1
  refine
    (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _) ?_
  exact (lpMeasSubgroupToLpTrim_ae_eq hm _).trans (lpTrimToLpMeasSubgroup_ae_eq hm _)

中文:
定理 lpMeasSubgroupToLpTrim_right_inv
  条件: (hm : m <= m0)
  证明: by
  intro f
  ext1
  refine
    (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _) ?_
  exact (lpMeasSubgroupToLpTrim_ae_eq hm _).trans (lpTrimToLpMeasSubgroup_ae_eq hm _)

Depends on / 依赖: Lp.stronglyMeasurable, ae_eq_trim_of_stronglyMeasurable, lpMeasSubgroupToLpTrim_ae_eq, lpTrimToLpMeasSubgroup_ae_eq, stronglyMeasurable
-/
theorem lpMeasSubgroupToLpTrim_right_inv (hm : m <= m0) :
    Function.RightInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  refine
    (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _) ?_
  exact (lpMeasSubgroupToLpTrim_ae_eq hm _).trans (lpTrimToLpMeasSubgroup_ae_eq hm _)

/--
theorem `lpMeasSubgroupToLpTrim_left_inv` / 定理 `lpMeasSubgroupToLpTrim_left_inv`

English:
theorem lpMeasSubgroupToLpTrim_left_inv
  given: (hm : m <= m0)
  proof: by
  intro f
  ext1
  ext1
  exact (lpTrimToLpMeasSubgroup_ae_eq hm _).trans (lpMeasSubgroupToLpTrim_ae_eq hm _)

中文:
定理 lpMeasSubgroupToLpTrim_left_inv
  条件: (hm : m <= m0)
  证明: by
  intro f
  ext1
  ext1
  exact (lpTrimToLpMeasSubgroup_ae_eq hm _).trans (lpMeasSubgroupToLpTrim_ae_eq hm _)

Depends on / 依赖: lpMeasSubgroupToLpTrim_ae_eq, lpTrimToLpMeasSubgroup_ae_eq
-/
theorem lpMeasSubgroupToLpTrim_left_inv (hm : m <= m0) :
    Function.LeftInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  ext1
  exact (lpTrimToLpMeasSubgroup_ae_eq hm _).trans (lpMeasSubgroupToLpTrim_ae_eq hm _)

/--
theorem `lpMeasSubgroupToLpTrim_add` / 定理 `lpMeasSubgroupToLpTrim_add`

English:
theorem lpMeasSubgroupToLpTrim_add
  given: (hm : m <= m0) (f g : lpMeasSubgroup F m p μ)
  proof: by
  ext1
  grw [Lp.coeFn_add]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm ?_ ?_
  · exact (Lp.stronglyMeasurable _).add (Lp.stronglyMeasurable _)
  grw [lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq,
    ← Lp.coeFn_add]
  rfl

中文:
定理 lpMeasSubgroupToLpTrim_add
  条件: (hm : m <= m0) (f g : lpMeasSubgroup F m p μ)
  证明: by
  ext1
  grw [Lp.coeFn_add]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm ?_ ?_
  · exact (Lp.stronglyMeasurable _).add (Lp.stronglyMeasurable _)
  grw [lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq,
    ← Lp.coeFn_add]
  rfl

Depends on / 依赖: Lp.coeFn_add, Lp.stronglyMeasurable, ae_eq_trim_of_stronglyMeasurable, coeFn_add, lpMeasSubgroupToLpTrim_ae_eq, stronglyMeasurable
-/
theorem lpMeasSubgroupToLpTrim_add (hm : m <= m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f + g) =
      lpMeasSubgroupToLpTrim F p μ hm f + lpMeasSubgroupToLpTrim F p μ hm g := by
  ext1
  grw [Lp.coeFn_add]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm ?_ ?_
  · exact (Lp.stronglyMeasurable _).add (Lp.stronglyMeasurable _)
  grw [lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq,
    ← Lp.coeFn_add]
  rfl

/--
theorem `lpMeasSubgroupToLpTrim_neg` / 定理 `lpMeasSubgroupToLpTrim_neg`

English:
theorem lpMeasSubgroupToLpTrim_neg
  given: (hm : m <= m0) (f : lpMeasSubgroup F m p μ)
  proof: by
  ext1
  grw [Lp.coeFn_neg]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _).neg
    ?_
  grw [lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq, ← Lp.coeFn_neg]
  rfl

中文:
定理 lpMeasSubgroupToLpTrim_neg
  条件: (hm : m <= m0) (f : lpMeasSubgroup F m p μ)
  证明: by
  ext1
  grw [Lp.coeFn_neg]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _).neg
    ?_
  grw [lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq, ← Lp.coeFn_neg]
  rfl

Depends on / 依赖: Lp.coeFn_neg, Lp.stronglyMeasurable, ae_eq_trim_of_stronglyMeasurable, coeFn_neg, lpMeasSubgroupToLpTrim_ae_eq, stronglyMeasurable
-/
theorem lpMeasSubgroupToLpTrim_neg (hm : m <= m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (-f) = -lpMeasSubgroupToLpTrim F p μ hm f := by
  ext1
  grw [Lp.coeFn_neg]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm (Lp.stronglyMeasurable _).neg
    ?_
  grw [lpMeasSubgroupToLpTrim_ae_eq, lpMeasSubgroupToLpTrim_ae_eq, ← Lp.coeFn_neg]
  rfl

/--
theorem `lpMeasSubgroupToLpTrim_sub` / 定理 `lpMeasSubgroupToLpTrim_sub`

English:
theorem lpMeasSubgroupToLpTrim_sub
  given: (hm : m <= m0) (f g : lpMeasSubgroup F m p μ)
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [lpMeasSubgroupToLpTrim_add]; rw [lpMeasSubgroupToLpTrim_neg]

中文:
定理 lpMeasSubgroupToLpTrim_sub
  条件: (hm : m <= m0) (f g : lpMeasSubgroup F m p μ)
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [lpMeasSubgroupToLpTrim_add]; rw [lpMeasSubgroupToLpTrim_neg]

Depends on / 依赖: lpMeasSubgroupToLpTrim_add, lpMeasSubgroupToLpTrim_neg, sub_eq_add_neg
-/
theorem lpMeasSubgroupToLpTrim_sub (hm : m <= m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f - g) =
      lpMeasSubgroupToLpTrim F p μ hm f - lpMeasSubgroupToLpTrim F p μ hm g := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [lpMeasSubgroupToLpTrim_add]; rw [lpMeasSubgroupToLpTrim_neg]

/--
theorem `lpMeasToLpTrim_smul` / 定理 `lpMeasToLpTrim_smul`

English:
theorem lpMeasToLpTrim_smul
  given: (hm : m <= m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ)
  proof: by
  ext1
  grw [Lp.coeFn_smul]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm ?_ ?_
  · exact (Lp.stronglyMeasurable _).const_smul c
  grw [lpMeasToLpTrim_ae_eq]
  push_cast
  grw [Lp.coeFn_smul, lpMeasToLpTrim_ae_eq]

中文:
定理 lpMeasToLpTrim_smul
  条件: (hm : m <= m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ)
  证明: by
  ext1
  grw [Lp.coeFn_smul]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm ?_ ?_
  · exact (Lp.stronglyMeasurable _).const_smul c
  grw [lpMeasToLpTrim_ae_eq]
  push_cast
  grw [Lp.coeFn_smul, lpMeasToLpTrim_ae_eq]

Depends on / 依赖: Lp.coeFn_smul, Lp.stronglyMeasurable, ae_eq_trim_of_stronglyMeasurable, coeFn_smul, const_smul, lpMeasToLpTrim_ae_eq, stronglyMeasurable
-/
theorem lpMeasToLpTrim_smul (hm : m <= m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm (c • f) = c • lpMeasToLpTrim F 𝕜 p μ hm f := by
  ext1
  grw [Lp.coeFn_smul]
  refine (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable hm ?_ ?_
  · exact (Lp.stronglyMeasurable _).const_smul c
  grw [lpMeasToLpTrim_ae_eq]
  push_cast
  grw [Lp.coeFn_smul, lpMeasToLpTrim_ae_eq]

/--
theorem `lpMeasSubgroupToLpTrim_norm_map` / 定理 `lpMeasSubgroupToLpTrim_norm_map`

English:
theorem lpMeasSubgroupToLpTrim_norm_map
  statement: [hp : Fact (1 <= p)] (hm : m <= m0)
  proof: by
  rw [Lp.norm_def]; rw [eLpNorm_trim hm (Lp.stronglyMeasurable _)]; rw [eLpNorm_congr_ae (lpMeasSubgroupToLpTrim_ae_eq hm _)]; rw [← Lp.norm_def]
  congr

中文:
定理 lpMeasSubgroupToLpTrim_norm_map
  结论: [hp : Fact (1 <= p)] (hm : m <= m0)
  证明: by
  rw [Lp.norm_def]; rw [eLpNorm_trim hm (Lp.stronglyMeasurable _)]; rw [eLpNorm_congr_ae (lpMeasSubgroupToLpTrim_ae_eq hm _)]; rw [← Lp.norm_def]
  congr

Depends on / 依赖: Lp.norm_def, Lp.stronglyMeasurable, eLpNorm_congr_ae, eLpNorm_trim, lpMeasSubgroupToLpTrim_ae_eq, norm_def, stronglyMeasurable
-/
theorem lpMeasSubgroupToLpTrim_norm_map [hp : Fact (1 <= p)] (hm : m <= m0)
    (f : lpMeasSubgroup F m p μ) : ‖lpMeasSubgroupToLpTrim F p μ hm f‖ = ‖f‖ := by
  rw [Lp.norm_def]; rw [eLpNorm_trim hm (Lp.stronglyMeasurable _)]; rw [eLpNorm_congr_ae (lpMeasSubgroupToLpTrim_ae_eq hm _)]; rw [← Lp.norm_def]
  congr

/--
theorem `isometry_lpMeasSubgroupToLpTrim` / 定理 `isometry_lpMeasSubgroupToLpTrim`

English:
theorem isometry_lpMeasSubgroupToLpTrim
  given: [hp : Fact (1 <= p)] (hm : m <= m0)
  proof: Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm]; rw [← lpMeasSubgroupToLpTrim_sub]; rw [lpMeasSubgroupToLpTrim_norm_map]; rw [dist_eq_norm]

中文:
定理 isometry_lpMeasSubgroupToLpTrim
  条件: [hp : Fact (1 <= p)] (hm : m <= m0)
  证明: Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm]; rw [← lpMeasSubgroupToLpTrim_sub]; rw [lpMeasSubgroupToLpTrim_norm_map]; rw [dist_eq_norm]

Depends on / 依赖: Isometry, Isometry.of_dist_eq, dist_eq_norm, lpMeasSubgroupToLpTrim_norm_map, lpMeasSubgroupToLpTrim_sub, of_dist_eq
-/
theorem isometry_lpMeasSubgroupToLpTrim [hp : Fact (1 <= p)] (hm : m <= m0) :
    Isometry (lpMeasSubgroupToLpTrim F p μ hm) :=
  Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm]; rw [← lpMeasSubgroupToLpTrim_sub]; rw [lpMeasSubgroupToLpTrim_norm_map]; rw [dist_eq_norm]

variable (F p μ)

/--
Definition of `lpMeasSubgroupToLpTrimIso` / `lpMeasSubgroupToLpTrimIso` 的定义

English:
definition lpMeasSubgroupToLpTrimIso
  signature: [Fact (1 <= p)] (hm : m <= m0)
  body: lpMeasSubgroupToLpTrim F p μ hm
  invFun := lpTrimToLpMeasSubgroup F p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  isometry_toFun := isometry_lpMeasSubgroupToLpTrim hm

中文:
定义 lpMeasSubgroupToLpTrimIso
  签名: [Fact (1 <= p)] (hm : m <= m0)
  定义体: lpMeasSubgroupToLpTrim F p μ hm
  invFun := lpTrimToLpMeasSubgroup F p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  isometry_toFun := isometry_lpMeasSubgroupToLpTrim hm

Depends on / 依赖: lpMeasSubgroupToLpTrim
-/
noncomputable def lpMeasSubgroupToLpTrimIso [Fact (1 <= p)] (hm : m <= m0) :
    lpMeasSubgroup F m p μ ≃ᵢ Lp F p (μ.trim hm) where
  toFun := lpMeasSubgroupToLpTrim F p μ hm
  invFun := lpTrimToLpMeasSubgroup F p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  isometry_toFun := isometry_lpMeasSubgroupToLpTrim hm

variable (𝕜)

/--
Definition of `lpMeasSubgroupToLpMeasIso` / `lpMeasSubgroupToLpMeasIso` 的定义

English:
definition lpMeasSubgroupToLpMeasIso
  signature: [Fact (1 <= p)]
  body: IsometryEquiv.refl (lpMeasSubgroup F m p μ)

中文:
定义 lpMeasSubgroupToLpMeasIso
  签名: [Fact (1 <= p)]
  定义体: IsometryEquiv.refl (lpMeasSubgroup F m p μ)

Depends on / 依赖: IsometryEquiv, IsometryEquiv.refl, lpMeasSubgroup
-/
noncomputable def lpMeasSubgroupToLpMeasIso [Fact (1 <= p)] :
    lpMeasSubgroup F m p μ ≃ᵢ lpMeas F 𝕜 m p μ :=
  IsometryEquiv.refl (lpMeasSubgroup F m p μ)

/--
Definition of `lpMeasToLpTrimLie` / `lpMeasToLpTrimLie` 的定义

English:
definition lpMeasToLpTrimLie
  signature: [Fact (1 <= p)] (hm : m <= m0)
  body: lpMeasToLpTrim F 𝕜 p μ hm
  invFun := lpTrimToLpMeas F 𝕜 p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  map_add' := lpMeasSubgroupToLpTrim_add hm
  map_smul' := lpMeasToLpTrim_smul hm
  norm_map' := lpMeasSubgroupToLpTrim_norm_map hm

中文:
定义 lpMeasToLpTrimLie
  签名: [Fact (1 <= p)] (hm : m <= m0)
  定义体: lpMeasToLpTrim F 𝕜 p μ hm
  invFun := lpTrimToLpMeas F 𝕜 p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  map_add' := lpMeasSubgroupToLpTrim_add hm
  map_smul' := lpMeasToLpTrim_smul hm
  norm_map' := lpMeasSubgroupToLpTrim_norm_map hm

Depends on / 依赖: lpMeasToLpTrim
-/
noncomputable def lpMeasToLpTrimLie [Fact (1 <= p)] (hm : m <= m0) :
    lpMeas F 𝕜 m p μ ≃ₗᵢ[𝕜] Lp F p (μ.trim hm) where
  toFun := lpMeasToLpTrim F 𝕜 p μ hm
  invFun := lpTrimToLpMeas F 𝕜 p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  map_add' := lpMeasSubgroupToLpTrim_add hm
  map_smul' := lpMeasToLpTrim_smul hm
  norm_map' := lpMeasSubgroupToLpTrim_norm_map hm

variable {F 𝕜 p μ}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hm
  signature: : Fact (m <= m0)] [CompleteSpace F] [hp : Fact (1 <= p)] :
  body: by
  rw [(lpMeasSubgroupToLpTrimIso F p μ hm.elim).completeSpace_iff]; infer_instance

中文:
实例 [hm
  签名: : Fact (m <= m0)] [CompleteSpace F] [hp : Fact (1 <= p)] :
  定义体: by
  rw [(lpMeasSubgroupToLpTrimIso F p μ hm.elim).completeSpace_iff]; infer_instance

Depends on / 依赖: completeSpace_iff, hm.elim, infer_instance, lpMeasSubgroupToLpTrimIso
-/
instance [hm : Fact (m <= m0)] [CompleteSpace F] [hp : Fact (1 <= p)] :
    CompleteSpace (lpMeasSubgroup F m p μ) := by
  rw [(lpMeasSubgroupToLpTrimIso F p μ hm.elim).completeSpace_iff]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hm
  signature: : Fact (m <= m0)] [CompleteSpace F] [hp : Fact (1 <= p)] :
  body: by
  rw [(lpMeasSubgroupToLpMeasIso F 𝕜 p μ).symm.completeSpace_iff]; infer_instance

中文:
实例 [hm
  签名: : Fact (m <= m0)] [CompleteSpace F] [hp : Fact (1 <= p)] :
  定义体: by
  rw [(lpMeasSubgroupToLpMeasIso F 𝕜 p μ).symm.completeSpace_iff]; infer_instance

Depends on / 依赖: completeSpace_iff, infer_instance, lpMeasSubgroupToLpMeasIso, symm.completeSpace_iff
-/
instance [hm : Fact (m <= m0)] [CompleteSpace F] [hp : Fact (1 <= p)] :
    CompleteSpace (lpMeas F 𝕜 m p μ) := by
  rw [(lpMeasSubgroupToLpMeasIso F 𝕜 p μ).symm.completeSpace_iff]; infer_instance

/--
theorem `isComplete_aestronglyMeasurable` / 定理 `isComplete_aestronglyMeasurable`

English:
theorem isComplete_aestronglyMeasurable
  given: [hp : Fact (1 <= p)] [CompleteSpace F] (hm : m <= m0)
  proof: by
  rw [← completeSpace_coe_iff_isComplete]
  have : Fact (m <= m0) := ⟨hm⟩
  change CompleteSpace (lpMeasSubgroup F m p μ)
  infer_instance

中文:
定理 isComplete_aestronglyMeasurable
  条件: [hp : Fact (1 <= p)] [CompleteSpace F] (hm : m <= m0)
  证明: by
  rw [← completeSpace_coe_iff_isComplete]
  have : Fact (m <= m0) := ⟨hm⟩
  change CompleteSpace (lpMeasSubgroup F m p μ)
  infer_instance

Depends on / 依赖: CompleteSpace, completeSpace_coe_iff_isComplete, infer_instance, lpMeasSubgroup
-/
theorem isComplete_aestronglyMeasurable [hp : Fact (1 <= p)] [CompleteSpace F] (hm : m <= m0) :
    IsComplete {f : Lp F p μ | AEStronglyMeasurable[m] f μ} := by
  rw [← completeSpace_coe_iff_isComplete]
  have : Fact (m <= m0) := ⟨hm⟩
  change CompleteSpace (lpMeasSubgroup F m p μ)
  infer_instance

/--
theorem `isClosed_aestronglyMeasurable` / 定理 `isClosed_aestronglyMeasurable`

English:
theorem isClosed_aestronglyMeasurable
  given: [Fact (1 <= p)] [CompleteSpace F] (hm : m <= m0)
  proof: IsComplete.isClosed (isComplete_aestronglyMeasurable hm)

中文:
定理 isClosed_aestronglyMeasurable
  条件: [Fact (1 <= p)] [CompleteSpace F] (hm : m <= m0)
  证明: IsComplete.isClosed (isComplete_aestronglyMeasurable hm)

Depends on / 依赖: IsComplete, IsComplete.isClosed, isClosed, isComplete_aestronglyMeasurable
-/
theorem isClosed_aestronglyMeasurable [Fact (1 <= p)] [CompleteSpace F] (hm : m <= m0) :
    IsClosed {f : Lp F p μ | AEStronglyMeasurable[m] f μ} :=
  IsComplete.isClosed (isComplete_aestronglyMeasurable hm)

end CompleteSubspace

section StronglyMeasurable

variable {m m0 : MeasurableSpace α} {μ : Measure α}

/--
theorem `lpMeas.ae_fin_strongly_measurable'` / 定理 `lpMeas.ae_fin_strongly_measurable'`

English:
theorem lpMeas.ae_fin_strongly_measurable'
  statement: (hm : m <= m0) (f : lpMeas F 𝕜 m p μ) (hp_ne_zero : p != 0)
  proof: ⟨lpMeasSubgroupToLpTrim F p μ hm f, Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top,
    (lpMeasSubgroupToLpTrim_ae_eq hm f).symm⟩

中文:
定理 lpMeas.ae_fin_strongly_measurable'
  结论: (hm : m <= m0) (f : lpMeas F 𝕜 m p μ) (hp_ne_zero : p != 0)
  证明: ⟨lpMeasSubgroupToLpTrim F p μ hm f, Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top,
    (lpMeasSubgroupToLpTrim_ae_eq hm f).symm⟩

Depends on / 依赖: Lp.finStronglyMeasurable, finStronglyMeasurable, hp_ne_top, hp_ne_zero, lpMeasSubgroupToLpTrim, lpMeasSubgroupToLpTrim_ae_eq
-/
theorem lpMeas.ae_fin_strongly_measurable' (hm : m <= m0) (f : lpMeas F 𝕜 m p μ) (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) :
    exists g, FinStronglyMeasurable g (μ.trim hm) ∧ f.1 =ᵐ[μ] g :=
  ⟨lpMeasSubgroupToLpTrim F p μ hm f, Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top,
    (lpMeasSubgroupToLpTrim_ae_eq hm f).symm⟩

/--
theorem `lpMeasToLpTrimLie_symm_indicator` / 定理 `lpMeasToLpTrimLie_symm_indicator`

English:
theorem lpMeasToLpTrimLie_symm_indicator
  statement: [one_le_p : Fact (1 <= p)] [NormedSpace Real F] {hm : m <= m0}
  proof: by
  ext1
  change
    lpTrimToLpMeas F Real p μ hm (indicatorConstLp p hs hμs c) =ᵐ[μ]
      (indicatorConstLp p _ _ c : α -> F)
  grw [lpTrimToLpMeas_ae_eq, ae_eq_of_ae_eq_trim indicatorConstLp_coeFn, indicatorConstLp_coeFn]

中文:
定理 lpMeasToLpTrimLie_symm_indicator
  结论: [one_le_p : Fact (1 <= p)] [NormedSpace 实数 F] {hm : m <= m0}
  证明: by
  ext1
  change
    lpTrimToLpMeas F Real p μ hm (indicatorConstLp p hs hμs c) =ᵐ[μ]
      (indicatorConstLp p _ _ c : α -> F)
  grw [lpTrimToLpMeas_ae_eq, ae_eq_of_ae_eq_trim indicatorConstLp_coeFn, indicatorConstLp_coeFn]

Depends on / 依赖: ae_eq_of_ae_eq_trim, indicatorConstLp, indicatorConstLp_coeFn, lpTrimToLpMeas, lpTrimToLpMeas_ae_eq
-/
theorem lpMeasToLpTrimLie_symm_indicator [one_le_p : Fact (1 <= p)] [NormedSpace Real F] {hm : m <= m0}
    {s : Set α} {μ : Measure α} (hs : MeasurableSet[m] s) (hμs : μ.trim hm s != ∞) (c : F) :
    ((lpMeasToLpTrimLie F Real p μ hm).symm (indicatorConstLp p hs hμs c) : Lp F p μ) =
      indicatorConstLp p (hm s hs) ((le_trim hm).trans_lt hμs.lt_top).ne c := by
  ext1
  change
    lpTrimToLpMeas F Real p μ hm (indicatorConstLp p hs hμs c) =ᵐ[μ]
      (indicatorConstLp p _ _ c : α -> F)
  grw [lpTrimToLpMeas_ae_eq, ae_eq_of_ae_eq_trim indicatorConstLp_coeFn, indicatorConstLp_coeFn]

/--
theorem `lpMeasToLpTrimLie_symm_toLp` / 定理 `lpMeasToLpTrimLie_symm_toLp`

English:
theorem lpMeasToLpTrimLie_symm_toLp
  statement: [one_le_p : Fact (1 <= p)] [NormedSpace Real F] (hm : m <= m0)
  proof: by
  ext1
  change lpTrimToLpMeas F Real p μ hm (MemLp.toLp f hf) =ᵐ[μ] (MemLp.toLp f _ : α -> F)
  grw [lpTrimToLpMeas_ae_eq, ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp hf), MemLp.coeFn_toLp]

中文:
定理 lpMeasToLpTrimLie_symm_toLp
  结论: [one_le_p : Fact (1 <= p)] [NormedSpace 实数 F] (hm : m <= m0)
  证明: by
  ext1
  change lpTrimToLpMeas F Real p μ hm (MemLp.toLp f hf) =ᵐ[μ] (MemLp.toLp f _ : α -> F)
  grw [lpTrimToLpMeas_ae_eq, ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp hf), MemLp.coeFn_toLp]

Depends on / 依赖: MemLp.coeFn_toLp, MemLp.toLp, ae_eq_of_ae_eq_trim, coeFn_toLp, lpTrimToLpMeas, lpTrimToLpMeas_ae_eq
-/
theorem lpMeasToLpTrimLie_symm_toLp [one_le_p : Fact (1 <= p)] [NormedSpace Real F] (hm : m <= m0)
    (f : α -> F) (hf : MemLp f p (μ.trim hm)) :
    ((lpMeasToLpTrimLie F Real p μ hm).symm (hf.toLp f) : Lp F p μ) =
      (memLp_of_memLp_trim hm hf).toLp f := by
  ext1
  change lpTrimToLpMeas F Real p μ hm (MemLp.toLp f hf) =ᵐ[μ] (MemLp.toLp f _ : α -> F)
  grw [lpTrimToLpMeas_ae_eq, ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp hf), MemLp.coeFn_toLp]

end StronglyMeasurable

end LpMeas

section Induction

variable {m m0 : MeasurableSpace α} {μ : Measure α} [Fact (1 <= p)] [NormedSpace Real F]

/-- Auxiliary lemma for `Lp.induction_stronglyMeasurable`. -/
@[elab_as_elim]
/--
theorem `Lp.induction_stronglyMeasurable_aux` / 定理 `Lp.induction_stronglyMeasurable_aux`

English:
theorem Lp.induction_stronglyMeasurable_aux
  statement: (hm : m <= m0) (hp_ne_top : p != ∞) (P : Lp F p μ -> Prop)
  proof: by
  intro f hf
  let f' := (⟨f, hf⟩ : lpMeas F Real m p μ)
  let g := lpMeasToLpTrimLie F Real p μ hm f'
  have hfg : f' = (lpMeasToLpTrimLie F Real p μ hm).symm g := by
    simp only [f', g, LinearIsometryEquiv.symm_apply_apply]
  change P ↑f'
  rw [hfg]
  refine
    @Lp.induction α F m _ p (μ.tri

中文:
定理 Lp.induction_stronglyMeasurable_aux
  结论: (hm : m <= m0) (hp_ne_top : p != ∞) (P : Lp F p μ -> 命题)
  证明: by
  intro f hf
  let f' := (⟨f, hf⟩ : lpMeas F Real m p μ)
  let g := lpMeasToLpTrimLie F Real p μ hm f'
  have hfg : f' = (lpMeasToLpTrimLie F Real p μ hm).symm g := by
    simp only [f', g, LinearIsometryEquiv.symm_apply_apply]
  change P ↑f'
  rw [hfg]
  refine
    @Lp.induction α F m _ p (μ.tri

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.symm_apply_apply, Lp.induction, Lp.simpleFunc.coe_indicatorConst, coe_indicatorConst, hp_ne_top, lpMeas, lpMeasToLpTrimLie, lpMeasToLpTrimLie_symm_indicator, simpleFunc, symm_apply_apply, t.ne
-/
theorem Lp.induction_stronglyMeasurable_aux (hm : m <= m0) (hp_ne_top : p != ∞) (P : Lp F p μ -> Prop)
    (h_ind : forall (c : F) {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s < ∞),
      P (Lp.simpleFunc.indicatorConst p (hm s hs) hμs.ne c))
    (h_add : forall ⦃f g⦄, forall hf : MemLp f p μ, forall hg : MemLp g p μ, AEStronglyMeasurable[m] f μ ->
      AEStronglyMeasurable[m] g μ -> Disjoint (Function.support f) (Function.support g) ->
        P (hf.toLp f) -> P (hg.toLp g) -> P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed {f : lpMeas F Real m p μ | P f}) :
    forall f : Lp F p μ, AEStronglyMeasurable[m] f μ -> P f := by
  intro f hf
  let f' := (⟨f, hf⟩ : lpMeas F Real m p μ)
  let g := lpMeasToLpTrimLie F Real p μ hm f'
  have hfg : f' = (lpMeasToLpTrimLie F Real p μ hm).symm g := by
    simp only [f', g, LinearIsometryEquiv.symm_apply_apply]
  change P ↑f'
  rw [hfg]
  refine
    @Lp.induction α F m _ p (μ.trim hm) _ hp_ne_top
      (fun g => P ((lpMeasToLpTrimLie F Real p μ hm).symm g)) ?_ ?_ ?_ g
  · intro b t ht hμt
    rw [@Lp.simpleFunc.coe_indicatorConst _ _ m]; rw [lpMeasToLpTrimLie_symm_indicator ht hμt.ne b]
    have hμt' : μ t < ∞ := (le_trim hm).trans_lt hμt
    specialize h_ind b ht hμt'
    rwa [Lp.simpleFunc.coe_indicatorConst] at h_ind
  · intro f g hf hg h_disj hfP hgP
    rw [LinearIsometryEquiv.map_add]
    push_cast
    have h_eq :
      forall (f : α -> F) (hf : MemLp f p (μ.trim hm)),
        ((lpMeasToLpTrimLie F Real p μ hm).symm (MemLp.toLp f hf) : Lp F p μ) =
          (memLp_of_memLp_trim hm hf).toLp f :=
      lpMeasToLpTrimLie_symm_toLp hm
    rw [h_eq f hf] at hfP ⊢
    rw [h_eq g hg] at hgP ⊢
    exact h_add (memLp_of_memLp_trim hm hf) (memLp_of_memLp_trim hm hg)
      (hf.aestronglyMeasurable.of_trim hm) (hg.aestronglyMeasurable.of_trim hm) h_disj hfP hgP
  · change IsClosed ((lpMeasToLpTrimLie F Real p μ hm).symm ⁻¹' {g : lpMeas F Real m p μ | P ↑g})
    exact IsClosed.preimage (LinearIsometryEquiv.continuous _) h_closed

set_option backward.isDefEq.respectTransparency false in
/-- To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.
-/
@[elab_as_elim]
/--
theorem `Lp.induction_stronglyMeasurable` / 定理 `Lp.induction_stronglyMeasurable`

English:
theorem Lp.induction_stronglyMeasurable
  statement: (hm : m <= m0) (hp_ne_top : p != ∞) (P : Lp F p μ -> Prop)
  proof: by
  intro f hf
  suffices h_add_ae :
    forall ⦃f g⦄, forall hf : MemLp f p μ, forall hg : MemLp g p μ, AEStronglyMeasurable[m] f μ ->
      AEStronglyMeasurable[m] g μ -> Disjoint (Function.support f) (Function.support g) ->
        P (hf.toLp f) -> P (hg.toLp g) -> P (hf.toLp f + hg.toLp g) from

中文:
定理 Lp.induction_stronglyMeasurable
  结论: (hm : m <= m0) (hp_ne_top : p != ∞) (P : Lp F p μ -> 命题)
  证明: by
  intro f hf
  suffices h_add_ae :
    forall ⦃f g⦄, forall hf : MemLp f p μ, forall hg : MemLp g p μ, AEStronglyMeasurable[m] f μ ->
      AEStronglyMeasurable[m] g μ -> Disjoint (Function.support f) (Function.support g) ->
        P (hf.toLp f) -> P (hg.toLp g) -> P (hf.toLp f + hg.toLp g) from

Depends on / 依赖: AEStronglyMeasurable, Disjoint, Function, Function.support, Lp.induction_stronglyMeasurable_aux, MeasurableSet, h_add_ae, h_closed, h_disj, h_ind, hf.toLp, hfm.mk, hfm.stronglyMeasura, hg.toLp, hp_ne_top, hs_f, induction_stronglyMeasurable_aux, stronglyMeasura, support
-/
theorem Lp.induction_stronglyMeasurable (hm : m <= m0) (hp_ne_top : p != ∞) (P : Lp F p μ -> Prop)
    (h_ind : forall (c : F) {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s < ∞),
      P (Lp.simpleFunc.indicatorConst p (hm s hs) hμs.ne c))
    (h_add : forall ⦃f g⦄, forall hf : MemLp f p μ, forall hg : MemLp g p μ, StronglyMeasurable[m] f ->
      StronglyMeasurable[m] g -> Disjoint (Function.support f) (Function.support g) ->
        P (hf.toLp f) -> P (hg.toLp g) -> P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed {f : lpMeas F Real m p μ | P f}) :
    forall f : Lp F p μ, AEStronglyMeasurable[m] f μ -> P f := by
  intro f hf
  suffices h_add_ae :
    forall ⦃f g⦄, forall hf : MemLp f p μ, forall hg : MemLp g p μ, AEStronglyMeasurable[m] f μ ->
      AEStronglyMeasurable[m] g μ -> Disjoint (Function.support f) (Function.support g) ->
        P (hf.toLp f) -> P (hg.toLp g) -> P (hf.toLp f + hg.toLp g) from
    Lp.induction_stronglyMeasurable_aux hm hp_ne_top _ h_ind h_add_ae h_closed f hf
  intro f g hf hg hfm hgm h_disj hPf hPg
  let s_f : Set α := Function.support (hfm.mk f)
  have hs_f : MeasurableSet[m] s_f := hfm.stronglyMeasurable_mk.measurableSet_support
  have hs_f_eq : s_f =ᵐ[μ] Function.support f := hfm.ae_eq_mk.symm.support
  let s_g : Set α := Function.support (hgm.mk g)
  have hs_g : MeasurableSet[m] s_g := hgm.stronglyMeasurable_mk.measurableSet_support
  have hs_g_eq : s_g =ᵐ[μ] Function.support g := hgm.ae_eq_mk.symm.support
  have h_inter_empty : (s_f inter s_g : Set α) =ᵐ[μ] (∅ : Set α) := by
    refine (hs_f_eq.inter hs_g_eq).trans ?_
    suffices Function.support f inter Function.support g = ∅ by rw [this]
    exact Set.disjoint_iff_inter_eq_empty.mp h_disj
  let f' := (s_f \ s_g).indicator (hfm.mk f)
  have hff' : f =ᵐ[μ] f' := by
    have : s_f \ s_g =ᵐ[μ] s_f := by
      rw [← Set.sdiff_inter_self_eq_sdiff]; rw [Set.inter_comm]
      refine ((ae_eq_refl s_f).diff h_inter_empty).trans ?_
      rw [Set.sdiff_empty]
    refine ((indicator_ae_eq_of_ae_eq_set this).trans ?_).symm
    rw [Set.indicator_support]
    exact hfm.ae_eq_mk.symm
  have hf'_meas : StronglyMeasurable[m] f' := hfm.stronglyMeasurable_mk.indicator (hs_f.diff hs_g)
  have hf'_Lp : MemLp f' p μ := hf.ae_eq hff'
  let g' := (s_g \ s_f).indicator (hgm.mk g)
  have hgg' : g =ᵐ[μ] g' := by
    have : s_g \ s_f =ᵐ[μ] s_g := by
      rw [← Set.sdiff_inter_self_eq_sdiff]
      refine ((ae_eq_refl s_g).diff h_inter_empty).trans ?_
      rw [Set.sdiff_empty]
    refine ((indicator_ae_eq_of_ae_eq_set this).trans ?_).symm
    rw [Set.indicator_support]
    exact hgm.ae_eq_mk.symm
  have hg'_meas : StronglyMeasurable[m] g' := hgm.stronglyMeasurable_mk.indicator (hs_g.diff hs_f)
  have hg'_Lp : MemLp g' p μ := hg.ae_eq hgg'
  have h_disj : Disjoint (Function.support f') (Function.support g') :=
    haveI : Disjoint (s_f \ s_g) (s_g \ s_f) := disjoint_sdiff_sdiff
    this.mono Set.support_indicator_subset Set.support_indicator_subset
  rw [← MemLp.toLp_congr hf'_Lp hf hff'.symm] at hPf ⊢
  rw [← MemLp.toLp_congr hg'_Lp hg hgg'.symm] at hPg ⊢
  exact h_add hf'_Lp hg'_Lp hf'_meas hg'_meas h_disj hPf hPg

/-- To prove something for an arbitrary `MemLp` function a.e. strongly measurable with respect
to a sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in the `Lᵖ` space strongly measurable w.r.t. `m` for which the property
  holds is closed.
* the property is closed under the almost-everywhere equal relation.
-/
@[elab_as_elim]
/--
theorem `MemLp.induction_stronglyMeasurable` / 定理 `MemLp.induction_stronglyMeasurable`

English:
theorem MemLp.induction_stronglyMeasurable
  statement: (hm : m <= m0) (hp_ne_top : p != ∞) (P : (α -> F) -> Prop)
  proof: by
  intro f hf hfm
  let f_Lp := hf.toLp f
  have hfm_Lp : AEStronglyMeasurable[m] f_Lp μ := hfm.congr hf.coeFn_toLp.symm
  refine h_ae hf.coeFn_toLp (Lp.memLp _) ?_
  change P f_Lp
  refine Lp.induction_stronglyMeasurable hm hp_ne_top (fun f => P f) ?_ ?_ h_closed f_Lp hfm_Lp
  · intro c s hs hμs


中文:
定理 MemLp.induction_stronglyMeasurable
  结论: (hm : m <= m0) (hp_ne_top : p != ∞) (P : (α -> F) -> 命题)
  证明: by
  intro f hf hfm
  let f_Lp := hf.toLp f
  have hfm_Lp : AEStronglyMeasurable[m] f_Lp μ := hfm.congr hf.coeFn_toLp.symm
  refine h_ae hf.coeFn_toLp (Lp.memLp _) ?_
  change P f_Lp
  refine Lp.induction_stronglyMeasurable hm hp_ne_top (fun f => P f) ?_ ?_ h_closed f_Lp hfm_Lp
  · intro c s hs hμs


Depends on / 依赖: AEStronglyMeasurable, Lp.induction_stronglyMeasurable, Lp.memLp, Lp.simpleFunc.coe_indicatorConst, Or.inr, coeFn_toLp, coe_indicatorConst, f_Lp, h_ae, h_closed, h_disj, h_ind, hf.coeFn_toLp, hf.coeFn_toLp.symm, hf.toLp, hf_mem, hfm.congr, hfm_Lp, hg_mem, hp_ne_top
-/
theorem MemLp.induction_stronglyMeasurable (hm : m <= m0) (hp_ne_top : p != ∞) (P : (α -> F) -> Prop)
    (h_ind : forall (c : F) ⦃s⦄, MeasurableSet[m] s -> μ s < ∞ -> P (s.indicator fun _ => c))
    (h_add : forall ⦃f g : α -> F⦄, Disjoint (Function.support f) (Function.support g) ->
      MemLp f p μ -> MemLp g p μ -> StronglyMeasurable[m] f -> StronglyMeasurable[m] g ->
        P f -> P g -> P (f + g))
    (h_closed : IsClosed {f : lpMeas F Real m p μ | P f})
    (h_ae : forall ⦃f g⦄, f =ᵐ[μ] g -> MemLp f p μ -> P f -> P g) :
    forall ⦃f : α -> F⦄, MemLp f p μ -> AEStronglyMeasurable[m] f μ -> P f := by
  intro f hf hfm
  let f_Lp := hf.toLp f
  have hfm_Lp : AEStronglyMeasurable[m] f_Lp μ := hfm.congr hf.coeFn_toLp.symm
  refine h_ae hf.coeFn_toLp (Lp.memLp _) ?_
  change P f_Lp
  refine Lp.induction_stronglyMeasurable hm hp_ne_top (fun f => P f) ?_ ?_ h_closed f_Lp hfm_Lp
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    refine h_ae indicatorConstLp_coeFn.symm ?_ (h_ind c hs hμs)
    exact memLp_indicator_const p (hm s hs) c (Or.inr hμs.ne)
  · intro f g hf_mem hg_mem hfm hgm h_disj hfP hgP
    have hfP' : P f := h_ae hf_mem.coeFn_toLp (Lp.memLp _) hfP
    have hgP' : P g := h_ae hg_mem.coeFn_toLp (Lp.memLp _) hgP
    specialize h_add h_disj hf_mem hg_mem hfm hgm hfP' hgP'
    refine h_ae ?_ (hf_mem.add hg_mem) h_add
    exact (hf_mem.coeFn_toLp.symm.add hg_mem.coeFn_toLp.symm).trans (Lp.coeFn_add _ _).symm

end Induction

end MeasureTheory
