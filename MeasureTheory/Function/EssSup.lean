/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Probability.UniformOn

/-!
# Essential supremum and infimum

We define the essential supremum and infimum of a function `f : α → β` with respect to a measure
`μ` on `α`. The essential supremum is the infimum of the constants `c : β` such that `f x ≤ c`
almost everywhere.

TODO: The essential supremum of functions `α → ℝ≥0∞` is used in particular to define the norm in
the `L∞` space (see `Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`).

There is a different quantity which is sometimes also called essential supremum: the least
upper-bound among measurable functions of a family of measurable functions (in an almost-everywhere
sense). We do not define that quantity here, which is simply the supremum of a map with values in
`α →ₘ[μ] β` (see `Mathlib/MeasureTheory/Function/AEEqFun.lean`).

## Main definitions

* `essSup f μ := (ae μ).limsup f`
* `essInf f μ := (ae μ).liminf f`
-/

@[expose] public section


open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {α β : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β] {f : α -> β}

/--
Definition of `essSup` / `essSup` 的定义

English:
definition essSup
  signature: {_ : MeasurableSpace α} (f : α -> β) (μ : Measure α)
  body: (ae μ).limsup f

中文:
定义 essSup
  签名: {_ : MeasurableSpace α} (f : α -> β) (μ : Measure α)
  定义体: (ae μ).limsup f

Depends on / 依赖: limsup
-/
def essSup {_ : MeasurableSpace α} (f : α -> β) (μ : Measure α) :=
  (ae μ).limsup f

/--
Definition of `essInf` / `essInf` 的定义

English:
definition essInf
  signature: {_ : MeasurableSpace α} (f : α -> β) (μ : Measure α)
  body: (ae μ).liminf f

中文:
定义 essInf
  签名: {_ : MeasurableSpace α} (f : α -> β) (μ : Measure α)
  定义体: (ae μ).liminf f

Depends on / 依赖: liminf
-/
def essInf {_ : MeasurableSpace α} (f : α -> β) (μ : Measure α) :=
  (ae μ).liminf f

/--
theorem `essSup_congr_ae` / 定理 `essSup_congr_ae`

English:
theorem essSup_congr_ae
  given: {f g : α -> β} (hfg : f =ᵐ[μ] g)
  statement: essSup f μ = essSup g μ
  proof: limsup_congr hfg

中文:
定理 essSup_congr_ae
  条件: {f g : α -> β} (hfg : f =ᵐ[μ] g)
  结论: essSup f μ = essSup g μ
  证明: limsup_congr hfg

Depends on / 依赖: limsup_congr
-/
theorem essSup_congr_ae {f g : α -> β} (hfg : f =ᵐ[μ] g) : essSup f μ = essSup g μ :=
  limsup_congr hfg

/--
theorem `essInf_congr_ae` / 定理 `essInf_congr_ae`

English:
theorem essInf_congr_ae
  given: {f g : α -> β} (hfg : f =ᵐ[μ] g)
  statement: essInf f μ = essInf g μ
  proof: @essSup_congr_ae α βᵒᵈ _ _ _ _ _ hfg

@[simp]

中文:
定理 essInf_congr_ae
  条件: {f g : α -> β} (hfg : f =ᵐ[μ] g)
  结论: essInf f μ = essInf g μ
  证明: @essSup_congr_ae α βᵒᵈ _ _ _ _ _ hfg

@[simp]

Depends on / 依赖: essSup_congr_ae
-/
theorem essInf_congr_ae {f g : α -> β} (hfg : f =ᵐ[μ] g) : essInf f μ = essInf g μ :=
  @essSup_congr_ae α βᵒᵈ _ _ _ _ _ hfg

@[simp]
/--
theorem `essSup_const'` / 定理 `essSup_const'`

English:
theorem essSup_const'
  given: [NeZero μ] (c : β)
  statement: essSup (fun _ : α => c) μ = c
  proof: limsup_const _

@[simp]

中文:
定理 essSup_const'
  条件: [NeZero μ] (c : β)
  结论: essSup (fun _ : α => c) μ = c
  证明: limsup_const _

@[simp]

Depends on / 依赖: limsup_const
-/
theorem essSup_const' [NeZero μ] (c : β) : essSup (fun _ : α => c) μ = c :=
  limsup_const _

@[simp]
/--
theorem `essInf_const'` / 定理 `essInf_const'`

English:
theorem essInf_const'
  given: [NeZero μ] (c : β)
  statement: essInf (fun _ : α => c) μ = c
  proof: liminf_const _

中文:
定理 essInf_const'
  条件: [NeZero μ] (c : β)
  结论: essInf (fun _ : α => c) μ = c
  证明: liminf_const _

Depends on / 依赖: liminf_const
-/
theorem essInf_const' [NeZero μ] (c : β) : essInf (fun _ : α => c) μ = c :=
  liminf_const _

/--
theorem `essSup_const` / 定理 `essSup_const`

English:
theorem essSup_const
  given: (c : β) (hμ : μ != 0)
  statement: essSup (fun _ : α => c) μ = c
  proof: have := NeZero.mk hμ; essSup_const' _

中文:
定理 essSup_const
  条件: (c : β) (hμ : μ != 0)
  结论: essSup (fun _ : α => c) μ = c
  证明: have := NeZero.mk hμ; essSup_const' _

Depends on / 依赖: NeZero, NeZero.mk, essSup_const
-/
theorem essSup_const (c : β) (hμ : μ != 0) : essSup (fun _ : α => c) μ = c :=
  have := NeZero.mk hμ; essSup_const' _

/--
theorem `essInf_const` / 定理 `essInf_const`

English:
theorem essInf_const
  given: (c : β) (hμ : μ != 0)
  statement: essInf (fun _ : α => c) μ = c
  proof: have := NeZero.mk hμ; essInf_const' _

中文:
定理 essInf_const
  条件: (c : β) (hμ : μ != 0)
  结论: essInf (fun _ : α => c) μ = c
  证明: have := NeZero.mk hμ; essInf_const' _

Depends on / 依赖: NeZero, NeZero.mk, essInf_const
-/
theorem essInf_const (c : β) (hμ : μ != 0) : essInf (fun _ : α => c) μ = c :=
  have := NeZero.mk hμ; essInf_const' _

section SMul
variable {R : Type*} [Semiring R] [IsDomain R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  [Module.IsTorsionFree R Real>=0∞] {c : R}

@[simp]
/--
lemma `essSup_smul_measure` / 引理 `essSup_smul_measure`

English:
lemma essSup_smul_measure
  given: (hc : c != 0) (f : α -> β)
  statement: essSup f (c • μ) = essSup f μ
  proof: by
  simp_rw [essSup, Measure.ae_smul_measure_eq hc]

中文:
引理 essSup_smul_measure
  条件: (hc : c != 0) (f : α -> β)
  结论: essSup f (c • μ) = essSup f μ
  证明: by
  simp_rw [essSup, Measure.ae_smul_measure_eq hc]

Depends on / 依赖: Measure, Measure.ae_smul_measure_eq, ae_smul_measure_eq, essSup, simp_rw
-/
lemma essSup_smul_measure (hc : c != 0) (f : α -> β) : essSup f (c • μ) = essSup f μ := by
  simp_rw [essSup, Measure.ae_smul_measure_eq hc]

end SMul

@[simp]
/--
lemma `essSup_ennreal_smul_measure` / 引理 `essSup_ennreal_smul_measure`

English:
lemma essSup_ennreal_smul_measure
  given: {c : Real>=0∞} (hc : c != 0) (f : α -> β)
  proof: by
  simp_rw [essSup, Measure.ae_ennreal_smul_measure_eq hc]

中文:
引理 essSup_ennreal_smul_measure
  条件: {c : 实数>=0∞} (hc : c != 0) (f : α -> β)
  证明: by
  simp_rw [essSup, Measure.ae_ennreal_smul_measure_eq hc]

Depends on / 依赖: Measure, Measure.ae_ennreal_smul_measure_eq, ae_ennreal_smul_measure_eq, essSup, simp_rw
-/
lemma essSup_ennreal_smul_measure {c : Real>=0∞} (hc : c != 0) (f : α -> β) :
    essSup f (c • μ) = essSup f μ := by
  simp_rw [essSup, Measure.ae_ennreal_smul_measure_eq hc]

/--
theorem `essSup_mono_ae` / 定理 `essSup_mono_ae`

English:
theorem essSup_mono_ae
  statement: {f g : α -> β} (hfg : f <=ᵐ[μ] g)
  proof: limsup_le_limsup hfg hf hg

中文:
定理 essSup_mono_ae
  结论: {f g : α -> β} (hfg : f <=ᵐ[μ] g)
  证明: limsup_le_limsup hfg hf hg

Depends on / 依赖: IsBoundedUnder, essSup, isBoundedDefault, limsup_le_limsup
-/
theorem essSup_mono_ae {f g : α -> β} (hfg : f <=ᵐ[μ] g)
    (hf : IsCoboundedUnder (· <= ·) (ae μ) f := by isBoundedDefault)
    (hg : IsBoundedUnder (· <= ·) (ae μ) g := by isBoundedDefault) :
    essSup f μ <= essSup g μ :=
  limsup_le_limsup hfg hf hg

/--
theorem `essInf_mono_ae` / 定理 `essInf_mono_ae`

English:
theorem essInf_mono_ae
  statement: {f g : α -> β} (hfg : f <=ᵐ[μ] g)
  proof: liminf_le_liminf hfg hf hg

中文:
定理 essInf_mono_ae
  结论: {f g : α -> β} (hfg : f <=ᵐ[μ] g)
  证明: liminf_le_liminf hfg hf hg

Depends on / 依赖: IsCoboundedUnder, essInf, isBoundedDefault, liminf_le_liminf
-/
theorem essInf_mono_ae {f g : α -> β} (hfg : f <=ᵐ[μ] g)
    (hf : IsBoundedUnder (· >= ·) (ae μ) f := by isBoundedDefault)
    (hg : IsCoboundedUnder (· >= ·) (ae μ) g := by isBoundedDefault) :
    essInf f μ <= essInf g μ :=
  liminf_le_liminf hfg hf hg

/--
theorem `essSup_le_of_ae_le` / 定理 `essSup_le_of_ae_le`

English:
theorem essSup_le_of_ae_le
  statement: {f : α -> β} (c : β) (hf : f <=ᵐ[μ] fun _ => c)
  proof: limsup_le_of_le hfbdd hf

中文:
定理 essSup_le_of_ae_le
  结论: {f : α -> β} (c : β) (hf : f <=ᵐ[μ] fun _ => c)
  证明: limsup_le_of_le hfbdd hf

Depends on / 依赖: essSup, isBoundedDefault, limsup_le_of_le
-/
theorem essSup_le_of_ae_le {f : α -> β} (c : β) (hf : f <=ᵐ[μ] fun _ => c)
    (hfbdd : IsCoboundedUnder (· <= ·) (ae μ) f := by isBoundedDefault) :
    essSup f μ <= c :=
  limsup_le_of_le hfbdd hf

/--
theorem `le_essInf_of_ae_le` / 定理 `le_essInf_of_ae_le`

English:
theorem le_essInf_of_ae_le
  statement: {f : α -> β} (c : β) (hf : (fun _ => c) <=ᵐ[μ] f)
  proof: le_liminf_of_le hfbdd hf

中文:
定理 le_essInf_of_ae_le
  结论: {f : α -> β} (c : β) (hf : (fun _ => c) <=ᵐ[μ] f)
  证明: le_liminf_of_le hfbdd hf

Depends on / 依赖: essInf, isBoundedDefault, le_liminf_of_le
-/
theorem le_essInf_of_ae_le {f : α -> β} (c : β) (hf : (fun _ => c) <=ᵐ[μ] f)
    (hfbdd : IsCoboundedUnder (· >= ·) (ae μ) f := by isBoundedDefault) :
    c <= essInf f μ :=
  le_liminf_of_le hfbdd hf

/--
theorem `OrderIso.essSup_apply` / 定理 `OrderIso.essSup_apply`

English:
theorem OrderIso.essSup_apply
  statement: {_ : MeasurableSpace α} {γ} [ConditionallyCompleteLattice γ]
  proof: OrderIso.limsup_apply g hf hf_co hgf hgf_co

中文:
定理 OrderIso.essSup_apply
  结论: {_ : MeasurableSpace α} {γ} [ConditionallyCompleteLattice γ]
  证明: OrderIso.limsup_apply g hf hf_co hgf hgf_co

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, OrderIso, OrderIso.limsup_apply, essSup, hf_co, hgf_co, isBoundedDefault, limsup_apply
-/
theorem OrderIso.essSup_apply {_ : MeasurableSpace α} {γ} [ConditionallyCompleteLattice γ]
    (f : α -> β) (μ : Measure α) (g : β ≃o γ)
    (hf : IsBoundedUnder (· <= ·) (ae μ) f := by isBoundedDefault)
    (hf_co : IsCoboundedUnder (· <= ·) (ae μ) f := by isBoundedDefault)
    (hgf : IsBoundedUnder (· <= ·) (ae μ) (fun x => g (f x)) := by isBoundedDefault)
    (hgf_co : IsCoboundedUnder (· <= ·) (ae μ) (fun x => g (f x)) := by
      isBoundedDefault) :
    g (essSup f μ) = essSup (fun x => g (f x)) μ :=
  OrderIso.limsup_apply g hf hf_co hgf hgf_co

/--
theorem `OrderIso.essInf_apply` / 定理 `OrderIso.essInf_apply`

English:
theorem OrderIso.essInf_apply
  statement: {_ : MeasurableSpace α} {γ} [ConditionallyCompleteLattice γ]
  proof: OrderIso.liminf_apply g hf hf_co hgf hgf_co

中文:
定理 OrderIso.essInf_apply
  结论: {_ : MeasurableSpace α} {γ} [ConditionallyCompleteLattice γ]
  证明: OrderIso.liminf_apply g hf hf_co hgf hgf_co

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, OrderIso, OrderIso.liminf_apply, essInf, hf_co, hgf_co, isBoundedDefault, liminf_apply
-/
theorem OrderIso.essInf_apply {_ : MeasurableSpace α} {γ} [ConditionallyCompleteLattice γ]
    (f : α -> β) (μ : Measure α) (g : β ≃o γ)
    (hf : IsBoundedUnder (· >= ·) (ae μ) f := by isBoundedDefault)
    (hf_co : IsCoboundedUnder (· >= ·) (ae μ) f := by isBoundedDefault)
    (hgf : IsBoundedUnder (· >= ·) (ae μ) (fun x => g (f x)) := by isBoundedDefault)
    (hgf_co : IsCoboundedUnder (· >= ·) (ae μ) (fun x => g (f x)) := by
      isBoundedDefault) :
    g (essInf f μ) = essInf (fun x => g (f x)) μ :=
  OrderIso.liminf_apply g hf hf_co hgf hgf_co

/--
theorem `essSup_mono_measure` / 定理 `essSup_mono_measure`

English:
theorem essSup_mono_measure
  statement: {f : α -> β} (hμν : ν ≪ μ)
  proof: limsup_le_limsup_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) hνf hμf

中文:
定理 essSup_mono_measure
  结论: {f : α -> β} (hμν : ν ≪ μ)
  证明: limsup_le_limsup_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) hνf hμf

Depends on / 依赖: IsBoundedUnder, Measure, Measure.ae_le_iff_absolutelyContinuous.mpr, ae_le_iff_absolutelyContinuous, essSup, isBoundedDefault, limsup_le_limsup_of_le
-/
theorem essSup_mono_measure {f : α -> β} (hμν : ν ≪ μ)
    (hνf : IsCoboundedUnder (· <= ·) (ae ν) f := by isBoundedDefault)
    (hμf : IsBoundedUnder (· <= ·) (ae μ) f := by isBoundedDefault) :
    essSup f ν <= essSup f μ :=
  limsup_le_limsup_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) hνf hμf

/--
theorem `essSup_mono_measure'` / 定理 `essSup_mono_measure'`

English:
theorem essSup_mono_measure'
  statement: {f : α -> β} (hμν : ν <= μ)
  proof: essSup_mono_measure (Measure.absolutelyContinuous_of_le hμν) hνf hμf

中文:
定理 essSup_mono_measure'
  结论: {f : α -> β} (hμν : ν <= μ)
  证明: essSup_mono_measure (Measure.absolutelyContinuous_of_le hμν) hνf hμf

Depends on / 依赖: IsBoundedUnder, Measure, Measure.absolutelyContinuous_of_le, absolutelyContinuous_of_le, essSup, essSup_mono_measure, isBoundedDefault
-/
theorem essSup_mono_measure' {f : α -> β} (hμν : ν <= μ)
    (hνf : IsCoboundedUnder (· <= ·) (ae ν) f := by isBoundedDefault)
    (hμf : IsBoundedUnder (· <= ·) (ae μ) f := by isBoundedDefault) :
    essSup f ν <= essSup f μ :=
  essSup_mono_measure (Measure.absolutelyContinuous_of_le hμν) hνf hμf

/--
theorem `essInf_antitone_measure` / 定理 `essInf_antitone_measure`

English:
theorem essInf_antitone_measure
  statement: {f : α -> β} (hμν : μ ≪ ν)
  proof: liminf_le_liminf_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) hνf hμf

中文:
定理 essInf_antitone_measure
  结论: {f : α -> β} (hμν : μ ≪ ν)
  证明: liminf_le_liminf_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) hνf hμf

Depends on / 依赖: IsCoboundedUnder, Measure, Measure.ae_le_iff_absolutelyContinuous.mpr, ae_le_iff_absolutelyContinuous, essInf, isBoundedDefault, liminf_le_liminf_of_le
-/
theorem essInf_antitone_measure {f : α -> β} (hμν : μ ≪ ν)
    (hνf : IsBoundedUnder (· >= ·) (ae ν) f := by isBoundedDefault)
    (hμf : IsCoboundedUnder (· >= ·) (ae μ) f := by isBoundedDefault) :
    essInf f ν <= essInf f μ :=
  liminf_le_liminf_of_le (Measure.ae_le_iff_absolutelyContinuous.mpr hμν) hνf hμf

section TopologicalSpace

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : α -> γ} {g : γ -> β}

/--
theorem `essSup_comp_le_essSup_map_measure` / 定理 `essSup_comp_le_essSup_map_measure`

English:
theorem essSup_comp_le_essSup_map_measure
  statement: (hf : AEMeasurable f μ)
  proof: by
  refine limsSup_le_limsSup_of_le ?_ hgf hg
  rw [← map_map]
  exact map_mono (Measure.tendsto_ae_map hf)

中文:
定理 essSup_comp_le_essSup_map_measure
  结论: (hf : AEMeasurable f μ)
  证明: by
  refine limsSup_le_limsSup_of_le ?_ hgf hg
  rw [← map_map]
  exact map_mono (Measure.tendsto_ae_map hf)

Depends on / 依赖: IsBoundedUnder, Measure, Measure.map, Measure.tendsto_ae_map, essSup, isBoundedDefault, limsSup_le_limsSup_of_le, map_map, map_mono, tendsto_ae_map
-/
theorem essSup_comp_le_essSup_map_measure (hf : AEMeasurable f μ)
    (hgf : IsCoboundedUnder (· <= ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hg : IsBoundedUnder (· <= ·) (ae (Measure.map f μ)) g := by isBoundedDefault) :
    essSup (g ∘ f) μ <= essSup g (Measure.map f μ) := by
  refine limsSup_le_limsSup_of_le ?_ hgf hg
  rw [← map_map]
  exact map_mono (Measure.tendsto_ae_map hf)

/--
theorem `MeasurableEmbedding.essSup_map_measure` / 定理 `MeasurableEmbedding.essSup_map_measure`

English:
theorem MeasurableEmbedding.essSup_map_measure
  statement: (hf : MeasurableEmbedding f)
  proof: by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf.measurable.aemeasurable hgf_co hg)
  refine limsSup_le_limsSup hg_co hgf (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  exact hf.ae_map_iff.mpr h_le

中文:
定理 MeasurableEmbedding.essSup_map_measure
  结论: (hf : MeasurableEmbedding f)
  证明: by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf.measurable.aemeasurable hgf_co hg)
  refine limsSup_le_limsSup hg_co hgf (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  exact hf.ae_map_iff.mpr h_le

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, Measure, Measure.map, ae_map_iff, aemeasurable, essSup, essSup_comp_le_essSup_map_measure, eventually_map, h_le, hf.ae_map_iff.m, hf.measurable.aemeasurable, hg_co, hgf_co, isBoundedDefault, le_antisymm, limsSup_le_limsSup, measurable
-/
theorem MeasurableEmbedding.essSup_map_measure (hf : MeasurableEmbedding f)
    (hg_co : IsCoboundedUnder (· <= ·) (ae (Measure.map f μ)) g := by isBoundedDefault)
    (hgf : IsBoundedUnder (· <= ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hgf_co : IsCoboundedUnder (· <= ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hg : IsBoundedUnder (· <= ·) (ae (Measure.map f μ)) g := by isBoundedDefault) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf.measurable.aemeasurable hgf_co hg)
  refine limsSup_le_limsSup hg_co hgf (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  exact hf.ae_map_iff.mpr h_le

variable [MeasurableSpace β] [TopologicalSpace β] [SecondCountableTopology β]
  [OrderClosedTopology β] [OpensMeasurableSpace β]

/--
theorem `essSup_map_measure_of_measurable` / 定理 `essSup_map_measure_of_measurable`

English:
theorem essSup_map_measure_of_measurable
  statement: (hg : Measurable g) (hf : AEMeasurable f μ)
  proof: by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf hgf_co hg_bdd)
  refine limsSup_le_limsSup hg_co hgf (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  rw [ae_map_iff hf (measurableSet_le hg measurable_const)]
  exact h_le

中文:
定理 essSup_map_measure_of_measurable
  结论: (hg : Measurable g) (hf : AEMeasurable f μ)
  证明: by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf hgf_co hg_bdd)
  refine limsSup_le_limsSup hg_co hgf (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  rw [ae_map_iff hf (measurableSet_le hg measurable_const)]
  exact h_le

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, Measure, Measure.map, ae_map_iff, essSup, essSup_comp_le_essSup_map_measure, eventually_map, h_le, hg_bdd, hg_co, hgf_co, isBoundedDefault, le_antisymm, limsSup_le_limsSup, measurableSet_le
-/
theorem essSup_map_measure_of_measurable (hg : Measurable g) (hf : AEMeasurable f μ)
    (hg_co : IsCoboundedUnder (· <= ·) (ae (Measure.map f μ)) g := by isBoundedDefault)
    (hgf : IsBoundedUnder (· <= ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hgf_co : IsCoboundedUnder (· <= ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hg_bdd : IsBoundedUnder (· <= ·) (ae (Measure.map f μ)) g := by isBoundedDefault) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  refine le_antisymm ?_ (essSup_comp_le_essSup_map_measure hf hgf_co hg_bdd)
  refine limsSup_le_limsSup hg_co hgf (fun c h_le => ?_)
  rw [eventually_map] at h_le ⊢
  rw [ae_map_iff hf (measurableSet_le hg measurable_const)]
  exact h_le

/--
theorem `essSup_map_measure` / 定理 `essSup_map_measure`

English:
theorem essSup_map_measure
  statement: (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ)
  proof: by
  have hg_mk_co : IsCoboundedUnder (· <= ·) (ae (Measure.map f μ)) (hg.mk g) := by
    simpa [IsCoboundedUnder, ← map_congr hg.ae_eq_mk]
  have hg_mk_bdd : IsBoundedUnder (· <= ·) (ae (Measure.map f μ)) (hg.mk g) := by
    simpa [IsBoundedUnder, ← map_congr hg.ae_eq_mk]
  have h_eq := ae_eq_comp 

中文:
定理 essSup_map_measure
  结论: (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ)
  证明: by
  have hg_mk_co : IsCoboundedUnder (· <= ·) (ae (Measure.map f μ)) (hg.mk g) := by
    simpa [IsCoboundedUnder, ← map_congr hg.ae_eq_mk]
  have hg_mk_bdd : IsBoundedUnder (· <= ·) (ae (Measure.map f μ)) (hg.mk g) := by
    simpa [IsBoundedUnder, ← map_congr hg.ae_eq_mk]
  have h_eq := ae_eq_comp 

Depends on / 依赖: IsBoundedUnder, IsCoboundedUnder, Measure, Measure.map, ae_eq_mk, essSup, hg.ae_eq_mk, hg.mk, hg_bdd, hg_mk_bdd, hg_mk_co, hgf_co, isBoundedDefault, map_congr
-/
theorem essSup_map_measure (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ)
    (hg_co : IsCoboundedUnder (· <= ·) (ae (Measure.map f μ)) g := by isBoundedDefault)
    (hgf : IsBoundedUnder (· <= ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hgf_co : IsCoboundedUnder (· <= ·) (ae μ) (g ∘ f) := by isBoundedDefault)
    (hg_bdd : IsBoundedUnder (· <= ·) (ae (Measure.map f μ)) g := by isBoundedDefault) :
    essSup g (Measure.map f μ) = essSup (g ∘ f) μ := by
  have hg_mk_co : IsCoboundedUnder (· <= ·) (ae (Measure.map f μ)) (hg.mk g) := by
    simpa [IsCoboundedUnder, ← map_congr hg.ae_eq_mk]
  have hg_mk_bdd : IsBoundedUnder (· <= ·) (ae (Measure.map f μ)) (hg.mk g) := by
    simpa [IsBoundedUnder, ← map_congr hg.ae_eq_mk]
  have h_eq := ae_eq_comp hf hg.ae_eq_mk
  have hg_mk_f : IsBoundedUnder (· <= ·) (ae μ) ((hg.mk g) ∘ f) := by
    simpa [IsBoundedUnder, ← map_congr h_eq]
  have hg_mk_f_co : IsCoboundedUnder (· <= ·) (ae μ) ((hg.mk g) ∘ f) := by
    simpa [IsCoboundedUnder, ← map_congr h_eq]
  rw [essSup_congr_ae hg.ae_eq_mk]; rw [essSup_map_measure_of_measurable hg.measurable_mk hf hg_mk_co hg_mk_f hg_mk_f_co hg_mk_bdd]
  exact essSup_congr_ae h_eq.symm

end TopologicalSpace

variable [Nonempty α]

/--
lemma `essSup_eq_ciSup` / 引理 `essSup_eq_ciSup`

English:
lemma essSup_eq_ciSup
  given: (hμ : forall a, μ {a} != 0) (hf : BddAbove (Set.range f))
  proof: by rw [essSup, ae_eq_top.2 hμ, limsup_top_eq_ciSup hf]

中文:
引理 essSup_eq_ciSup
  条件: (hμ : 对任意 a, μ {a} != 0) (hf : BddAbove (Set.range f))
  证明: by rw [essSup, ae_eq_top.2 hμ, limsup_top_eq_ciSup hf]

Depends on / 依赖: ae_eq_top, essSup, limsup_top_eq_ciSup
-/
lemma essSup_eq_ciSup (hμ : forall a, μ {a} != 0) (hf : BddAbove (Set.range f)) :
    essSup f μ = ⨆ a, f a := by rw [essSup, ae_eq_top.2 hμ, limsup_top_eq_ciSup hf]

/--
lemma `essInf_eq_ciInf` / 引理 `essInf_eq_ciInf`

English:
lemma essInf_eq_ciInf
  given: (hμ : forall a, μ {a} != 0) (hf : BddBelow (Set.range f))
  proof: by rw [essInf, ae_eq_top.2 hμ, liminf_top_eq_ciInf hf]

中文:
引理 essInf_eq_ciInf
  条件: (hμ : 对任意 a, μ {a} != 0) (hf : BddBelow (Set.range f))
  证明: by rw [essInf, ae_eq_top.2 hμ, liminf_top_eq_ciInf hf]

Depends on / 依赖: ae_eq_top, essInf, liminf_top_eq_ciInf
-/
lemma essInf_eq_ciInf (hμ : forall a, μ {a} != 0) (hf : BddBelow (Set.range f)) :
    essInf f μ = ⨅ a, f a := by rw [essInf, ae_eq_top.2 hμ, liminf_top_eq_ciInf hf]

variable [MeasurableSingletonClass α]

/--
lemma `essSup_count_eq_ciSup` / 引理 `essSup_count_eq_ciSup`

English:
lemma essSup_count_eq_ciSup
  given: (hf : BddAbove (Set.range f))
  proof: essSup_eq_ciSup (by simp) hf

中文:
引理 essSup_count_eq_ciSup
  条件: (hf : BddAbove (Set.range f))
  证明: essSup_eq_ciSup (by simp) hf
-/
@[simp] lemma essSup_count_eq_ciSup (hf : BddAbove (Set.range f)) :
    essSup f .count = ⨆ a, f a := essSup_eq_ciSup (by simp) hf

/--
lemma `essInf_count_eq_ciInf` / 引理 `essInf_count_eq_ciInf`

English:
lemma essInf_count_eq_ciInf
  given: (hf : BddBelow (Set.range f))
  proof: essInf_eq_ciInf (by simp) hf

中文:
引理 essInf_count_eq_ciInf
  条件: (hf : BddBelow (Set.range f))
  证明: essInf_eq_ciInf (by simp) hf
-/
@[simp] lemma essInf_count_eq_ciInf (hf : BddBelow (Set.range f)) :
    essInf f .count = ⨅ a, f a := essInf_eq_ciInf (by simp) hf

/--
lemma `essSup_uniformOn_eq_ciSup` / 引理 `essSup_uniformOn_eq_ciSup`

English:
lemma essSup_uniformOn_eq_ciSup
  given: [Finite α] (hf : BddAbove (Set.range f))
  proof: essSup_eq_ciSup (by simpa [uniformOn, cond_apply]) hf

中文:
引理 essSup_uniformOn_eq_ciSup
  条件: [Finite α] (hf : BddAbove (Set.range f))
  证明: essSup_eq_ciSup (by simpa [uniformOn, cond_apply]) hf
-/
@[simp] lemma essSup_uniformOn_eq_ciSup [Finite α] (hf : BddAbove (Set.range f)) :
    essSup f (uniformOn univ) = ⨆ a, f a :=
  essSup_eq_ciSup (by simpa [uniformOn, cond_apply]) hf

/--
lemma `essInf_cond_count_eq_ciInf` / 引理 `essInf_cond_count_eq_ciInf`

English:
lemma essInf_cond_count_eq_ciInf
  given: [Finite α] (hf : BddBelow (Set.range f))
  proof: essInf_eq_ciInf (by simpa [uniformOn, cond_apply]) hf

中文:
引理 essInf_cond_count_eq_ciInf
  条件: [Finite α] (hf : BddBelow (Set.range f))
  证明: essInf_eq_ciInf (by simpa [uniformOn, cond_apply]) hf
-/
@[simp] lemma essInf_cond_count_eq_ciInf [Finite α] (hf : BddBelow (Set.range f)) :
    essInf f (uniformOn univ) = ⨅ a, f a :=
  essInf_eq_ciInf (by simpa [uniformOn, cond_apply]) hf

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder β] {x : β} {f : α -> β}

/--
theorem `essSup_eq_sInf` / 定理 `essSup_eq_sInf`

English:
theorem essSup_eq_sInf
  given: {m : MeasurableSpace α} (μ : Measure α) (f : α -> β)
  proof: by
  dsimp [essSup, limsup, limsSup]
  simp only [eventually_map, ae_iff, not_le]

中文:
定理 essSup_eq_sInf
  条件: {m : MeasurableSpace α} (μ : Measure α) (f : α -> β)
  证明: by
  dsimp [essSup, limsup, limsSup]
  simp only [eventually_map, ae_iff, not_le]

Depends on / 依赖: ae_iff, essSup, eventually_map, limsSup, limsup, not_le
-/
theorem essSup_eq_sInf {m : MeasurableSpace α} (μ : Measure α) (f : α -> β) :
    essSup f μ = sInf { a | μ { x | a < f x } = 0 } := by
  dsimp [essSup, limsup, limsSup]
  simp only [eventually_map, ae_iff, not_le]

/--
theorem `essInf_eq_sSup` / 定理 `essInf_eq_sSup`

English:
theorem essInf_eq_sSup
  given: {m : MeasurableSpace α} (μ : Measure α) (f : α -> β)
  proof: by
  dsimp [essInf, liminf, limsInf]
  simp only [eventually_map, ae_iff, not_le]

中文:
定理 essInf_eq_sSup
  条件: {m : MeasurableSpace α} (μ : Measure α) (f : α -> β)
  证明: by
  dsimp [essInf, liminf, limsInf]
  simp only [eventually_map, ae_iff, not_le]

Depends on / 依赖: ae_iff, essInf, eventually_map, liminf, limsInf, not_le
-/
theorem essInf_eq_sSup {m : MeasurableSpace α} (μ : Measure α) (f : α -> β) :
    essInf f μ = sSup { a | μ { x | f x < a } = 0 } := by
  dsimp [essInf, liminf, limsInf]
  simp only [eventually_map, ae_iff, not_le]

/--
theorem `ae_lt_of_essSup_lt` / 定理 `ae_lt_of_essSup_lt`

English:
theorem ae_lt_of_essSup_lt
  statement: (hx : essSup f μ < x)
  proof: eventually_lt_of_limsup_lt hx hf

中文:
定理 ae_lt_of_essSup_lt
  结论: (hx : essSup f μ < x)
  证明: eventually_lt_of_limsup_lt hx hf

Depends on / 依赖: eventually_lt_of_limsup_lt, isBoundedDefault
-/
theorem ae_lt_of_essSup_lt (hx : essSup f μ < x)
    (hf : IsBoundedUnder (· <= ·) (ae μ) f := by isBoundedDefault) :
    forallᵐ y ∂μ, f y < x :=
  eventually_lt_of_limsup_lt hx hf

/--
theorem `ae_lt_of_lt_essInf` / 定理 `ae_lt_of_lt_essInf`

English:
theorem ae_lt_of_lt_essInf
  statement: (hx : x < essInf f μ)
  proof: eventually_lt_of_lt_liminf hx hf

中文:
定理 ae_lt_of_lt_essInf
  结论: (hx : x < essInf f μ)
  证明: eventually_lt_of_lt_liminf hx hf

Depends on / 依赖: eventually_lt_of_lt_liminf, isBoundedDefault
-/
theorem ae_lt_of_lt_essInf (hx : x < essInf f μ)
    (hf : IsBoundedUnder (· >= ·) (ae μ) f := by isBoundedDefault) :
    forallᵐ y ∂μ, x < f y :=
  eventually_lt_of_lt_liminf hx hf

variable [TopologicalSpace β] [FirstCountableTopology β] [OrderTopology β]

/--
theorem `ae_le_essSup` / 定理 `ae_le_essSup`

English:
theorem ae_le_essSup
  proof: eventually_le_limsup hf

中文:
定理 ae_le_essSup
  证明: eventually_le_limsup hf

Depends on / 依赖: essSup, eventually_le_limsup, isBoundedDefault
-/
theorem ae_le_essSup
    (hf : IsBoundedUnder (· <= ·) (ae μ) f := by isBoundedDefault) :
    forallᵐ y ∂μ, f y <= essSup f μ :=
  eventually_le_limsup hf

/--
theorem `ae_essInf_le` / 定理 `ae_essInf_le`

English:
theorem ae_essInf_le
  proof: eventually_liminf_le hf

中文:
定理 ae_essInf_le
  证明: eventually_liminf_le hf

Depends on / 依赖: essInf, eventually_liminf_le, isBoundedDefault
-/
theorem ae_essInf_le
    (hf : IsBoundedUnder (· >= ·) (ae μ) f := by isBoundedDefault) :
    forallᵐ y ∂μ, essInf f μ <= f y :=
  eventually_liminf_le hf

/--
theorem `meas_essSup_lt` / 定理 `meas_essSup_lt`

English:
theorem meas_essSup_lt
  proof: by
  simp_rw [← not_le]
  exact ae_le_essSup hf

中文:
定理 meas_essSup_lt
  证明: by
  simp_rw [← not_le]
  exact ae_le_essSup hf

Depends on / 依赖: ae_le_essSup, essSup, isBoundedDefault, not_le, simp_rw
-/
theorem meas_essSup_lt
    (hf : IsBoundedUnder (· <= ·) (ae μ) f := by isBoundedDefault) :
    μ { y | essSup f μ < f y } = 0 := by
  simp_rw [← not_le]
  exact ae_le_essSup hf

/--
theorem `meas_lt_essInf` / 定理 `meas_lt_essInf`

English:
theorem meas_lt_essInf
  proof: by
  simp_rw [← not_le]
  exact ae_essInf_le hf

中文:
定理 meas_lt_essInf
  证明: by
  simp_rw [← not_le]
  exact ae_essInf_le hf

Depends on / 依赖: ae_essInf_le, essInf, isBoundedDefault, not_le, simp_rw
-/
theorem meas_lt_essInf
    (hf : IsBoundedUnder (· >= ·) (ae μ) f := by isBoundedDefault) :
    μ { y | f y < essInf f μ } = 0 := by
  simp_rw [← not_le]
  exact ae_essInf_le hf

end ConditionallyCompleteLinearOrder

section CompleteLattice

variable [CompleteLattice β]

@[simp]
/--
theorem `essSup_measure_zero` / 定理 `essSup_measure_zero`

English:
theorem essSup_measure_zero
  given: {m : MeasurableSpace α} {f : α -> β}
  statement: essSup f (0 : Measure α) = ⊥
  proof: le_bot_iff.mp (sInf_le (by simp))

@[simp]

中文:
定理 essSup_measure_zero
  条件: {m : MeasurableSpace α} {f : α -> β}
  结论: essSup f (0 : Measure α) = ⊥
  证明: le_bot_iff.mp (sInf_le (by simp))

@[simp]

Depends on / 依赖: le_bot_iff, le_bot_iff.mp, sInf_le
-/
theorem essSup_measure_zero {m : MeasurableSpace α} {f : α -> β} : essSup f (0 : Measure α) = ⊥ :=
  le_bot_iff.mp (sInf_le (by simp))

@[simp]
/--
theorem `essInf_measure_zero` / 定理 `essInf_measure_zero`

English:
theorem essInf_measure_zero
  given: {_ : MeasurableSpace α} {f : α -> β}
  statement: essInf f (0 : Measure α) = ⊤
  proof: @essSup_measure_zero α βᵒᵈ _ _ _

中文:
定理 essInf_measure_zero
  条件: {_ : MeasurableSpace α} {f : α -> β}
  结论: essInf f (0 : Measure α) = ⊤
  证明: @essSup_measure_zero α βᵒᵈ _ _ _

Depends on / 依赖: essSup_measure_zero
-/
theorem essInf_measure_zero {_ : MeasurableSpace α} {f : α -> β} : essInf f (0 : Measure α) = ⊤ :=
  @essSup_measure_zero α βᵒᵈ _ _ _

/--
theorem `essSup_const_bot` / 定理 `essSup_const_bot`

English:
theorem essSup_const_bot
  statement: essSup (fun _ : α => (⊥ : β)) μ = (⊥ : β)
  proof: limsup_const_bot

中文:
定理 essSup_const_bot
  结论: essSup (fun _ : α => (⊥ : β)) μ = (⊥ : β)
  证明: limsup_const_bot

Depends on / 依赖: limsup_const_bot
-/
theorem essSup_const_bot : essSup (fun _ : α => (⊥ : β)) μ = (⊥ : β) :=
  limsup_const_bot

/--
theorem `essInf_const_top` / 定理 `essInf_const_top`

English:
theorem essInf_const_top
  statement: essInf (fun _ : α => (⊤ : β)) μ = (⊤ : β)
  proof: liminf_const_top

中文:
定理 essInf_const_top
  结论: essInf (fun _ : α => (⊤ : β)) μ = (⊤ : β)
  证明: liminf_const_top

Depends on / 依赖: liminf_const_top
-/
theorem essInf_const_top : essInf (fun _ : α => (⊤ : β)) μ = (⊤ : β) :=
  liminf_const_top

/--
lemma `essSup_eq_iSup` / 引理 `essSup_eq_iSup`

English:
lemma essSup_eq_iSup
  given: (hμ : forall a, μ {a} != 0) (f : α -> β)
  statement: essSup f μ = ⨆ i, f i
  proof: by
  rw [essSup]; rw [ae_eq_top.2 hμ]; rw [limsup_top_eq_iSup]

中文:
引理 essSup_eq_iSup
  条件: (hμ : 对任意 a, μ {a} != 0) (f : α -> β)
  结论: essSup f μ = ⨆ i, f i
  证明: by
  rw [essSup]; rw [ae_eq_top.2 hμ]; rw [limsup_top_eq_iSup]

Depends on / 依赖: ae_eq_top, essSup, limsup_top_eq_iSup
-/
lemma essSup_eq_iSup (hμ : forall a, μ {a} != 0) (f : α -> β) : essSup f μ = ⨆ i, f i := by
  rw [essSup]; rw [ae_eq_top.2 hμ]; rw [limsup_top_eq_iSup]

/--
lemma `essSup_le_iSup` / 引理 `essSup_le_iSup`

English:
lemma essSup_le_iSup
  given: {f : α -> β}
  statement: essSup f μ <= ⨆ i, f i
  proof: essSup_le_of_ae_le _ (ae_of_all _ (le_iSup f))

中文:
引理 essSup_le_iSup
  条件: {f : α -> β}
  结论: essSup f μ <= ⨆ i, f i
  证明: essSup_le_of_ae_le _ (ae_of_all _ (le_iSup f))

Depends on / 依赖: ae_of_all, essSup_le_of_ae_le, le_iSup
-/
lemma essSup_le_iSup {f : α -> β} : essSup f μ <= ⨆ i, f i :=
  essSup_le_of_ae_le _ (ae_of_all _ (le_iSup f))

/--
lemma `essInf_eq_iInf` / 引理 `essInf_eq_iInf`

English:
lemma essInf_eq_iInf
  given: (hμ : forall a, μ {a} != 0) (f : α -> β)
  statement: essInf f μ = ⨅ i, f i
  proof: by
  rw [essInf]; rw [ae_eq_top.2 hμ]; rw [liminf_top_eq_iInf]

中文:
引理 essInf_eq_iInf
  条件: (hμ : 对任意 a, μ {a} != 0) (f : α -> β)
  结论: essInf f μ = ⨅ i, f i
  证明: by
  rw [essInf]; rw [ae_eq_top.2 hμ]; rw [liminf_top_eq_iInf]

Depends on / 依赖: ae_eq_top, essInf, liminf_top_eq_iInf
-/
lemma essInf_eq_iInf (hμ : forall a, μ {a} != 0) (f : α -> β) : essInf f μ = ⨅ i, f i := by
  rw [essInf]; rw [ae_eq_top.2 hμ]; rw [liminf_top_eq_iInf]

/--
lemma `essSup_count` / 引理 `essSup_count`

English:
lemma essSup_count
  given: [MeasurableSingletonClass α] (f : α -> β)
  statement: essSup f .count = ⨆ i, f i
  proof: essSup_eq_iSup (by simp) _

中文:
引理 essSup_count
  条件: [MeasurableSingletonClass α] (f : α -> β)
  结论: essSup f .count = ⨆ i, f i
  证明: essSup_eq_iSup (by simp) _

Depends on / 依赖: SlashInvariantForm, SlashInvariantForm.funLike, funLike
-/
@[simp] lemma essSup_count [MeasurableSingletonClass α] (f : α -> β) : essSup f .count = ⨆ i, f i :=
  essSup_eq_iSup (by simp) _

/--
lemma `essInf_count` / 引理 `essInf_count`

English:
lemma essInf_count
  given: [MeasurableSingletonClass α] (f : α -> β)
  statement: essInf f .count = ⨅ i, f i
  proof: essInf_eq_iInf (by simp) _

中文:
引理 essInf_count
  条件: [MeasurableSingletonClass α] (f : α -> β)
  结论: essInf f .count = ⨅ i, f i
  证明: essInf_eq_iInf (by simp) _
-/
@[simp] lemma essInf_count [MeasurableSingletonClass α] (f : α -> β) : essInf f .count = ⨅ i, f i :=
  essInf_eq_iInf (by simp) _

end CompleteLattice

section CompleteLinearOrder

variable [CompleteLinearOrder β]

/--
lemma `iSup_eq_essSup` / 引理 `iSup_eq_essSup`

English:
lemma iSup_eq_essSup
  given: {f : α -> β} (h : forall ⦃x a⦄, a < f x -> μ {y | a < f y} != 0)
  proof: by
  apply le_antisymm (iSup_le _) essSup_le_iSup
  intro i
  rw [essSup_eq_sInf]
  apply le_sInf
  intro b hb
  exact not_lt.mp fun a => h a hb

中文:
引理 iSup_eq_essSup
  条件: {f : α -> β} (h : 对任意 ⦃x a⦄, a < f x -> μ {y | a < f y} != 0)
  证明: by
  apply le_antisymm (iSup_le _) essSup_le_iSup
  intro i
  rw [essSup_eq_sInf]
  apply le_sInf
  intro b hb
  exact not_lt.mp fun a => h a hb

Depends on / 依赖: SlashInvariantFormClass, SlashInvariantFormClass.slashInvariantForm, essSup_eq_sInf, essSup_le_iSup, iSup_le, le_antisymm, le_sInf, not_lt, not_lt.mp, slashInvariantForm
-/
lemma iSup_eq_essSup {f : α -> β} (h : forall ⦃x a⦄, a < f x -> μ {y | a < f y} != 0) :
    ⨆ x, f x = essSup f μ := by
  apply le_antisymm (iSup_le _) essSup_le_iSup
  intro i
  rw [essSup_eq_sInf]
  apply le_sInf
  intro b hb
  exact not_lt.mp fun a => h a hb

end CompleteLinearOrder

namespace ENNReal

variable {f : α -> Real>=0∞}

/--
lemma `essSup_piecewise` / 引理 `essSup_piecewise`

English:
lemma essSup_piecewise
  given: {s : Set α} [DecidablePred (· in s)] {g} (hs : MeasurableSet s)
  proof: by
  simp only [essSup, limsup_piecewise, blimsup_eq_limsup, ae_restrict_eq, hs, hs.compl]; rfl

中文:
引理 essSup_piecewise
  条件: {s : Set α} [DecidablePred (· in s)] {g} (hs : MeasurableSet s)
  证明: by
  simp only [essSup, limsup_piecewise, blimsup_eq_limsup, ae_restrict_eq, hs, hs.compl]; rfl

Depends on / 依赖: ae_restrict_eq, blimsup_eq_limsup, essSup, hs.compl, limsup_piecewise
-/
lemma essSup_piecewise {s : Set α} [DecidablePred (· in s)] {g} (hs : MeasurableSet s) :
    essSup (s.piecewise f g) μ = max (essSup f (μ.restrict s)) (essSup g (μ.restrict sᶜ)) := by
  simp only [essSup, limsup_piecewise, blimsup_eq_limsup, ae_restrict_eq, hs, hs.compl]; rfl

/--
theorem `essSup_indicator_eq_essSup_restrict` / 定理 `essSup_indicator_eq_essSup_restrict`

English:
theorem essSup_indicator_eq_essSup_restrict
  given: {s : Set α} {f : α -> Real>=0∞} (hs : MeasurableSet s)
  proof: by
  classical
  simp only [← piecewise_eq_indicator, essSup_piecewise hs, max_eq_left_iff]
  exact limsup_const_bot.trans_le zero_le

中文:
定理 essSup_indicator_eq_essSup_restrict
  条件: {s : Set α} {f : α -> 实数>=0∞} (hs : MeasurableSet s)
  证明: by
  classical
  simp only [← piecewise_eq_indicator, essSup_piecewise hs, max_eq_left_iff]
  exact limsup_const_bot.trans_le zero_le

Depends on / 依赖: classical, essSup_piecewise, limsup_const_bot, limsup_const_bot.trans_le, max_eq_left_iff, piecewise_eq_indicator, trans_le, zero_le
-/
theorem essSup_indicator_eq_essSup_restrict {s : Set α} {f : α -> Real>=0∞} (hs : MeasurableSet s) :
    essSup (s.indicator f) μ = essSup f (μ.restrict s) := by
  classical
  simp only [← piecewise_eq_indicator, essSup_piecewise hs, max_eq_left_iff]
  exact limsup_const_bot.trans_le zero_le

/--
theorem `ae_le_essSup` / 定理 `ae_le_essSup`

English:
theorem ae_le_essSup
  given: (f : α -> Real>=0∞)
  statement: forallᵐ y ∂μ, f y <= essSup f μ
  proof: eventually_le_limsup f

@[simp]

中文:
定理 ae_le_essSup
  条件: (f : α -> 实数>=0∞)
  结论: 对任意ᵐ y ∂μ, f y <= essSup f μ
  证明: eventually_le_limsup f

@[simp]

Depends on / 依赖: eventually_le_limsup
-/
theorem ae_le_essSup (f : α -> Real>=0∞) : forallᵐ y ∂μ, f y <= essSup f μ :=
  eventually_le_limsup f

@[simp]
/--
theorem `essSup_eq_zero_iff` / 定理 `essSup_eq_zero_iff`

English:
theorem essSup_eq_zero_iff
  statement: essSup f μ = 0 ↔ f =ᵐ[μ] 0
  proof: limsup_eq_zero_iff

中文:
定理 essSup_eq_zero_iff
  结论: essSup f μ = 0 ↔ f =ᵐ[μ] 0
  证明: limsup_eq_zero_iff

Depends on / 依赖: limsup_eq_zero_iff
-/
theorem essSup_eq_zero_iff : essSup f μ = 0 ↔ f =ᵐ[μ] 0 :=
  limsup_eq_zero_iff

/--
theorem `essSup_const_mul` / 定理 `essSup_const_mul`

English:
theorem essSup_const_mul
  given: {a : Real>=0∞}
  statement: essSup (fun x : α => a * f x) μ = a * essSup f μ
  proof: limsup_const_mul

中文:
定理 essSup_const_mul
  条件: {a : 实数>=0∞}
  结论: essSup (fun x : α => a * f x) μ = a * essSup f μ
  证明: limsup_const_mul

Depends on / 依赖: limsup_const_mul
-/
theorem essSup_const_mul {a : Real>=0∞} : essSup (fun x : α => a * f x) μ = a * essSup f μ :=
  limsup_const_mul

/--
theorem `essSup_mul_le` / 定理 `essSup_mul_le`

English:
theorem essSup_mul_le
  given: (f g : α -> Real>=0∞)
  statement: essSup (f * g) μ <= essSup f μ * essSup g μ
  proof: limsup_mul_le f g

中文:
定理 essSup_mul_le
  条件: (f g : α -> 实数>=0∞)
  结论: essSup (f * g) μ <= essSup f μ * essSup g μ
  证明: limsup_mul_le f g

Depends on / 依赖: limsup_mul_le
-/
theorem essSup_mul_le (f g : α -> Real>=0∞) : essSup (f * g) μ <= essSup f μ * essSup g μ :=
  limsup_mul_le f g

/--
theorem `essSup_add_le` / 定理 `essSup_add_le`

English:
theorem essSup_add_le
  given: (f g : α -> Real>=0∞)
  statement: essSup (f + g) μ <= essSup f μ + essSup g μ
  proof: limsup_add_le f g

中文:
定理 essSup_add_le
  条件: (f g : α -> 实数>=0∞)
  结论: essSup (f + g) μ <= essSup f μ + essSup g μ
  证明: limsup_add_le f g

Depends on / 依赖: limsup_add_le
-/
theorem essSup_add_le (f g : α -> Real>=0∞) : essSup (f + g) μ <= essSup f μ + essSup g μ :=
  limsup_add_le f g

/--
theorem `essSup_liminf_le` / 定理 `essSup_liminf_le`

English:
theorem essSup_liminf_le
  given: {ι} [Countable ι] [Preorder ι] (f : ι -> α -> Real>=0∞)
  proof: by
  simp_rw [essSup]
  exact ENNReal.limsup_liminf_le_liminf_limsup fun a b => f b a

中文:
定理 essSup_liminf_le
  条件: {ι} [Countable ι] [Preorder ι] (f : ι -> α -> 实数>=0∞)
  证明: by
  simp_rw [essSup]
  exact ENNReal.limsup_liminf_le_liminf_limsup fun a b => f b a

Depends on / 依赖: ENNReal, ENNReal.limsup_liminf_le_liminf_limsup, essSup, limsup_liminf_le_liminf_limsup, simp_rw
-/
theorem essSup_liminf_le {ι} [Countable ι] [Preorder ι] (f : ι -> α -> Real>=0∞) :
    essSup (fun x => atTop.liminf fun n => f n x) μ <=
      atTop.liminf fun n => essSup (fun x => f n x) μ := by
  simp_rw [essSup]
  exact ENNReal.limsup_liminf_le_liminf_limsup fun a b => f b a

/--
theorem `coe_essSup` / 定理 `coe_essSup`

English:
theorem coe_essSup
  given: {f : α -> Real>=0} (hf : IsBoundedUnder (· <= ·) (ae μ) f)
  proof: (ENNReal.coe_sInf <| hf).trans
    eq_of_forall_le_iff fun r => by
      simp [essSup, limsup, limsSup, eventually_map, ENNReal.forall_ennreal]; rfl

中文:
定理 coe_essSup
  条件: {f : α -> 实数>=0} (hf : IsBoundedUnder (· <= ·) (ae μ) f)
  证明: (ENNReal.coe_sInf <| hf).trans
    eq_of_forall_le_iff fun r => by
      simp [essSup, limsup, limsSup, eventually_map, ENNReal.forall_ennreal]; rfl

Depends on / 依赖: ENNReal, ENNReal.coe_sInf, ENNReal.forall_ennreal, coe_sInf, eq_of_forall_le_iff, essSup, eventually_map, forall_ennreal, limsSup, limsup
-/
theorem coe_essSup {f : α -> Real>=0} (hf : IsBoundedUnder (· <= ·) (ae μ) f) :
    ((essSup f μ : Real>=0) : Real>=0∞) = essSup (fun x => (f x : Real>=0∞)) μ :=
(ENNReal.coe_sInf <| hf).trans
    eq_of_forall_le_iff fun r => by
      simp [essSup, limsup, limsSup, eventually_map, ENNReal.forall_ennreal]; rfl

/--
lemma `ofReal_essSup` / 引理 `ofReal_essSup`

English:
lemma ofReal_essSup
  statement: {f : α -> Real} (h₁ : IsCoboundedUnder (· <= ·) (ae μ) f)
  proof: ENNReal.ofReal_limsup

中文:
引理 ofReal_essSup
  结论: {f : α -> 实数} (h₁ : IsCoboundedUnder (· <= ·) (ae μ) f)
  证明: ENNReal.ofReal_limsup

Depends on / 依赖: ENNReal, ENNReal.ofReal_limsup, ofReal_limsup
-/
lemma ofReal_essSup {f : α -> Real} (h₁ : IsCoboundedUnder (· <= ·) (ae μ) f)
    (h₂ : IsBoundedUnder (· <= ·) (ae μ) f) :
    ENNReal.ofReal (essSup f μ) = essSup (fun a => .ofReal (f a)) μ := ENNReal.ofReal_limsup

/--
lemma `toReal_essSup` / 引理 `toReal_essSup`

English:
lemma toReal_essSup
  statement: {f : α -> Real>=0∞} (h₁ : forallᵐ a ∂μ, f a != ⊤)
  proof: by
  obtain rfl | hμ := eq_zero_or_neZero μ
  · simp [essSup, limsup, limsSup]
  · exact ENNReal.toReal_limsup h₁

中文:
引理 toReal_essSup
  结论: {f : α -> 实数>=0∞} (h₁ : 对任意ᵐ a ∂μ, f a != ⊤)
  证明: by
  obtain rfl | hμ := eq_zero_or_neZero μ
  · simp [essSup, limsup, limsSup]
  · exact ENNReal.toReal_limsup h₁

Depends on / 依赖: ENNReal, ENNReal.toReal_limsup, eq_zero_or_neZero, essSup, limsSup, limsup, toReal_limsup
-/
lemma toReal_essSup {f : α -> Real>=0∞} (h₁ : forallᵐ a ∂μ, f a != ⊤)
    (h₂ : IsBoundedUnder (· <= ·) (ae μ) fun i => (f i).toReal) :
    (essSup f μ).toReal = essSup (fun a => (f a).toReal) μ := by
  obtain rfl | hμ := eq_zero_or_neZero μ
  · simp [essSup, limsup, limsSup]
  · exact ENNReal.toReal_limsup h₁

/--
lemma `essSup_restrict_eq_of_support_subset` / 引理 `essSup_restrict_eq_of_support_subset`

English:
lemma essSup_restrict_eq_of_support_subset
  given: {s : Set α} {f : α -> Real>=0∞} (hsf : f.support subseteq s)
  proof: by
  apply le_antisymm (essSup_mono_measure' Measure.restrict_le_self)
  apply le_of_forall_lt (fun c hc => ?_)
  obtain ⟨d, cd, hd⟩ : exists d, c < d ∧ d < essSup f μ := exists_between hc
  let t := {x | d < f x}
  have A : 0 < (μ.restrict t) t := by
    simp only [Measure.restrict_apply_self]
    

中文:
引理 essSup_restrict_eq_of_support_subset
  条件: {s : Set α} {f : α -> 实数>=0∞} (hsf : f.support subseteq s)
  证明: by
  apply le_antisymm (essSup_mono_measure' Measure.restrict_le_self)
  apply le_of_forall_lt (fun c hc => ?_)
  obtain ⟨d, cd, hd⟩ : exists d, c < d ∧ d < essSup f μ := exists_between hc
  let t := {x | d < f x}
  have A : 0 < (μ.restrict t) t := by
    simp only [Measure.restrict_apply_self]
    

Depends on / 依赖: Measure, Measure.restrict_apply_self, Measure.restrict_le_self, OrderBot, OrderBot.bddBelow, bddBelow, bot_lt_iff_ne_bot, essSup, essSup_eq_sInf, essSup_mono_measure, exists_between, le_antisymm, le_of_forall_lt, notMem_of_lt_csInf, restrict, restrict_apply_self, restrict_le_self
-/
lemma essSup_restrict_eq_of_support_subset {s : Set α} {f : α -> Real>=0∞} (hsf : f.support subseteq s) :
    essSup f (μ.restrict s) = essSup f μ := by
  apply le_antisymm (essSup_mono_measure' Measure.restrict_le_self)
  apply le_of_forall_lt (fun c hc => ?_)
  obtain ⟨d, cd, hd⟩ : exists d, c < d ∧ d < essSup f μ := exists_between hc
  let t := {x | d < f x}
  have A : 0 < (μ.restrict t) t := by
    simp only [Measure.restrict_apply_self]
    rw [essSup_eq_sInf] at hd
    have : d ∉ {a | μ {x | a < f x} = 0} := notMem_of_lt_csInf hd (OrderBot.bddBelow _)
    exact bot_lt_iff_ne_bot.2 this
  have B : 0 < (μ.restrict s) t := by
    have : μ.restrict t <= μ.restrict s := by
      apply Measure.restrict_mono _ le_rfl
      apply subset_trans _ hsf
      intro x (hx : d < f x)
      exact (lt_of_le_of_lt bot_le hx).ne'
    exact lt_of_lt_of_le A (this _)
  apply cd.trans_le
  rw [essSup_eq_sInf]
  apply le_sInf (fun b hb => ?_)
  contrapose! hb
  exact ne_of_gt (B.trans_le (measure_mono (fun x hx => hb.trans hx)))

end ENNReal
