/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. This property, called `AEMeasurable f μ`, is defined in the file `MeasureSpaceDef`.
We discuss several of its properties that are analogous to properties of measurable functions.
-/

public section

open MeasureTheory MeasureTheory.Measure Filter Set Function ENNReal

variable {ι α β γ δ R : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] {f g : α -> β} {μ ν : Measure α}

section

@[nontriviality]
/--
theorem `Subsingleton.aemeasurable` / 定理 `Subsingleton.aemeasurable`

English:
theorem Subsingleton.aemeasurable
  given: [Subsingleton α]
  statement: AEMeasurable f μ
  proof: Subsingleton.measurable.aemeasurable

@[nontriviality, fun_prop]

中文:
定理 子单例.aemeasurable
  条件: [子单例 α]
  结论: 几乎处处可测 f μ
  证明: Subsingleton.measurable.aemeasurable

@[nontriviality, fun_prop]

Depends on / 依赖: Subsingleton, Subsingleton.measurable.aemeasurable, aemeasurable, measurable
-/
theorem Subsingleton.aemeasurable [Subsingleton α] : AEMeasurable f μ :=
  Subsingleton.measurable.aemeasurable

@[nontriviality, fun_prop]
/--
theorem `aemeasurable_of_subsingleton_codomain` / 定理 `aemeasurable_of_subsingleton_codomain`

English:
theorem aemeasurable_of_subsingleton_codomain
  given: [Subsingleton β]
  statement: AEMeasurable f μ
  proof: (measurable_of_subsingleton_codomain f).aemeasurable

@[simp, fun_prop]

中文:
定理 aemeasurable_of_subsingleton_codomain
  条件: [子单例 β]
  结论: 几乎处处可测 f μ
  证明: (measurable_of_subsingleton_codomain f).aemeasurable

@[simp, fun_prop]

Depends on / 依赖: aemeasurable, measurable_of_subsingleton_codomain
-/
theorem aemeasurable_of_subsingleton_codomain [Subsingleton β] : AEMeasurable f μ :=
  (measurable_of_subsingleton_codomain f).aemeasurable

@[simp, fun_prop]
/--
theorem `aemeasurable_zero_measure` / 定理 `aemeasurable_zero_measure`

English:
theorem aemeasurable_zero_measure
  statement: AEMeasurable f (0 : Measure α)
  proof: by
  nontriviality α; inhabit α
  exact ⟨fun _ => f default, measurable_const, rfl⟩

中文:
定理 aemeasurable_zero_measure
  结论: 几乎处处可测 f (0 : 测度 α)
  证明: by
  nontriviality α; inhabit α
  exact ⟨fun _ => f default, measurable_const, rfl⟩

Depends on / 依赖: inhabit, measurable_const, nontriviality
-/
theorem aemeasurable_zero_measure : AEMeasurable f (0 : Measure α) := by
  nontriviality α; inhabit α
  exact ⟨fun _ => f default, measurable_const, rfl⟩

/--
theorem `aemeasurable_id''` / 定理 `aemeasurable_id''`

English:
theorem aemeasurable_id''
  given: (μ : Measure α) {m : MeasurableSpace α} (hm : m <= m0)
  proof: @Measurable.aemeasurable α α m0 m id μ (measurable_id'' hm)

中文:
定理 aemeasurable_id''
  条件: (μ : 测度 α) {m : 可测空间 α} (hm : m <= m0)
  证明: @Measurable.aemeasurable α α m0 m id μ (measurable_id'' hm)

Depends on / 依赖: Measurable, Measurable.aemeasurable, aemeasurable, measurable_id
-/
theorem aemeasurable_id'' (μ : Measure α) {m : MeasurableSpace α} (hm : m <= m0) :
    @AEMeasurable α α m m0 id μ :=
  @Measurable.aemeasurable α α m0 m id μ (measurable_id'' hm)

/--
lemma `aemeasurable_of_map_neZero` / 引理 `aemeasurable_of_map_neZero`

English:
lemma aemeasurable_of_map_neZero
  statement: {μ : Measure α}
  proof: by
  by_contra h'
  simp [h'] at h

中文:
引理 aemeasurable_of_map_neZero
  结论: {μ : 测度 α}
  证明: by
  by_contra h'
  simp [h'] at h
-/
lemma aemeasurable_of_map_neZero {μ : Measure α}
    {f : α -> β} (h : NeZero (μ.map f)) :
    AEMeasurable f μ := by
  by_contra h'
  simp [h'] at h

namespace AEMeasurable

/--
lemma `mono_ac` / 引理 `mono_ac`

English:
lemma mono_ac
  given: (hf : AEMeasurable f ν) (hμν : μ ≪ ν)
  statement: AEMeasurable f μ
  proof: ⟨hf.mk f, hf.measurable_mk, hμν.ae_le hf.ae_eq_mk⟩

中文:
引理 mono_ac
  条件: (hf : 几乎处处可测 f ν) (hμν : μ ≪ ν)
  结论: 几乎处处可测 f μ
  证明: ⟨hf.mk f, hf.measurable_mk, hμν.ae_le hf.ae_eq_mk⟩

Depends on / 依赖: ae_eq_mk, ae_le, hf.ae_eq_mk, hf.measurable_mk, hf.mk, measurable_mk
-/
lemma mono_ac (hf : AEMeasurable f ν) (hμν : μ ≪ ν) : AEMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk, hμν.ae_le hf.ae_eq_mk⟩

/--
theorem `mono_measure` / 定理 `mono_measure`

English:
theorem mono_measure
  given: (h : AEMeasurable f μ) (h' : ν <= μ)
  statement: AEMeasurable f ν
  proof: mono_ac h h'.absolutelyContinuous

中文:
定理 mono_measure
  条件: (h : 几乎处处可测 f μ) (h' : ν <= μ)
  结论: 几乎处处可测 f ν
  证明: mono_ac h h'.absolutelyContinuous

Depends on / 依赖: absolutelyContinuous, mono_ac
-/
theorem mono_measure (h : AEMeasurable f μ) (h' : ν <= μ) : AEMeasurable f ν :=
  mono_ac h h'.absolutelyContinuous

/--
theorem `mono_set` / 定理 `mono_set`

English:
theorem mono_set
  given: {s t} (h : s subseteq t) (ht : AEMeasurable f (μ.restrict t))
  proof: ht.mono_measure (restrict_mono h le_rfl)

@[fun_prop]

中文:
定理 mono_set
  条件: {s t} (h : s subseteq t) (ht : 几乎处处可测 f (μ.restrict t))
  证明: ht.mono_measure (restrict_mono h le_rfl)

@[fun_prop]

Depends on / 依赖: ht.mono_measure, le_rfl, mono_measure, restrict_mono
-/
theorem mono_set {s t} (h : s subseteq t) (ht : AEMeasurable f (μ.restrict t)) :
    AEMeasurable f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)

@[fun_prop]
/--
theorem `mono'` / 定理 `mono'`

English:
theorem mono'
  given: (h : AEMeasurable f μ) (h' : ν ≪ μ)
  statement: AEMeasurable f ν
  proof: ⟨h.mk f, h.measurable_mk, h' h.ae_eq_mk⟩

中文:
定理 mono'
  条件: (h : 几乎处处可测 f μ) (h' : ν ≪ μ)
  结论: 几乎处处可测 f ν
  证明: ⟨h.mk f, h.measurable_mk, h' h.ae_eq_mk⟩
-/
protected theorem mono' (h : AEMeasurable f μ) (h' : ν ≪ μ) : AEMeasurable f ν :=
  ⟨h.mk f, h.measurable_mk, h' h.ae_eq_mk⟩

/--
theorem `ae_mem_imp_eq_mk` / 定理 `ae_mem_imp_eq_mk`

English:
theorem ae_mem_imp_eq_mk
  given: {s} (h : AEMeasurable f (μ.restrict s))
  proof: ae_imp_of_ae_restrict h.ae_eq_mk

中文:
定理 ae_mem_imp_eq_mk
  条件: {s} (h : 几乎处处可测 f (μ.restrict s))
  证明: ae_imp_of_ae_restrict h.ae_eq_mk

Depends on / 依赖: ae_eq_mk, ae_imp_of_ae_restrict, h.ae_eq_mk
-/
theorem ae_mem_imp_eq_mk {s} (h : AEMeasurable f (μ.restrict s)) :
    forallᵐ x ∂μ, x in s -> f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk

/--
theorem `ae_inf_principal_eq_mk` / 定理 `ae_inf_principal_eq_mk`

English:
theorem ae_inf_principal_eq_mk
  given: {s} (h : AEMeasurable f (μ.restrict s))
  statement: f =ᶠ[ae μ ⊓ 𝓟 s] h.mk f
  proof: le_ae_restrict h.ae_eq_mk

@[fun_prop]

中文:
定理 ae_inf_principal_eq_mk
  条件: {s} (h : 几乎处处可测 f (μ.restrict s))
  结论: f =ᶠ[ae μ ⊓ 𝓟 s] h.mk f
  证明: le_ae_restrict h.ae_eq_mk

@[fun_prop]

Depends on / 依赖: ae_eq_mk, h.ae_eq_mk, le_ae_restrict
-/
theorem ae_inf_principal_eq_mk {s} (h : AEMeasurable f (μ.restrict s)) : f =ᶠ[ae μ ⊓ 𝓟 s] h.mk f :=
  le_ae_restrict h.ae_eq_mk

@[fun_prop]
/--
theorem `sum_measure` / 定理 `sum_measure`

English:
theorem sum_measure
  given: [Countable ι] {μ : ι -> Measure α} (h : forall i, AEMeasurable f (μ i))
  proof: by
  classical
  nontriviality β
  inhabit β
  set s : ι -> Set α := fun i => toMeasurable (μ i) { x | f x != (h i).mk f x }
  have hsμ : forall i, μ i (s i) = 0 := by
    intro i
    rw [measure_toMeasurable]
    exact (h i).ae_eq_mk
  have hsm : MeasurableSet (⋂ i, s i) :=
    MeasurableSet.iInter

中文:
定理 sum_measure
  条件: [可数 ι] {μ : ι -> 测度 α} (h : 对任意 i, 几乎处处可测 f (μ i))
  证明: by
  classical
  nontriviality β
  inhabit β
  set s : ι -> Set α := fun i => toMeasurable (μ i) { x | f x != (h i).mk f x }
  have hsμ : forall i, μ i (s i) = 0 := by
    intro i
    rw [measure_toMeasurable]
    exact (h i).ae_eq_mk
  have hsm : MeasurableSet (⋂ i, s i) :=
    MeasurableSet.iInter

Depends on / 依赖: MeasurableSet, MeasurableSet.iInter, ae_eq_mk, classical, contrapose, iInter, inhabit, measurableSet_toMeasurable, measure_toMeasurable, nontriviality, piecewise, subset_toMeasurable, toMeasurable
-/
theorem sum_measure [Countable ι] {μ : ι -> Measure α} (h : forall i, AEMeasurable f (μ i)) :
    AEMeasurable f (sum μ) := by
  classical
  nontriviality β
  inhabit β
  set s : ι -> Set α := fun i => toMeasurable (μ i) { x | f x != (h i).mk f x }
  have hsμ : forall i, μ i (s i) = 0 := by
    intro i
    rw [measure_toMeasurable]
    exact (h i).ae_eq_mk
  have hsm : MeasurableSet (⋂ i, s i) :=
    MeasurableSet.iInter fun i => measurableSet_toMeasurable _ _
  have hs : forall i x, x ∉ s i -> f x = (h i).mk f x := by
    intro i x hx
    contrapose! hx
    exact subset_toMeasurable _ _ hx
  set g : α -> β := (⋂ i, s i).piecewise (const α default) f
  refine ⟨g, measurable_of_restrict_of_restrict_compl hsm ?_ ?_, ae_sum_iff.mpr fun i => ?_⟩
  · rw [domRestrict_piecewise]
    simp only [s]
    exact measurable_const
  · rw [domRestrict_piecewise_compl, compl_iInter]
    intro t ht
    refine ⟨⋃ i, (h i).mk f ⁻¹' t inter (s i)ᶜ, MeasurableSet.iUnion fun i =>
      (measurable_mk _ ht).inter (measurableSet_toMeasurable _ _).compl, ?_⟩
    ext ⟨x, hx⟩
    simp only [mem_preimage, mem_iUnion, Set.domRestrict, mem_inter_iff,
      mem_compl_iff] at hx ⊢
    constructor
    · rintro ⟨i, hxt, hxs⟩
      rwa [hs _ _ hxs]
    · rcases hx with ⟨i, hi⟩
      rw [hs _ _ hi]
      exact fun h => ⟨i, h, hi⟩
  · refine measure_mono_null (fun x (hx : f x != g x) => ?_) (hsμ i)
    contrapose hx
    refine (piecewise_eq_of_notMem _ _ _ ?_).symm
    exact fun h => hx (mem_iInter.1 h i)

@[simp]
/--
theorem `_root_.aemeasurable_sum_measure_iff` / 定理 `_root_.aemeasurable_sum_measure_iff`

English:
theorem _root_.aemeasurable_sum_measure_iff
  given: [Countable ι] {μ : ι -> Measure α}
  proof: ⟨fun h _ => h.mono_measure (le_sum _ _), sum_measure⟩

@[simp]

中文:
定理 _root_.aemeasurable_sum_measure_iff
  条件: [可数 ι] {μ : ι -> 测度 α}
  证明: ⟨fun h _ => h.mono_measure (le_sum _ _), sum_measure⟩

@[simp]

Depends on / 依赖: h.mono_measure, le_sum, mono_measure, sum_measure
-/
theorem _root_.aemeasurable_sum_measure_iff [Countable ι] {μ : ι -> Measure α} :
    AEMeasurable f (sum μ) ↔ forall i, AEMeasurable f (μ i) :=
  ⟨fun h _ => h.mono_measure (le_sum _ _), sum_measure⟩

@[simp]
/--
theorem `_root_.aemeasurable_add_measure_iff` / 定理 `_root_.aemeasurable_add_measure_iff`

English:
theorem _root_.aemeasurable_add_measure_iff
  proof: by
  rw [← sum_cond]; rw [aemeasurable_sum_measure_iff]; rw [Bool.forall_bool]; rw [and_comm]
  rfl

@[fun_prop]

中文:
定理 _root_.aemeasurable_add_measure_iff
  证明: by
  rw [← sum_cond]; rw [aemeasurable_sum_measure_iff]; rw [Bool.forall_bool]; rw [and_comm]
  rfl

@[fun_prop]

Depends on / 依赖: Bool.forall_bool, aemeasurable_sum_measure_iff, and_comm, forall_bool, sum_cond
-/
theorem _root_.aemeasurable_add_measure_iff :
    AEMeasurable f (μ + ν) ↔ AEMeasurable f μ ∧ AEMeasurable f ν := by
  rw [← sum_cond]; rw [aemeasurable_sum_measure_iff]; rw [Bool.forall_bool]; rw [and_comm]
  rfl

@[fun_prop]
/--
theorem `add_measure` / 定理 `add_measure`

English:
theorem add_measure
  given: {f : α -> β} (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν)
  proof: aemeasurable_add_measure_iff.2 ⟨hμ, hν⟩

中文:
定理 add_measure
  条件: {f : α -> β} (hμ : 几乎处处可测 f μ) (hν : 几乎处处可测 f ν)
  证明: aemeasurable_add_measure_iff.2 ⟨hμ, hν⟩

Depends on / 依赖: aemeasurable_add_measure_iff
-/
theorem add_measure {f : α -> β} (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    AEMeasurable f (μ + ν) :=
  aemeasurable_add_measure_iff.2 ⟨hμ, hν⟩

/--
theorem `map_add₀` / 定理 `map_add₀`

English:
theorem map_add₀
  statement: {μ ν : Measure α} {f : α -> β}
  proof: by
  ext
  simp [*]

@[fun_prop]

中文:
定理 map_add₀
  结论: {μ ν : 测度 α} {f : α -> β}
  证明: by
  ext
  simp [*]

@[fun_prop]
-/
protected theorem map_add₀ {μ ν : Measure α} {f : α -> β}
    (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    (μ + ν).map f = μ.map f + ν.map f := by
  ext
  simp [*]

@[fun_prop]
/--
theorem `iUnion` / 定理 `iUnion`

English:
theorem iUnion
  statement: [Countable ι] {s : ι -> Set α}
  proof: (sum_measure h).mono_measure restrict_iUnion_le

@[simp]

中文:
定理 iUnion
  结论: [可数 ι] {s : ι -> 集合 α}
  证明: (sum_measure h).mono_measure restrict_iUnion_le

@[simp]
-/
protected theorem iUnion [Countable ι] {s : ι -> Set α}
    (h : forall i, AEMeasurable f (μ.restrict (s i))) : AEMeasurable f (μ.restrict (⋃ i, s i)) :=
(sum_measure h).mono_measure restrict_iUnion_le

@[simp]
/--
theorem `_root_.aemeasurable_iUnion_iff` / 定理 `_root_.aemeasurable_iUnion_iff`

English:
theorem _root_.aemeasurable_iUnion_iff
  given: [Countable ι] {s : ι -> Set α}
  proof: ⟨fun h _ => h.mono_measure restrict_mono (subset_iUnion _ _) le_rfl, AEMeasurable.iUnion⟩

@[simp]

中文:
定理 _root_.aemeasurable_iUnion_iff
  条件: [可数 ι] {s : ι -> 集合 α}
  证明: ⟨fun h _ => h.mono_measure restrict_mono (subset_iUnion _ _) le_rfl, AEMeasurable.iUnion⟩

@[simp]

Depends on / 依赖: AEMeasurable, AEMeasurable.iUnion, h.mono_measure, iUnion, le_rfl, mono_measure, restrict_mono, subset_iUnion
-/
theorem _root_.aemeasurable_iUnion_iff [Countable ι] {s : ι -> Set α} :
    AEMeasurable f (μ.restrict (⋃ i, s i)) ↔ forall i, AEMeasurable f (μ.restrict (s i)) :=
⟨fun h _ => h.mono_measure restrict_mono (subset_iUnion _ _) le_rfl, AEMeasurable.iUnion⟩

@[simp]
/--
theorem `_root_.aemeasurable_union_iff` / 定理 `_root_.aemeasurable_union_iff`

English:
theorem _root_.aemeasurable_union_iff
  given: {s t : Set α}
  proof: by
  simp only [union_eq_iUnion, aemeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]

@[fun_prop]

中文:
定理 _root_.aemeasurable_union_iff
  条件: {s t : 集合 α}
  证明: by
  simp only [union_eq_iUnion, aemeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]

@[fun_prop]

Depends on / 依赖: Bool.forall_bool, aemeasurable_iUnion_iff, and_comm, forall_bool, union_eq_iUnion
-/
theorem _root_.aemeasurable_union_iff {s t : Set α} :
    AEMeasurable f (μ.restrict (s union t)) ↔
      AEMeasurable f (μ.restrict s) ∧ AEMeasurable f (μ.restrict t) := by
  simp only [union_eq_iUnion, aemeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]

@[fun_prop]
/--
theorem `smul_measure` / 定理 `smul_measure`

English:
theorem smul_measure
  statement: [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: ⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩

中文:
定理 smul_measure
  结论: [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  证明: ⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩

Depends on / 依赖: ae_eq_mk, ae_smul_measure, h.ae_eq_mk, h.measurable_mk, h.mk, measurable_mk
-/
theorem smul_measure [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (h : AEMeasurable f μ) (c : R) : AEMeasurable f (c • μ) :=
  ⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩

/--
theorem `comp_aemeasurable` / 定理 `comp_aemeasurable`

English:
theorem comp_aemeasurable
  statement: {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g (μ.map f))
  proof: ⟨hg.mk g ∘ hf.mk f, hg.measurable_mk.comp hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (mk g hg))⟩

@[fun_prop]

中文:
定理 comp_aemeasurable
  结论: {f : α -> δ} {g : δ -> β} (hg : 几乎处处可测 g (μ.map f))
  证明: ⟨hg.mk g ∘ hf.mk f, hg.measurable_mk.comp hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (mk g hg))⟩

@[fun_prop]

Depends on / 依赖: ae_eq_comp, ae_eq_mk, fun_comp, hf.ae_eq_mk.fun_comp, hf.measurable_mk, hf.mk, hg.ae_eq_mk, hg.measurable_mk.comp, hg.mk, measurable_mk
-/
theorem comp_aemeasurable {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g (μ.map f))
    (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.measurable_mk.comp hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (mk g hg))⟩

@[fun_prop]
/--
theorem `comp_aemeasurable'` / 定理 `comp_aemeasurable'`

English:
theorem comp_aemeasurable'
  statement: {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g (μ.map f))
  proof: comp_aemeasurable hg hf

中文:
定理 comp_aemeasurable'
  结论: {f : α -> δ} {g : δ -> β} (hg : 几乎处处可测 g (μ.map f))
  证明: comp_aemeasurable hg hf

Depends on / 依赖: comp_aemeasurable
-/
theorem comp_aemeasurable' {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g (μ.map f))
    (hf : AEMeasurable f μ) : AEMeasurable (fun x => g (f x)) μ := comp_aemeasurable hg hf

/--
theorem `comp_measurable` / 定理 `comp_measurable`

English:
theorem comp_measurable
  statement: {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g (μ.map f))
  proof: hg.comp_aemeasurable hf.aemeasurable

@[fun_prop]

中文:
定理 comp_measurable
  结论: {f : α -> δ} {g : δ -> β} (hg : 几乎处处可测 g (μ.map f))
  证明: hg.comp_aemeasurable hf.aemeasurable

@[fun_prop]

Depends on / 依赖: aemeasurable, comp_aemeasurable, hf.aemeasurable, hg.comp_aemeasurable
-/
theorem comp_measurable {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g (μ.map f))
    (hf : Measurable f) : AEMeasurable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable

@[fun_prop]
/--
theorem `comp_quasiMeasurePreserving` / 定理 `comp_quasiMeasurePreserving`

English:
theorem comp_quasiMeasurePreserving
  statement: {ν : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν)
  proof: (hg.mono' hf.absolutelyContinuous).comp_measurable hf.measurable

中文:
定理 comp_quasiMeasurePreserving
  结论: {ν : 测度 δ} {f : α -> δ} {g : δ -> β} (hg : 几乎处处可测 g ν)
  证明: (hg.mono' hf.absolutelyContinuous).comp_measurable hf.measurable

Depends on / 依赖: absolutelyContinuous, comp_measurable, hf.absolutelyContinuous, hf.measurable, hg.mono, measurable
-/
theorem comp_quasiMeasurePreserving {ν : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AEMeasurable (g ∘ f) μ :=
  (hg.mono' hf.absolutelyContinuous).comp_measurable hf.measurable

/--
theorem `map_map_of_aemeasurable` / 定理 `map_map_of_aemeasurable`

English:
theorem map_map_of_aemeasurable
  statement: {g : β -> γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ))
  proof: by
  ext1 s hs
  rw [map_apply_of_aemeasurable hg hs]; rw [map_apply₀ hf (hg.nullMeasurable hs)]; rw [map_apply_of_aemeasurable (hg.comp_aemeasurable hf) hs]; rw [preimage_comp]

@[fun_prop]

中文:
定理 map_map_of_aemeasurable
  结论: {g : β -> γ} {f : α -> β} (hg : 几乎处处可测 g (测度.map f μ))
  证明: by
  ext1 s hs
  rw [map_apply_of_aemeasurable hg hs]; rw [map_apply₀ hf (hg.nullMeasurable hs)]; rw [map_apply_of_aemeasurable (hg.comp_aemeasurable hf) hs]; rw [preimage_comp]

@[fun_prop]

Depends on / 依赖: comp_aemeasurable, hg.comp_aemeasurable, hg.nullMeasurable, map_apply_of_aemeasurable, nullMeasurable, preimage_comp
-/
theorem map_map_of_aemeasurable {g : β -> γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : (μ.map f).map g = μ.map (g ∘ f) := by
  ext1 s hs
  rw [map_apply_of_aemeasurable hg hs]; rw [map_apply₀ hf (hg.nullMeasurable hs)]; rw [map_apply_of_aemeasurable (hg.comp_aemeasurable hf) hs]; rw [preimage_comp]

@[fun_prop]
/--
theorem `fst` / 定理 `fst`

English:
theorem fst
  given: {f : α -> β × γ} (hf : AEMeasurable f μ)
  proof: measurable_fst.comp_aemeasurable hf

@[fun_prop]

中文:
定理 fst
  条件: {f : α -> β × γ} (hf : 几乎处处可测 f μ)
  证明: measurable_fst.comp_aemeasurable hf

@[fun_prop]
-/
protected theorem fst {f : α -> β × γ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x).1) μ :=
  measurable_fst.comp_aemeasurable hf

@[fun_prop]
/--
theorem `snd` / 定理 `snd`

English:
theorem snd
  given: {f : α -> β × γ} (hf : AEMeasurable f μ)
  proof: measurable_snd.comp_aemeasurable hf

@[fun_prop]

中文:
定理 snd
  条件: {f : α -> β × γ} (hf : 几乎处处可测 f μ)
  证明: measurable_snd.comp_aemeasurable hf

@[fun_prop]
-/
protected theorem snd {f : α -> β × γ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x).2) μ :=
  measurable_snd.comp_aemeasurable hf

@[fun_prop]
/--
theorem `prodMk` / 定理 `prodMk`

English:
theorem prodMk
  given: {f : α -> β} {g : α -> γ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
  proof: ⟨fun a => (hf.mk f a, hg.mk g a), hf.measurable_mk.prodMk hg.measurable_mk,
    hf.ae_eq_mk.prodMk hg.ae_eq_mk⟩

中文:
定理 prodMk
  条件: {f : α -> β} {g : α -> γ} (hf : 几乎处处可测 f μ) (hg : 几乎处处可测 g μ)
  证明: ⟨fun a => (hf.mk f a, hg.mk g a), hf.measurable_mk.prodMk hg.measurable_mk,
    hf.ae_eq_mk.prodMk hg.ae_eq_mk⟩

Depends on / 依赖: ae_eq_mk, hf.ae_eq_mk.prodMk, hf.measurable_mk.prodMk, hf.mk, hg.ae_eq_mk, hg.measurable_mk, hg.mk, measurable_mk, prodMk
-/
theorem prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => (f x, g x)) μ :=
  ⟨fun a => (hf.mk f a, hg.mk g a), hf.measurable_mk.prodMk hg.measurable_mk,
    hf.ae_eq_mk.prodMk hg.ae_eq_mk⟩

/--
theorem `_root_.nullMeasurableSet_eq_fun` / 定理 `_root_.nullMeasurableSet_eq_fun`

English:
theorem _root_.nullMeasurableSet_eq_fun
  statement: [MeasurableEq β]
  proof: (hf.prodMk hg).nullMeasurableSet_preimage measurableSet_diagonal

中文:
定理 _root_.nullMeasurableSet_eq_fun
  结论: [MeasurableEq β]
  证明: (hf.prodMk hg).nullMeasurableSet_preimage measurableSet_diagonal

Depends on / 依赖: hf.prodMk, measurableSet_diagonal, nullMeasurableSet_preimage, prodMk
-/
theorem _root_.nullMeasurableSet_eq_fun [MeasurableEq β]
    {f g : α -> β} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ :=
  (hf.prodMk hg).nullMeasurableSet_preimage measurableSet_diagonal

/--
theorem `exists_ae_eq_range_subset` / 定理 `exists_ae_eq_range_subset`

English:
theorem exists_ae_eq_range_subset
  statement: (H : AEMeasurable f μ) {t : Set β} (ht : forallᵐ x ∂μ, f x in t)
  proof: by
  classical
  let s : Set α := toMeasurable μ { x | f x = H.mk f x ∧ f x in t }ᶜ
  let g : α -> β := piecewise s (fun _ => h₀.some) (H.mk f)
  refine ⟨g, ?_, ?_, ?_⟩
  · exact Measurable.piecewise (measurableSet_toMeasurable _ _) measurable_const H.measurable_mk
  · rintro _ ⟨x, rfl⟩
    by_cases

中文:
定理 存在_ae_eq_range_subset
  结论: (H : 几乎处处可测 f μ) {t : 集合 β} (ht : 对任意ᵐ x ∂μ, f x in t)
  证明: by
  classical
  let s : Set α := toMeasurable μ { x | f x = H.mk f x ∧ f x in t }ᶜ
  let g : α -> β := piecewise s (fun _ => h₀.some) (H.mk f)
  refine ⟨g, ?_, ?_, ?_⟩
  · exact Measurable.piecewise (measurableSet_toMeasurable _ _) measurable_const H.measurable_mk
  · rintro _ ⟨x, rfl⟩
    by_cases

Depends on / 依赖: H.measurable_mk, H.mk, Measurable, Measurable.piecewise, classical, contextual, contrapose, measurableSet_toMeasurable, measurable_const, measurable_mk, mem_compl_iff, mem_ofPred_eq, not_, not_and, not_false_iff, piecewise, piecewise_eq_of_notMem, some_mem, subset_toMeasurable, toMeasurable
-/
theorem exists_ae_eq_range_subset (H : AEMeasurable f μ) {t : Set β} (ht : forallᵐ x ∂μ, f x in t)
    (h₀ : t.Nonempty) : exists g, Measurable g ∧ range g subseteq t ∧ f =ᵐ[μ] g := by
  classical
  let s : Set α := toMeasurable μ { x | f x = H.mk f x ∧ f x in t }ᶜ
  let g : α -> β := piecewise s (fun _ => h₀.some) (H.mk f)
  refine ⟨g, ?_, ?_, ?_⟩
  · exact Measurable.piecewise (measurableSet_toMeasurable _ _) measurable_const H.measurable_mk
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x in s
    · simpa [g, hx] using h₀.some_mem
    · simp only [g, hx, piecewise_eq_of_notMem, not_false_iff]
      contrapose hx
      apply subset_toMeasurable
      simp +contextual only [hx, mem_compl_iff, mem_ofPred_eq, not_and,
        not_false_iff, imp_true_iff]
  · have A : μ (toMeasurable μ { x | f x = H.mk f x ∧ f x in t }ᶜ) = 0 := by
      rw [measure_toMeasurable]; rw [← compl_mem_ae_iff]; rw [compl_compl]
      exact H.ae_eq_mk.and ht
    filter_upwards [compl_mem_ae_iff.2 A] with x hx
    rw [mem_compl_iff] at hx
    simp only [s, g, hx, piecewise_eq_of_notMem, not_false_iff]
    contrapose! hx
    apply subset_toMeasurable
    simp only [hx, mem_compl_iff, mem_ofPred_eq, false_and, not_false_iff]

/--
theorem `exists_measurable_nonneg` / 定理 `exists_measurable_nonneg`

English:
theorem exists_measurable_nonneg
  statement: {β} [Preorder β] [Zero β] {mβ : MeasurableSpace β} {f : α -> β}
  proof: by
  obtain ⟨G, hG_meas, hG_mem, hG_ae_eq⟩ := hf.exists_ae_eq_range_subset f_nn ⟨0, le_rfl⟩
  exact ⟨G, hG_meas, fun x => hG_mem (mem_range_self x), hG_ae_eq⟩

中文:
定理 存在_measurable_nonneg
  结论: {β} [预序 β] [零 β] {mβ : 可测空间 β} {f : α -> β}
  证明: by
  obtain ⟨G, hG_meas, hG_mem, hG_ae_eq⟩ := hf.exists_ae_eq_range_subset f_nn ⟨0, le_rfl⟩
  exact ⟨G, hG_meas, fun x => hG_mem (mem_range_self x), hG_ae_eq⟩

Depends on / 依赖: exists_ae_eq_range_subset, f_nn, hG_ae_eq, hG_meas, hG_mem, hf.exists_ae_eq_range_subset, le_rfl, mem_range_self
-/
theorem exists_measurable_nonneg {β} [Preorder β] [Zero β] {mβ : MeasurableSpace β} {f : α -> β}
    (hf : AEMeasurable f μ) (f_nn : forallᵐ t ∂μ, 0 <= f t) : exists g, Measurable g ∧ 0 <= g ∧ f =ᵐ[μ] g := by
  obtain ⟨G, hG_meas, hG_mem, hG_ae_eq⟩ := hf.exists_ae_eq_range_subset f_nn ⟨0, le_rfl⟩
  exact ⟨G, hG_meas, fun x => hG_mem (mem_range_self x), hG_ae_eq⟩

/--
theorem `subtype_mk` / 定理 `subtype_mk`

English:
theorem subtype_mk
  given: (h : AEMeasurable f μ) {s : Set β} {hfs : forall x, f x in s}
  proof: by
  nontriviality α; inhabit α
  obtain ⟨g, g_meas, hg, fg⟩ : exists g : α -> β, Measurable g ∧ range g subseteq s ∧ f =ᵐ[μ] g :=
    h.exists_ae_eq_range_subset (Eventually.of_forall hfs) ⟨_, hfs default⟩
  refine ⟨codRestrict g s fun x => hg (mem_range_self _), Measurable.subtype_mk g_meas, ?_⟩
 

中文:
定理 subtype_mk
  条件: (h : 几乎处处可测 f μ) {s : 集合 β} {hfs : 对任意 x, f x in s}
  证明: by
  nontriviality α; inhabit α
  obtain ⟨g, g_meas, hg, fg⟩ : exists g : α -> β, Measurable g ∧ range g subseteq s ∧ f =ᵐ[μ] g :=
    h.exists_ae_eq_range_subset (Eventually.of_forall hfs) ⟨_, hfs default⟩
  refine ⟨codRestrict g s fun x => hg (mem_range_self _), Measurable.subtype_mk g_meas, ?_⟩
 

Depends on / 依赖: Eventually, Eventually.of_forall, Measurable, Measurable.subtype_mk, Subtype, Subtype.ext_iff, codRestrict, exists_ae_eq_range_subset, ext_iff, filter_upwards, g_meas, h.exists_ae_eq_range_subset, inhabit, mem_range_self, nontriviality, of_forall, subseteq, subtype_mk
-/
theorem subtype_mk (h : AEMeasurable f μ) {s : Set β} {hfs : forall x, f x in s} :
    AEMeasurable (codRestrict f s hfs) μ := by
  nontriviality α; inhabit α
  obtain ⟨g, g_meas, hg, fg⟩ : exists g : α -> β, Measurable g ∧ range g subseteq s ∧ f =ᵐ[μ] g :=
    h.exists_ae_eq_range_subset (Eventually.of_forall hfs) ⟨_, hfs default⟩
  refine ⟨codRestrict g s fun x => hg (mem_range_self _), Measurable.subtype_mk g_meas, ?_⟩
  filter_upwards [fg] with x hx
  simpa [Subtype.ext_iff]

end AEMeasurable

/--
theorem `aemeasurable_const'` / 定理 `aemeasurable_const'`

English:
theorem aemeasurable_const'
  given: (h : forallᵐ (x) (y) ∂μ, f x = f y)
  statement: AEMeasurable f μ
  proof: by
  rcases eq_or_ne μ 0 with (rfl | hμ)
  · exact aemeasurable_zero_measure
  · have := ae_neBot.2 hμ
    rcases h.exists with ⟨x, hx⟩
    exact ⟨const α (f x), measurable_const, EventuallyEq.symm hx⟩

中文:
定理 aemeasurable_const'
  条件: (h : 对任意ᵐ (x) (y) ∂μ, f x = f y)
  结论: 几乎处处可测 f μ
  证明: by
  rcases eq_or_ne μ 0 with (rfl | hμ)
  · exact aemeasurable_zero_measure
  · have := ae_neBot.2 hμ
    rcases h.exists with ⟨x, hx⟩
    exact ⟨const α (f x), measurable_const, EventuallyEq.symm hx⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.symm, ae_neBot, aemeasurable_zero_measure, eq_or_ne, h.exists, measurable_const
-/
theorem aemeasurable_const' (h : forallᵐ (x) (y) ∂μ, f x = f y) : AEMeasurable f μ := by
  rcases eq_or_ne μ 0 with (rfl | hμ)
  · exact aemeasurable_zero_measure
  · have := ae_neBot.2 hμ
    rcases h.exists with ⟨x, hx⟩
    exact ⟨const α (f x), measurable_const, EventuallyEq.symm hx⟩

open scoped Interval in
/--
theorem `aemeasurable_uIoc_iff` / 定理 `aemeasurable_uIoc_iff`

English:
theorem aemeasurable_uIoc_iff
  given: [LinearOrder α] {f : α -> β} {a b : α}
  proof: by
  rw [uIoc_eq_union]; rw [aemeasurable_union_iff]

中文:
定理 aemeasurable_uIoc_iff
  条件: [线性序 α] {f : α -> β} {a b : α}
  证明: by
  rw [uIoc_eq_union]; rw [aemeasurable_union_iff]

Depends on / 依赖: aemeasurable_union_iff, uIoc_eq_union
-/
theorem aemeasurable_uIoc_iff [LinearOrder α] {f : α -> β} {a b : α} :
    (AEMeasurable f <| μ.restrict <| Ι a b) ↔
      (AEMeasurable f <| μ.restrict <| Ioc a b) ∧ (AEMeasurable f <| μ.restrict <| Ioc b a) := by
  rw [uIoc_eq_union]; rw [aemeasurable_union_iff]

/--
theorem `aemeasurable_iff_measurable` / 定理 `aemeasurable_iff_measurable`

English:
theorem aemeasurable_iff_measurable
  given: [μ.IsComplete]
  statement: AEMeasurable f μ ↔ Measurable f
  proof: ⟨fun h => h.nullMeasurable.measurable_of_complete, fun h => h.aemeasurable⟩

中文:
定理 aemeasurable_iff_measurable
  条件: [μ.是完备]
  结论: 几乎处处可测 f μ ↔ 可测 f
  证明: ⟨fun h => h.nullMeasurable.measurable_of_complete, fun h => h.aemeasurable⟩

Depends on / 依赖: aemeasurable, h.aemeasurable, h.nullMeasurable.measurable_of_complete, measurable_of_complete, nullMeasurable
-/
theorem aemeasurable_iff_measurable [μ.IsComplete] : AEMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.nullMeasurable.measurable_of_complete, fun h => h.aemeasurable⟩

/--
theorem `MeasurableEmbedding.aemeasurable_map_iff` / 定理 `MeasurableEmbedding.aemeasurable_map_iff`

English:
theorem MeasurableEmbedding.aemeasurable_map_iff
  given: {g : β -> γ} (hf : MeasurableEmbedding f)
  proof: by
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_measurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩

中文:
定理 可测嵌入.aemeasurable_map_iff
  条件: {g : β -> γ} (hf : 可测嵌入 f)
  证明: by
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_measurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩

Depends on / 依赖: H.comp_measurable, ae_map_iff, comp_measurable, exists_measurable_extend, hf.ae_map_iff, hf.exists_measurable_extend, hf.measurable, measurable
-/
theorem MeasurableEmbedding.aemeasurable_map_iff {g : β -> γ} (hf : MeasurableEmbedding f) :
    AEMeasurable g (μ.map f) ↔ AEMeasurable (g ∘ f) μ := by
  refine ⟨fun H => H.comp_measurable hf.measurable, ?_⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_measurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩

/--
theorem `MeasurableEmbedding.aemeasurable_comp_iff` / 定理 `MeasurableEmbedding.aemeasurable_comp_iff`

English:
theorem MeasurableEmbedding.aemeasurable_comp_iff
  statement: {g : β -> γ} (hg : MeasurableEmbedding g)
  proof: by
  refine ⟨fun H => ?_, hg.measurable.comp_aemeasurable⟩
  suffices AEMeasurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) μ by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp_aemeasurable H.subtype_mk

中文:
定理 可测嵌入.aemeasurable_comp_iff
  结论: {g : β -> γ} (hg : 可测嵌入 g)
  证明: by
  refine ⟨fun H => ?_, hg.measurable.comp_aemeasurable⟩
  suffices AEMeasurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) μ by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp_aemeasurable H.subtype_mk

Depends on / 依赖: AEMeasurable, H.subtype_mk, comp_aemeasurable, comp_eq_id, hg.injective, hg.measurable.comp_aemeasurable, hg.measurable_rangeSplitting.comp_aemeasurable, injective, measurable, measurable_rangeSplitting, rangeFactorization, rangeSplitting, rightInverse_rangeSplitting, subtype_mk
-/
theorem MeasurableEmbedding.aemeasurable_comp_iff {g : β -> γ} (hg : MeasurableEmbedding g)
    {μ : Measure α} : AEMeasurable (g ∘ f) μ ↔ AEMeasurable f μ := by
  refine ⟨fun H => ?_, hg.measurable.comp_aemeasurable⟩
  suffices AEMeasurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) μ by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp_aemeasurable H.subtype_mk

/--
theorem `aemeasurable_restrict_iff_comap_subtype` / 定理 `aemeasurable_restrict_iff_comap_subtype`

English:
theorem aemeasurable_restrict_iff_comap_subtype
  statement: {s : Set α} (hs : MeasurableSet s) {μ : Measure α}
  proof: by
  rw [← map_comap_subtype_coe hs]; rw [(MeasurableEmbedding.subtype_coe hs).aemeasurable_map_iff]

@[to_additive]

中文:
定理 aemeasurable_restrict_iff_comap_subtype
  结论: {s : 集合 α} (hs : 可测集 s) {μ : 测度 α}
  证明: by
  rw [← map_comap_subtype_coe hs]; rw [(MeasurableEmbedding.subtype_coe hs).aemeasurable_map_iff]

@[to_additive]

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, aemeasurable_map_iff, map_comap_subtype_coe, subtype_coe
-/
theorem aemeasurable_restrict_iff_comap_subtype {s : Set α} (hs : MeasurableSet s) {μ : Measure α}
    {f : α -> β} : AEMeasurable f (μ.restrict s) ↔ AEMeasurable (f ∘ (↑) : s -> β) (comap (↑) μ) := by
  rw [← map_comap_subtype_coe hs]; rw [(MeasurableEmbedding.subtype_coe hs).aemeasurable_map_iff]

@[to_additive]
/--
theorem `aemeasurable_one` / 定理 `aemeasurable_one`

English:
theorem aemeasurable_one
  given: [One β]
  statement: AEMeasurable (fun _ : α => (1 : β)) μ
  proof: measurable_one.aemeasurable

@[simp]

中文:
定理 aemeasurable_one
  条件: [幺 β]
  结论: 几乎处处可测 (fun _ : α => (1 : β)) μ
  证明: measurable_one.aemeasurable

@[simp]

Depends on / 依赖: aemeasurable, measurable_one, measurable_one.aemeasurable
-/
theorem aemeasurable_one [One β] : AEMeasurable (fun _ : α => (1 : β)) μ :=
  measurable_one.aemeasurable

@[simp]
/--
theorem `aemeasurable_smul_measure_iff` / 定理 `aemeasurable_smul_measure_iff`

English:
theorem aemeasurable_smul_measure_iff
  given: {c : Real>=0∞} (hc : c != 0)
  proof: ⟨fun h => ⟨h.mk f, h.measurable_mk, (ae_ennreal_smul_measure_iff hc).1 h.ae_eq_mk⟩, fun h =>
    ⟨h.mk f, h.measurable_mk, (ae_ennreal_smul_measure_iff hc).2 h.ae_eq_mk⟩⟩

中文:
定理 aemeasurable_smul_measure_iff
  条件: {c : 实数>=0∞} (hc : c != 0)
  证明: ⟨fun h => ⟨h.mk f, h.measurable_mk, (ae_ennreal_smul_measure_iff hc).1 h.ae_eq_mk⟩, fun h =>
    ⟨h.mk f, h.measurable_mk, (ae_ennreal_smul_measure_iff hc).2 h.ae_eq_mk⟩⟩

Depends on / 依赖: ae_ennreal_smul_measure_iff, ae_eq_mk, h.ae_eq_mk, h.measurable_mk, h.mk, measurable_mk
-/
theorem aemeasurable_smul_measure_iff {c : Real>=0∞} (hc : c != 0) :
    AEMeasurable f (c • μ) ↔ AEMeasurable f μ :=
  ⟨fun h => ⟨h.mk f, h.measurable_mk, (ae_ennreal_smul_measure_iff hc).1 h.ae_eq_mk⟩, fun h =>
    ⟨h.mk f, h.measurable_mk, (ae_ennreal_smul_measure_iff hc).2 h.ae_eq_mk⟩⟩

/--
theorem `aemeasurable_of_aemeasurable_trim` / 定理 `aemeasurable_of_aemeasurable_trim`

English:
theorem aemeasurable_of_aemeasurable_trim
  statement: {α} {m m0 : MeasurableSpace α} {μ : Measure α}
  proof: ⟨hf.mk f, Measurable.mono hf.measurable_mk hm le_rfl, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

中文:
定理 aemeasurable_of_aemeasurable_trim
  结论: {α} {m m0 : 可测空间 α} {μ : 测度 α}
  证明: ⟨hf.mk f, Measurable.mono hf.measurable_mk hm le_rfl, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

Depends on / 依赖: Measurable, Measurable.mono, ae_eq_mk, ae_eq_of_ae_eq_trim, hf.ae_eq_mk, hf.measurable_mk, hf.mk, le_rfl, measurable_mk
-/
theorem aemeasurable_of_aemeasurable_trim {α} {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m <= m0) {f : α -> β} (hf : AEMeasurable f (μ.trim hm)) : AEMeasurable f μ :=
  ⟨hf.mk f, Measurable.mono hf.measurable_mk hm le_rfl, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

/--
theorem `aemeasurable_restrict_of_measurable_subtype` / 定理 `aemeasurable_restrict_of_measurable_subtype`

English:
theorem aemeasurable_restrict_of_measurable_subtype
  statement: {s : Set α} (hs : MeasurableSet s)
  proof: (aemeasurable_restrict_iff_comap_subtype hs).2 hf.aemeasurable

中文:
定理 aemeasurable_restrict_of_measurable_subtype
  结论: {s : 集合 α} (hs : 可测集 s)
  证明: (aemeasurable_restrict_iff_comap_subtype hs).2 hf.aemeasurable

Depends on / 依赖: aemeasurable, aemeasurable_restrict_iff_comap_subtype, hf.aemeasurable
-/
theorem aemeasurable_restrict_of_measurable_subtype {s : Set α} (hs : MeasurableSet s)
    (hf : Measurable fun x : s => f x) : AEMeasurable f (μ.restrict s) :=
  (aemeasurable_restrict_iff_comap_subtype hs).2 hf.aemeasurable

/--
theorem `aemeasurable_map_equiv_iff` / 定理 `aemeasurable_map_equiv_iff`

English:
theorem aemeasurable_map_equiv_iff
  given: (e : α ≃ᵐ β) {f : β -> γ}
  proof: e.measurableEmbedding.aemeasurable_map_iff

中文:
定理 aemeasurable_map_equiv_iff
  条件: (e : α ≃ᵐ β) {f : β -> γ}
  证明: e.measurableEmbedding.aemeasurable_map_iff

Depends on / 依赖: aemeasurable_map_iff, e.measurableEmbedding.aemeasurable_map_iff, measurableEmbedding
-/
theorem aemeasurable_map_equiv_iff (e : α ≃ᵐ β) {f : β -> γ} :
    AEMeasurable f (μ.map e) ↔ AEMeasurable (f ∘ e) μ :=
  e.measurableEmbedding.aemeasurable_map_iff

end

@[fun_prop]
/--
theorem `AEMeasurable.restrict` / 定理 `AEMeasurable.restrict`

English:
theorem AEMeasurable.restrict
  given: (hfm : AEMeasurable f μ) {s}
  statement: AEMeasurable f (μ.restrict s)
  proof: ⟨AEMeasurable.mk f hfm, hfm.measurable_mk, ae_restrict_of_ae hfm.ae_eq_mk⟩

中文:
定理 几乎处处可测.restrict
  条件: (hfm : 几乎处处可测 f μ) {s}
  结论: 几乎处处可测 f (μ.restrict s)
  证明: ⟨AEMeasurable.mk f hfm, hfm.measurable_mk, ae_restrict_of_ae hfm.ae_eq_mk⟩

Depends on / 依赖: AEMeasurable, AEMeasurable.mk, ae_eq_mk, ae_restrict_of_ae, hfm.ae_eq_mk, hfm.measurable_mk, measurable_mk
-/
theorem AEMeasurable.restrict (hfm : AEMeasurable f μ) {s} : AEMeasurable f (μ.restrict s) :=
  ⟨AEMeasurable.mk f hfm, hfm.measurable_mk, ae_restrict_of_ae hfm.ae_eq_mk⟩

/--
theorem `aemeasurable_Ioi_of_forall_Ioc` / 定理 `aemeasurable_Ioi_of_forall_Ioc`

English:
theorem aemeasurable_Ioi_of_forall_Ioc
  statement: {β} {mβ : MeasurableSpace β} [LinearOrder α]
  proof: by
  have : Nonempty α := ⟨x⟩
  obtain ⟨u, hu_tendsto⟩ := exists_seq_tendsto (atTop : Filter α)
  have Ioi_eq_iUnion : Ioi x = ⋃ n : Nat, Ioc x (u n) := by
    rw [iUnion_Ioc_eq_Ioi_self_iff.mpr _]
    exact fun y _ => (hu_tendsto.eventually (eventually_ge_atTop y)).exists
  rw [Ioi_eq_iUnion]; rw [

中文:
定理 aemeasurable_Ioi_of_对任意_Ioc
  结论: {β} {mβ : 可测空间 β} [线性序 α]
  证明: by
  have : Nonempty α := ⟨x⟩
  obtain ⟨u, hu_tendsto⟩ := exists_seq_tendsto (atTop : Filter α)
  have Ioi_eq_iUnion : Ioi x = ⋃ n : Nat, Ioc x (u n) := by
    rw [iUnion_Ioc_eq_Ioi_self_iff.mpr _]
    exact fun y _ => (hu_tendsto.eventually (eventually_ge_atTop y)).exists
  rw [Ioi_eq_iUnion]; rw [

Depends on / 依赖: Filter, Ioc_eq_empty, Ioi_eq_iUnion, Measure, Measure.restrict_empty, Nonempty, aemeasurable_iUnion_iff, aemeasurable_zero_measure, eventually, eventually_ge_atTop, exists_seq_tendsto, g_meas, hu_tendsto, hu_tendsto.eventually, iUnion_Ioc_eq_Ioi_self_iff, iUnion_Ioc_eq_Ioi_self_iff.mpr, lt_or_ge, not_lt, not_lt.mpr, restrict_empty
-/
theorem aemeasurable_Ioi_of_forall_Ioc {β} {mβ : MeasurableSpace β} [LinearOrder α]
    [(atTop : Filter α).IsCountablyGenerated] {x : α} {g : α -> β}
    (g_meas : forall t > x, AEMeasurable g (μ.restrict (Ioc x t))) :
    AEMeasurable g (μ.restrict (Ioi x)) := by
  have : Nonempty α := ⟨x⟩
  obtain ⟨u, hu_tendsto⟩ := exists_seq_tendsto (atTop : Filter α)
  have Ioi_eq_iUnion : Ioi x = ⋃ n : Nat, Ioc x (u n) := by
    rw [iUnion_Ioc_eq_Ioi_self_iff.mpr _]
    exact fun y _ => (hu_tendsto.eventually (eventually_ge_atTop y)).exists
  rw [Ioi_eq_iUnion]; rw [aemeasurable_iUnion_iff]
  intro n
  rcases lt_or_ge x (u n) with h | h
  · exact g_meas (u n) h
  · rw [Ioc_eq_empty (not_lt.mpr h), Measure.restrict_empty]
    exact aemeasurable_zero_measure

section Zero

variable [Zero β]

/--
theorem `aemeasurable_indicator_iff` / 定理 `aemeasurable_indicator_iff`

English:
theorem aemeasurable_indicator_iff
  given: {s} (hs : MeasurableSet s)
  proof: by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.measurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (AEMeasurable.mk f h) :=
      (indicator_ae_eq

中文:
定理 aemeasurable_indicator_iff
  条件: {s} (hs : 可测集 s)
  证明: by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.measurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (AEMeasurable.mk f h) :=
      (indicator_ae_eq

Depends on / 依赖: AEMeasurable, AEMeasurable.mk, Measure, Measure.restrict_le_self, ae_eq_mk, h.ae_eq_mk.trans, h.measurable_mk.indicator, h.mk, h.mono_measure, indicator, indicator_ae_eq_restrict, indicator_ae_eq_restrict_c, indicator_ae_eq_restrict_compl, measurable_mk, mono_measure, restrict, restrict_le_self, s.indicator
-/
theorem aemeasurable_indicator_iff {s} (hs : MeasurableSet s) :
    AEMeasurable (indicator s f) μ ↔ AEMeasurable f (μ.restrict s) := by
  constructor
  · intro h
    exact (h.mono_measure Measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine ⟨indicator s (h.mk f), h.measurable_mk.indicator hs, ?_⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (AEMeasurable.mk f h) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (AEMeasurable.mk f h) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B

/--
theorem `aemeasurable_indicator_iff₀` / 定理 `aemeasurable_indicator_iff₀`

English:
theorem aemeasurable_indicator_iff₀
  given: {s} (hs : NullMeasurableSet s μ)
  proof: by
  rcases hs with ⟨t, ht, hst⟩
  rw [← aemeasurable_congr (indicator_ae_eq_of_ae_eq_set hst.symm)]; rw [aemeasurable_indicator_iff ht]; rw [restrict_congr_set hst]

中文:
定理 aemeasurable_indicator_iff₀
  条件: {s} (hs : NullMeasurableSet s μ)
  证明: by
  rcases hs with ⟨t, ht, hst⟩
  rw [← aemeasurable_congr (indicator_ae_eq_of_ae_eq_set hst.symm)]; rw [aemeasurable_indicator_iff ht]; rw [restrict_congr_set hst]

Depends on / 依赖: aemeasurable_congr, aemeasurable_indicator_iff, hst.symm, indicator_ae_eq_of_ae_eq_set, restrict_congr_set
-/
theorem aemeasurable_indicator_iff₀ {s} (hs : NullMeasurableSet s μ) :
    AEMeasurable (indicator s f) μ ↔ AEMeasurable f (μ.restrict s) := by
  rcases hs with ⟨t, ht, hst⟩
  rw [← aemeasurable_congr (indicator_ae_eq_of_ae_eq_set hst.symm)]; rw [aemeasurable_indicator_iff ht]; rw [restrict_congr_set hst]

/--
lemma `aemeasurable_indicator_const_iff` / 引理 `aemeasurable_indicator_const_iff`

English:
lemma aemeasurable_indicator_const_iff
  given: {s} [MeasurableSingletonClass β] (b : β) [NeZero b]
  proof: by
  classical
  constructor <;> intro h
  · convert! h.nullMeasurable (MeasurableSet.singleton (0 : β)).compl
    rw [indicator_const_preimage_eq_union s {0}ᶜ b]
    simp [NeZero.ne b]
  · exact (aemeasurable_indicator_iff₀ h).mpr aemeasurable_const

@[fun_prop]

中文:
引理 aemeasurable_indicator_const_iff
  条件: {s} [MeasurableSingleton类 β] (b : β) [NeZero b]
  证明: by
  classical
  constructor <;> intro h
  · convert! h.nullMeasurable (MeasurableSet.singleton (0 : β)).compl
    rw [indicator_const_preimage_eq_union s {0}ᶜ b]
    simp [NeZero.ne b]
  · exact (aemeasurable_indicator_iff₀ h).mpr aemeasurable_const

@[fun_prop]

Depends on / 依赖: MeasurableSet, MeasurableSet.singleton, NeZero, NeZero.ne, aemeasurable_const, classical, convert, h.nullMeasurable, indicator_const_preimage_eq_union, nullMeasurable, singleton
-/
lemma aemeasurable_indicator_const_iff {s} [MeasurableSingletonClass β] (b : β) [NeZero b] :
    AEMeasurable (s.indicator (fun _ => b)) μ ↔ NullMeasurableSet s μ := by
  classical
  constructor <;> intro h
  · convert! h.nullMeasurable (MeasurableSet.singleton (0 : β)).compl
    rw [indicator_const_preimage_eq_union s {0}ᶜ b]
    simp [NeZero.ne b]
  · exact (aemeasurable_indicator_iff₀ h).mpr aemeasurable_const

@[fun_prop]
/--
theorem `AEMeasurable.indicator` / 定理 `AEMeasurable.indicator`

English:
theorem AEMeasurable.indicator
  given: (hfm : AEMeasurable f μ) {s} (hs : MeasurableSet s)
  proof: (aemeasurable_indicator_iff hs).mpr hfm.restrict

中文:
定理 几乎处处可测.indicator
  条件: (hfm : 几乎处处可测 f μ) {s} (hs : 可测集 s)
  证明: (aemeasurable_indicator_iff hs).mpr hfm.restrict

Depends on / 依赖: aemeasurable_indicator_iff, hfm.restrict, restrict
-/
theorem AEMeasurable.indicator (hfm : AEMeasurable f μ) {s} (hs : MeasurableSet s) :
    AEMeasurable (s.indicator f) μ :=
  (aemeasurable_indicator_iff hs).mpr hfm.restrict

/--
theorem `AEMeasurable.indicator₀` / 定理 `AEMeasurable.indicator₀`

English:
theorem AEMeasurable.indicator₀
  given: (hfm : AEMeasurable f μ) {s} (hs : NullMeasurableSet s μ)
  proof: (aemeasurable_indicator_iff₀ hs).mpr hfm.restrict

中文:
定理 几乎处处可测.indicator₀
  条件: (hfm : 几乎处处可测 f μ) {s} (hs : NullMeasurableSet s μ)
  证明: (aemeasurable_indicator_iff₀ hs).mpr hfm.restrict

Depends on / 依赖: hfm.restrict, restrict
-/
theorem AEMeasurable.indicator₀ (hfm : AEMeasurable f μ) {s} (hs : NullMeasurableSet s μ) :
    AEMeasurable (s.indicator f) μ :=
  (aemeasurable_indicator_iff₀ hs).mpr hfm.restrict

end Zero

/--
theorem `MeasureTheory.Measure.restrict_map_of_aemeasurable` / 定理 `MeasureTheory.Measure.restrict_map_of_aemeasurable`

English:
theorem MeasureTheory.Measure.restrict_map_of_aemeasurable
  statement: {f : α -> δ} (hf : AEMeasurable f μ)
  proof: calc
    (μ.map f).restrict s = (μ.map (hf.mk f)).restrict s := by
      congr 1
      apply Measure.map_congr hf.ae_eq_mk
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map (hf.mk f) := Measure.restrict_map hf.measurable_mk hs
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map f :=
      (Measure.map_congr (ae_restr

中文:
定理 测度论.测度.restrict_map_of_aemeasurable
  结论: {f : α -> δ} (hf : 几乎处处可测 f μ)
  证明: calc
    (μ.map f).restrict s = (μ.map (hf.mk f)).restrict s := by
      congr 1
      apply Measure.map_congr hf.ae_eq_mk
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map (hf.mk f) := Measure.restrict_map hf.measurable_mk hs
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map f :=
      (Measure.map_congr (ae_restr

Depends on / 依赖: EventuallyEq, EventuallyEq.refl, Measure, Measure.map_congr, Measure.restrict_apply, Measure.restrict_map, NoBotOrder, NoMinOrder, Preorder, ae_eq_mk, ae_restrict_of_ae, congr_arg, hf.ae_eq_mk, hf.ae_eq_mk.symm, hf.ae_eq_mk.symm.preimage, hf.measurable_mk, hf.mk, map_congr, measurable_mk, measure_congr
-/
theorem MeasureTheory.Measure.restrict_map_of_aemeasurable {f : α -> δ} (hf : AEMeasurable f μ)
    {s : Set δ} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  calc
    (μ.map f).restrict s = (μ.map (hf.mk f)).restrict s := by
      congr 1
      apply Measure.map_congr hf.ae_eq_mk
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map (hf.mk f) := Measure.restrict_map hf.measurable_mk hs
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map f :=
      (Measure.map_congr (ae_restrict_of_ae hf.ae_eq_mk.symm))
    _ = (μ.restrict <| f ⁻¹' s).map f := by
      apply congr_arg
      ext1 t ht
      simp only [ht, Measure.restrict_apply]
      apply measure_congr
      apply (EventuallyEq.refl _ _).inter (hf.ae_eq_mk.symm.preimage s)

/--
theorem `MeasureTheory.Measure.map_mono_of_aemeasurable` / 定理 `MeasureTheory.Measure.map_mono_of_aemeasurable`

English:
theorem MeasureTheory.Measure.map_mono_of_aemeasurable
  statement: {f : α -> δ} (h : μ <= ν)
  proof: le_iff.2 fun s hs => by simpa [hf, hs, hf.mono_measure h] using h (f ⁻¹' s)

中文:
定理 测度论.测度.map_mono_of_aemeasurable
  结论: {f : α -> δ} (h : μ <= ν)
  证明: le_iff.2 fun s hs => by simpa [hf, hs, hf.mono_measure h] using h (f ⁻¹' s)

Depends on / 依赖: hf.mono_measure, le_iff, mono_measure
-/
theorem MeasureTheory.Measure.map_mono_of_aemeasurable {f : α -> δ} (h : μ <= ν)
    (hf : AEMeasurable f ν) : μ.map f <= ν.map f :=
  le_iff.2 fun s hs => by simpa [hf, hs, hf.mono_measure h] using h (f ⁻¹' s)

/--
lemma `MeasureTheory.NullMeasurable.aemeasurable` / 引理 `MeasureTheory.NullMeasurable.aemeasurable`

English:
lemma MeasureTheory.NullMeasurable.aemeasurable
  statement: {f : α -> β}
  proof: by
  classical
  nontriviality β; inhabit β
  rcases hc.1 with ⟨S, hSc, rfl⟩
  choose! T hTf hTm hTeq using fun s hs => (h <| .basic s hs).exists_measurable_subset_ae_eq
  choose! U hUf hUm hUeq using fun s hs => (h <| .basic s hs).exists_measurable_superset_ae_eq
  set v := ⋃ s in S, U s \ T s
  ha

中文:
引理 测度论.NullMeasurable.aemeasurable
  结论: {f : α -> β}
  证明: by
  classical
  nontriviality β; inhabit β
  rcases hc.1 with ⟨S, hSc, rfl⟩
  choose! T hTf hTm hTeq using fun s hs => (h <| .basic s hs).exists_measurable_subset_ae_eq
  choose! U hUf hUm hUeq using fun s hs => (h <| .basic s hs).exists_measurable_superset_ae_eq
  set v := ⋃ s in S, U s \ T s
  ha

Depends on / 依赖: MeasurableSet, ae_le_set, biUnion, classical, exists_measurable_subset_ae_eq, exists_measurable_superset_ae_eq, inhabit, measure_biUnion_null_iff, nontriviality, v.piece
-/
lemma MeasureTheory.NullMeasurable.aemeasurable {f : α -> β}
    [hc : MeasurableSpace.CountablyGenerated β] (h : NullMeasurable f μ) : AEMeasurable f μ := by
  classical
  nontriviality β; inhabit β
  rcases hc.1 with ⟨S, hSc, rfl⟩
  choose! T hTf hTm hTeq using fun s hs => (h <| .basic s hs).exists_measurable_subset_ae_eq
  choose! U hUf hUm hUeq using fun s hs => (h <| .basic s hs).exists_measurable_superset_ae_eq
  set v := ⋃ s in S, U s \ T s
  have hvm : MeasurableSet v := .biUnion hSc fun s hs => (hUm s hs).diff (hTm s hs)
have hvμ : μ v = 0 := (measure_biUnion_null_iff hSc).2 fun s hs => ae_le_set.1
    ((hUeq s hs).trans (hTeq s hs).symm).le
  refine ⟨v.piecewise (fun _ => default) f, ?_, measure_mono_null (fun x =>
    not_imp_comm.2 fun hxv => (piecewise_eq_of_notMem _ _ _ hxv).symm) hvμ⟩
  refine measurable_of_restrict_of_restrict_compl hvm ?_ ?_
  · rw [domRestrict_piecewise]
    apply measurable_const
  · rw [domRestrict_piecewise_compl, domRestrict_eq]
    refine measurable_generateFrom fun s hs => .of_subtype_image ?_
    rw [preimage_comp]; rw [Subtype.image_preimage_coe]
    convert! (hTm s hs).diff hvm using 1
    rw [inter_comm]
    refine Set.ext fun x => and_congr_left fun hxv => ⟨fun hx => ?_, fun hx => hTf s hs hx⟩
exact by_contra fun hx' => hxv mem_biUnion hs ⟨hUf s hs hx, hx'⟩

/--
lemma `MeasureTheory.NullMeasurable.aemeasurable_of_aerange` / 引理 `MeasureTheory.NullMeasurable.aemeasurable_of_aerange`

English:
lemma MeasureTheory.NullMeasurable.aemeasurable_of_aerange
  statement: {f : α -> β} {t : Set β}
  proof: by
  rcases eq_empty_or_nonempty t with rfl | hne
  · obtain rfl : μ = 0 := by simpa using hft
    apply aemeasurable_zero_measure
  · rw [← μ.ae_completion] at hft
    obtain ⟨f', hf'm, hf't, hff'⟩ :
        exists f' : α -> β, NullMeasurable f' μ ∧ range f' subseteq t ∧ f =ᵐ[μ] f' :=
      h.measu

中文:
引理 测度论.NullMeasurable.aemeasurable_of_aerange
  结论: {f : α -> β} {t : 集合 β}
  证明: by
  rcases eq_empty_or_nonempty t with rfl | hne
  · obtain rfl : μ = 0 := by simpa using hft
    apply aemeasurable_zero_measure
  · rw [← μ.ae_completion] at hft
    obtain ⟨f', hf'm, hf't, hff'⟩ :
        exists f' : α -> β, NullMeasurable f' μ ∧ range f' subseteq t ∧ f =ᵐ[μ] f' :=
      h.measu

Depends on / 依赖: Classical, Classical.arbitrary, NullMeasurable, ae_completion, aemeasurable, aemeasurable.exists_ae_eq_range_subset, aemeasurable_zero_measure, arbitrary, classical, comp_aemeasurable, eq_empty_or_nonempty, exists_ae_eq_range_subset, exists_lt, h.measurable, m.measurable, measurable, measurable_subtype_coe, measurable_subtype_coe.comp_aemeasurable, range_subset_iff, replace
-/
lemma MeasureTheory.NullMeasurable.aemeasurable_of_aerange {f : α -> β} {t : Set β}
    [MeasurableSpace.CountablyGenerated t] (h : NullMeasurable f μ) (hft : forallᵐ x ∂μ, f x in t) :
    AEMeasurable f μ := by
  rcases eq_empty_or_nonempty t with rfl | hne
  · obtain rfl : μ = 0 := by simpa using hft
    apply aemeasurable_zero_measure
  · rw [← μ.ae_completion] at hft
    obtain ⟨f', hf'm, hf't, hff'⟩ :
        exists f' : α -> β, NullMeasurable f' μ ∧ range f' subseteq t ∧ f =ᵐ[μ] f' :=
      h.measurable'.aemeasurable.exists_ae_eq_range_subset hft hne
    rw [range_subset_iff] at hf't
    lift f' to α -> t using hf't
    replace hf'm : NullMeasurable f' μ := hf'm.measurable'.subtype_mk
    exact (measurable_subtype_coe.comp_aemeasurable hf'm.aemeasurable).congr hff'.symm

namespace MeasureTheory
namespace Measure

/--
lemma `map_sum` / 引理 `map_sum`

English:
lemma map_sum
  given: {ι : Type*} {m : ι -> Measure α} {f : α -> β} (hf : AEMeasurable f (Measure.sum m))
  proof: by
  ext s hs
  rw [map_apply_of_aemeasurable hf hs]; rw [sum_apply₀ _ (hf.nullMeasurable hs)]; rw [sum_apply _ hs]
  have M i : AEMeasurable f (m i) := hf.mono_measure (le_sum m i)
  simp_rw [map_apply_of_aemeasurable (M _) hs]

中文:
引理 map_sum
  条件: {ι : 类型} {m : ι -> 测度 α} {f : α -> β} (hf : 几乎处处可测 f (测度.求和 m))
  证明: by
  ext s hs
  rw [map_apply_of_aemeasurable hf hs]; rw [sum_apply₀ _ (hf.nullMeasurable hs)]; rw [sum_apply _ hs]
  have M i : AEMeasurable f (m i) := hf.mono_measure (le_sum m i)
  simp_rw [map_apply_of_aemeasurable (M _) hs]

Depends on / 依赖: AEMeasurable, hf.mono_measure, hf.nullMeasurable, le_sum, map_apply_of_aemeasurable, mono_measure, nullMeasurable, simp_rw, sum_apply
-/
lemma map_sum {ι : Type*} {m : ι -> Measure α} {f : α -> β} (hf : AEMeasurable f (Measure.sum m)) :
    Measure.map f (Measure.sum m) = Measure.sum (fun i => Measure.map f (m i)) := by
  ext s hs
  rw [map_apply_of_aemeasurable hf hs]; rw [sum_apply₀ _ (hf.nullMeasurable hs)]; rw [sum_apply _ hs]
  have M i : AEMeasurable f (m i) := hf.mono_measure (le_sum m i)
  simp_rw [map_apply_of_aemeasurable (M _) hs]

/--
lemma `map_finset_sum` / 引理 `map_finset_sum`

English:
lemma map_finset_sum
  statement: {ι β : Type*} {mβ : MeasurableSpace β} {m : ι -> Measure α}
  proof: by
  rw [← sum_coe_finset]; rw [← sum_coe_finset]; rw [Measure.map_sum]
  rwa [sum_coe_finset]

中文:
引理 map_finset_sum
  结论: {ι β : 类型} {mβ : 可测空间 β} {m : ι -> 测度 α}
  证明: by
  rw [← sum_coe_finset]; rw [← sum_coe_finset]; rw [Measure.map_sum]
  rwa [sum_coe_finset]

Depends on / 依赖: Measure, Measure.map_sum, map_sum, sum_coe_finset
-/
lemma map_finset_sum {ι β : Type*} {mβ : MeasurableSpace β} {m : ι -> Measure α}
    {f : α -> β} {s : Finset ι} (hf : AEMeasurable f (∑ i in s, m i)) :
    map f (∑ i in s, m i) = ∑ i in s, (m i).map f := by
  rw [← sum_coe_finset]; rw [← sum_coe_finset]; rw [Measure.map_sum]
  rwa [sum_coe_finset]

/--
lemma `map_finset_sum'` / 引理 `map_finset_sum'`

English:
lemma map_finset_sum'
  statement: {ι β : Type*} [Fintype ι] {mβ : MeasurableSpace β} {m : ι -> Measure α}
  proof: map_finset_sum hf

中文:
引理 map_finset_sum'
  结论: {ι β : 类型} [有限类型 ι] {mβ : 可测空间 β} {m : ι -> 测度 α}
  证明: map_finset_sum hf

Depends on / 依赖: map_finset_sum
-/
lemma map_finset_sum' {ι β : Type*} [Fintype ι] {mβ : MeasurableSpace β} {m : ι -> Measure α}
    {f : α -> β} (hf : AEMeasurable f (∑ i, m i)) :
    map f (∑ i, m i) = ∑ i, (m i).map f := map_finset_sum hf

instance (μ : Measure α) (f : α -> β) [SFinite μ] : SFinite (μ.map f) := by
  by_cases H : AEMeasurable f μ
  · rw [← sum_sfiniteSeq μ] at H ⊢
    rw [map_sum H]
    infer_instance
  · rw [map_of_not_aemeasurable H]
    infer_instance

end Measure
end MeasureTheory
