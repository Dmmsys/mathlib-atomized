/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The Giry monad

Let X be a measurable space. The collection of all measures on X again
forms a measurable space. This construction forms a monad on
measurable spaces and measurable functions, called the Giry monad.

Note that most sources use the term "Giry monad" for the restriction
to *probability* measures. Here we include all measures on X.

See also `Mathlib/MeasureTheory/Category/MeasCat.lean`, containing an upgrade of the type-level
monad to an honest monad of the functor `measure : MeasCat ⥤ MeasCat`.

## References

* <https://ncatlab.org/nlab/show/Giry+monad>

## Tags

giry monad
-/

@[expose] public section


noncomputable section

open ENNReal Set Filter

variable {α β : Type*}

namespace MeasureTheory

namespace Measure

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/--
Instance `instMeasurableSpace` / 实例 `instMeasurableSpace`

English:
instance instMeasurableSpace
  signature: : MeasurableSpace (Measure α)
  body: ⨆ (s : Set α) (_ : MeasurableSet s), (borel Real>=0∞).comap fun μ => μ s

中文:
实例 instMeasurableSpace
  签名: : MeasurableSpace (Measure α)
  定义体: ⨆ (s : Set α) (_ : MeasurableSet s), (borel Real>=0∞).comap fun μ => μ s

Depends on / 依赖: IsEmpty, IsWellOrder, MeasurableSet
-/
instance instMeasurableSpace : MeasurableSpace (Measure α) :=
  ⨆ (s : Set α) (_ : MeasurableSet s), (borel Real>=0∞).comap fun μ => μ s

/--
theorem `measurable_coe` / 定理 `measurable_coe`

English:
theorem measurable_coe
  given: {s : Set α} (hs : MeasurableSet s)
  statement: Measurable fun μ : Measure α => μ s
  proof: Measurable.of_comap_le le_iSup_of_le s le_iSup_of_le hs le_rfl

中文:
定理 measurable_coe
  条件: {s : Set α} (hs : MeasurableSet s)
  结论: Measurable fun μ : Measure α => μ s
  证明: Measurable.of_comap_le le_iSup_of_le s le_iSup_of_le hs le_rfl

Depends on / 依赖: Measurable, Measurable.of_comap_le, le_iSup_of_le, le_rfl, of_comap_le
-/
theorem measurable_coe {s : Set α} (hs : MeasurableSet s) : Measurable fun μ : Measure α => μ s :=
Measurable.of_comap_le le_iSup_of_le s le_iSup_of_le hs le_rfl

/--
theorem `measurable_of_measurable_coe` / 定理 `measurable_of_measurable_coe`

English:
theorem measurable_of_measurable_coe
  statement: (f : β -> Measure α)
  proof: Measurable.of_le_map
    iSup₂_le fun s hs =>
MeasurableSpace.comap_le_iff_le_map.2 by rw [MeasurableSpace.map_comp]; exact h s hs

中文:
定理 measurable_of_measurable_coe
  结论: (f : β -> Measure α)
  证明: Measurable.of_le_map
    iSup₂_le fun s hs =>
MeasurableSpace.comap_le_iff_le_map.2 by rw [MeasurableSpace.map_comp]; exact h s hs

Depends on / 依赖: Measurable, Measurable.of_le_map, MeasurableSpace, MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp, comap_le_iff_le_map, map_comp, of_le_map
-/
theorem measurable_of_measurable_coe (f : β -> Measure α)
    (h : forall (s : Set α), MeasurableSet s -> Measurable fun b => f b s) : Measurable f :=
Measurable.of_le_map
    iSup₂_le fun s hs =>
MeasurableSpace.comap_le_iff_le_map.2 by rw [MeasurableSpace.map_comp]; exact h s hs

/--
Instance `instMeasurableAdd₂` / 实例 `instMeasurableAdd₂`

English:
instance instMeasurableAdd₂
  signature: {α : Type*} {m : MeasurableSpace α}
  body: by
  refine ⟨Measure.measurable_of_measurable_coe _ fun s hs => ?_⟩
  simp_rw [Measure.coe_add, Pi.add_apply]
  refine Measurable.add ?_ ?_
  · exact (Measure.measurable_coe hs).comp measurable_fst
  · exact (Measure.measurable_coe hs).comp measurable_snd

中文:
实例 instMeasurableAdd₂
  签名: {α : 类型} {m : MeasurableSpace α}
  定义体: by
  refine ⟨Measure.measurable_of_measurable_coe _ fun s hs => ?_⟩
  simp_rw [Measure.coe_add, Pi.add_apply]
  refine Measurable.add ?_ ?_
  · exact (Measure.measurable_coe hs).comp measurable_fst
  · exact (Measure.measurable_coe hs).comp measurable_snd

Depends on / 依赖: InvImage, InvImage.wf, IsWellFounded, IsWellFounded.wf, Measurable, Measurable.add, Measure, Measure.coe_add, Measure.measurable_coe, Measure.measurable_of_measurable_coe, Pi.add_apply, add_apply, coe_add, measurable_coe, measurable_fst, measurable_of_measurable_coe, measurable_snd, simp_rw
-/
instance instMeasurableAdd₂ {α : Type*} {m : MeasurableSpace α} : MeasurableAdd₂ (Measure α) := by
  refine ⟨Measure.measurable_of_measurable_coe _ fun s hs => ?_⟩
  simp_rw [Measure.coe_add, Pi.add_apply]
  refine Measurable.add ?_ ?_
  · exact (Measure.measurable_coe hs).comp measurable_fst
  · exact (Measure.measurable_coe hs).comp measurable_snd

-- There is no typeclass for measurability of `SMul` only on that side, otherwise we could
-- turn that into an instance.
@[fun_prop]
/--
lemma `_root_.Measurable.smul_measure` / 引理 `_root_.Measurable.smul_measure`

English:
lemma _root_.Measurable.smul_measure
  given: {f : α -> Real>=0∞} (hf : Measurable f) (μ : Measure β)
  proof: by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  fun_prop

中文:
引理 _root_.Measurable.smul_measure
  条件: {f : α -> 实数>=0∞} (hf : Measurable f) (μ : Measure β)
  证明: by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  fun_prop

Depends on / 依赖: Measure, Measure.measurable_of_measurable_coe, Measure.smul_apply, fun_prop, measurable_of_measurable_coe, measure, smul_apply, smul_eq_mul
-/
lemma _root_.Measurable.smul_measure {f : α -> Real>=0∞} (hf : Measurable f) (μ : Measure β) :
    Measurable (fun x => f x • μ) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  fun_prop

/--
theorem `measurable_measure` / 定理 `measurable_measure`

English:
theorem measurable_measure
  given: {μ : α -> Measure β}
  proof: ⟨fun hμ _s hs => (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩

中文:
定理 measurable_measure
  条件: {μ : α -> Measure β}
  证明: ⟨fun hμ _s hs => (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩

Depends on / 依赖: measurable_coe, measurable_of_measurable_coe
-/
theorem measurable_measure {μ : α -> Measure β} :
    Measurable μ ↔ forall (s : Set β), MeasurableSet s -> Measurable fun b => μ b s :=
  ⟨fun hμ _s hs => (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩

/--
theorem `_root_.Measurable.measure_of_isPiSystem` / 定理 `_root_.Measurable.measure_of_isPiSystem`

English:
theorem _root_.Measurable.measure_of_isPiSystem
  statement: {μ : α -> Measure β} [forall a, IsFiniteMeasure (μ a)]
  proof: by
  rw [measurable_measure]
  intro s hs
  induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp
  | basic s hs => exact h_basic s hs
  | compl s hsm ihs =>
    simp only [measure_compl hsm (measure_ne_top _ _)]
    exact h_univ.sub ihs
  | iUnion f hfd hfm ihf =>

中文:
定理 _root_.Measurable.measure_of_isPiSystem
  结论: {μ : α -> Measure β} [对任意 a, IsFiniteMeasure (μ a)]
  证明: by
  rw [measurable_measure]
  intro s hs
  induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp
  | basic s hs => exact h_basic s hs
  | compl s hsm ihs =>
    simp only [measure_compl hsm (measure_ne_top _ _)]
    exact h_univ.sub ihs
  | iUnion f hfd hfm ihf =>

Depends on / 依赖: MeasurableSpace, MeasurableSpace.induction_on_inter, h_basic, h_univ, h_univ.sub, iUnion, induction_on_inter, measurable_measure, measure_compl, measure_iUnion, measure_ne_top
-/
theorem _root_.Measurable.measure_of_isPiSystem {μ : α -> Measure β} [forall a, IsFiniteMeasure (μ a)]
    {S : Set (Set β)} (hgen : ‹MeasurableSpace β› = .generateFrom S) (hpi : IsPiSystem S)
    (h_basic : forall s in S, Measurable fun a => μ a s) (h_univ : Measurable fun a => μ a univ) :
    Measurable μ := by
  rw [measurable_measure]
  intro s hs
  induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp
  | basic s hs => exact h_basic s hs
  | compl s hsm ihs =>
    simp only [measure_compl hsm (measure_ne_top _ _)]
    exact h_univ.sub ihs
  | iUnion f hfd hfm ihf =>
    simpa only [measure_iUnion hfd hfm] using .tsum ihf

/--
theorem `_root_.Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` / 定理 `_root_.Measurable.measure_of_isPiSystem_of_isProbabilityMeasure`

English:
theorem _root_.Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
  statement: {μ : α -> Measure β}
  proof: .measure_of_isPiSystem hgen hpi h_basic by simp

@[fun_prop]

中文:
定理 _root_.Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
  结论: {μ : α -> Measure β}
  证明: .measure_of_isPiSystem hgen hpi h_basic by simp

@[fun_prop]

Depends on / 依赖: h_basic, measure_of_isPiSystem
-/
theorem _root_.Measurable.measure_of_isPiSystem_of_isProbabilityMeasure {μ : α -> Measure β}
    [forall a, IsProbabilityMeasure (μ a)]
    {S : Set (Set β)} (hgen : ‹MeasurableSpace β› = .generateFrom S) (hpi : IsPiSystem S)
    (h_basic : forall s in S, Measurable fun a => μ a s) : Measurable μ :=
.measure_of_isPiSystem hgen hpi h_basic by simp

@[fun_prop]
/--
theorem `measurable_map` / 定理 `measurable_map`

English:
theorem measurable_map
  given: (f : α -> β) (hf : Measurable f)
  proof: by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [map_apply hf hs]
  exact measurable_coe (hf hs)

@[fun_prop]

中文:
定理 measurable_map
  条件: (f : α -> β) (hf : Measurable f)
  证明: by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [map_apply hf hs]
  exact measurable_coe (hf hs)

@[fun_prop]

Depends on / 依赖: map_apply, measurable_coe, measurable_of_measurable_coe, simp_rw
-/
theorem measurable_map (f : α -> β) (hf : Measurable f) :
    Measurable fun μ : Measure α => map f μ := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [map_apply hf hs]
  exact measurable_coe (hf hs)

@[fun_prop]
/--
theorem `measurable_dirac` / 定理 `measurable_dirac`

English:
theorem measurable_dirac
  statement: Measurable (Measure.dirac : α -> Measure α)
  proof: by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [dirac_apply' _ hs]
  exact measurable_one.indicator hs

@[fun_prop]

中文:
定理 measurable_dirac
  结论: Measurable (Measure.dirac : α -> Measure α)
  证明: by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [dirac_apply' _ hs]
  exact measurable_one.indicator hs

@[fun_prop]

Depends on / 依赖: dirac_apply, indicator, measurable_of_measurable_coe, measurable_one, measurable_one.indicator, simp_rw
-/
theorem measurable_dirac : Measurable (Measure.dirac : α -> Measure α) := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [dirac_apply' _ hs]
  exact measurable_one.indicator hs

@[fun_prop]
/--
theorem `measurable_lintegral` / 定理 `measurable_lintegral`

English:
theorem measurable_lintegral
  given: {f : α -> Real>=0∞} (hf : Measurable f)
  proof: by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine .iSup fun n => Finset.measurable_fun_sum _ fun i _ => ?_
  refine Measurable.const_mul ?_ _
  exact measurable_coe ((SimpleFunc.eapprox f n).measurableSet_preimage _)

中文:
定理 measurable_lintegral
  条件: {f : α -> 实数>=0∞} (hf : Measurable f)
  证明: by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine .iSup fun n => Finset.measurable_fun_sum _ fun i _ => ?_
  refine Measurable.const_mul ?_ _
  exact measurable_coe ((SimpleFunc.eapprox f n).measurableSet_preimage _)

Depends on / 依赖: Finset, Finset.measurable_fun_sum, Measurable, Measurable.const_mul, SimpleFunc, SimpleFunc.eapprox, SimpleFunc.lintegral, const_mul, eapprox, lintegral, lintegral_eq_iSup_eapprox_lintegral, measurableSet_preimage, measurable_coe, measurable_fun_sum
-/
theorem measurable_lintegral {f : α -> Real>=0∞} (hf : Measurable f) :
    Measurable fun μ : Measure α => ∫⁻ x, f x ∂μ := by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine .iSup fun n => Finset.measurable_fun_sum _ fun i _ => ?_
  refine Measurable.const_mul ?_ _
  exact measurable_coe ((SimpleFunc.eapprox f n).measurableSet_preimage _)

/--
Definition of `join` / `join` 的定义

English:
definition join
  signature: (m : Measure (Measure α))
  body: Measure.ofMeasurable (fun s _ => ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, zero_mul])
    (by
      intro f hf h
      simp_rw [measure_iUnion h hf]
      apply lintegral_tsum
      intro i; exact (measurable_coe (hf i)).aemeasurable)

@[simp]

中文:
定义 join
  签名: (m : Measure (Measure α))
  定义体: Measure.ofMeasurable (fun s _ => ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, zero_mul])
    (by
      intro f hf h
      simp_rw [measure_iUnion h hf]
      apply lintegral_tsum
      intro i; exact (measurable_coe (hf i)).aemeasurable)

@[simp]

Depends on / 依赖: Measure, Measure.ofMeasurable, aemeasurable, lintegral_const, lintegral_tsum, measurable_coe, measure_empty, measure_iUnion, ofMeasurable, simp_rw, zero_mul
-/
def join (m : Measure (Measure α)) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, zero_mul])
    (by
      intro f hf h
      simp_rw [measure_iUnion h hf]
      apply lintegral_tsum
      intro i; exact (measurable_coe (hf i)).aemeasurable)

@[simp]
/--
theorem `join_apply` / 定理 `join_apply`

English:
theorem join_apply
  given: {m : Measure (Measure α)} {s : Set α} (hs : MeasurableSet s)
  proof: Measure.ofMeasurable_apply s hs

中文:
定理 join_apply
  条件: {m : Measure (Measure α)} {s : Set α} (hs : MeasurableSet s)
  证明: Measure.ofMeasurable_apply s hs

Depends on / 依赖: Measure, Measure.ofMeasurable_apply, ofMeasurable_apply
-/
theorem join_apply {m : Measure (Measure α)} {s : Set α} (hs : MeasurableSet s) :
    join m s = ∫⁻ μ, μ s ∂m :=
  Measure.ofMeasurable_apply s hs

/--
theorem `le_join_apply` / 定理 `le_join_apply`

English:
theorem le_join_apply
  given: (m : Measure (Measure α)) (s : Set α)
  statement: ∫⁻ μ, μ s ∂m <= join m s
  proof: by
  rw [measure_eq_iInf]
  exact le_iInf₂ fun t hst => le_iInf fun htm => join_apply htm ▸ by gcongr

@[simp]

中文:
定理 le_join_apply
  条件: (m : Measure (Measure α)) (s : Set α)
  结论: ∫⁻ μ, μ s ∂m <= join m s
  证明: by
  rw [measure_eq_iInf]
  exact le_iInf₂ fun t hst => le_iInf fun htm => join_apply htm ▸ by gcongr

@[simp]

Depends on / 依赖: join_apply, le_iInf, measure_eq_iInf
-/
theorem le_join_apply (m : Measure (Measure α)) (s : Set α) : ∫⁻ μ, μ s ∂m <= join m s := by
  rw [measure_eq_iInf]
  exact le_iInf₂ fun t hst => le_iInf fun htm => join_apply htm ▸ by gcongr

@[simp]
/--
theorem `join_smul` / 定理 `join_smul`

English:
theorem join_smul
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R)
  proof: by
  ext s hs
  simp [hs]

中文:
定理 join_smul
  结论: {R : 类型} [SMul R 实数>=0∞] [IsScalarTower R 实数>=0∞ 实数>=0∞] (c : R)
  证明: by
  ext s hs
  simp [hs]
-/
theorem join_smul {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R)
    (m : Measure (Measure α)) : (c • m).join = c • m.join := by
  ext s hs
  simp [hs]

/--
lemma `join_sum` / 引理 `join_sum`

English:
lemma join_sum
  given: {ι : Type*} (m : ι -> Measure (Measure α))
  proof: by
  ext s hs
  simp_rw [sum_apply _ hs, join_apply hs, lintegral_sum_measure]

@[simp]

中文:
引理 join_sum
  条件: {ι : 类型} (m : ι -> Measure (Measure α))
  证明: by
  ext s hs
  simp_rw [sum_apply _ hs, join_apply hs, lintegral_sum_measure]

@[simp]

Depends on / 依赖: join_apply, lintegral_sum_measure, simp_rw, sum_apply
-/
lemma join_sum {ι : Type*} (m : ι -> Measure (Measure α)) :
    (sum m).join = sum fun (i : ι) => (m i).join := by
  ext s hs
  simp_rw [sum_apply _ hs, join_apply hs, lintegral_sum_measure]

@[simp]
/--
theorem `join_dirac` / 定理 `join_dirac`

English:
theorem join_dirac
  given: (μ : Measure α)
  statement: join (dirac μ) = μ
  proof: by
  ext s hs
  simp [hs, lintegral_dirac', measurable_coe]

中文:
定理 join_dirac
  条件: (μ : Measure α)
  结论: join (dirac μ) = μ
  证明: by
  ext s hs
  simp [hs, lintegral_dirac', measurable_coe]

Depends on / 依赖: lintegral_dirac, measurable_coe
-/
theorem join_dirac (μ : Measure α) : join (dirac μ) = μ := by
  ext s hs
  simp [hs, lintegral_dirac', measurable_coe]

/--
theorem `le_ae_join` / 定理 `le_ae_join`

English:
theorem le_ae_join
  given: (m : Measure (Measure α))
  statement: (ae m).bind ae <= ae m.join
  proof: by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, htm, ht⟩
  rw [join_apply htm]; rw [lintegral_eq_zero_iff (measurable_coe htm)] at ht
  rw [mem_bind']
  exact ht.mono fun _ => measure_mono_null hst

中文:
定理 le_ae_join
  条件: (m : Measure (Measure α))
  结论: (ae m).bind ae <= ae m.join
  证明: by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, htm, ht⟩
  rw [join_apply htm]; rw [lintegral_eq_zero_iff (measurable_coe htm)] at ht
  rw [mem_bind']
  exact ht.mono fun _ => measure_mono_null hst

Depends on / 依赖: exists_measurable_superset_of_null, ht.mono, join_apply, lintegral_eq_zero_iff, measurable_coe, measure_mono_null, mem_bind
-/
theorem le_ae_join (m : Measure (Measure α)) : (ae m).bind ae <= ae m.join := by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, htm, ht⟩
  rw [join_apply htm]; rw [lintegral_eq_zero_iff (measurable_coe htm)] at ht
  rw [mem_bind']
  exact ht.mono fun _ => measure_mono_null hst

/--
theorem `ae_ae_of_ae_join` / 定理 `ae_ae_of_ae_join`

English:
theorem ae_ae_of_ae_join
  given: {m : Measure (Measure α)} {p : α -> Prop} (h : forallᵐ a ∂m.join, p a)
  proof: le_ae_join m h

中文:
定理 ae_ae_of_ae_join
  条件: {m : Measure (Measure α)} {p : α -> 命题} (h : 对任意ᵐ a ∂m.join, p a)
  证明: le_ae_join m h

Depends on / 依赖: le_ae_join
-/
theorem ae_ae_of_ae_join {m : Measure (Measure α)} {p : α -> Prop} (h : forallᵐ a ∂m.join, p a) :
    forallᵐ μ ∂m, forallᵐ a ∂μ, p a :=
  le_ae_join m h

/--
theorem `_root_.AEMeasurable.ae_of_join` / 定理 `_root_.AEMeasurable.ae_of_join`

English:
theorem _root_.AEMeasurable.ae_of_join
  statement: {m : Measure (Measure α)} {f : α -> β}
  proof: let ⟨g, hgm, hg⟩ := h; (ae_ae_of_ae_join hg).mono fun _μ hμ => ⟨g, hgm, hμ⟩

中文:
定理 _root_.AEMeasurable.ae_of_join
  结论: {m : Measure (Measure α)} {f : α -> β}
  证明: let ⟨g, hgm, hg⟩ := h; (ae_ae_of_ae_join hg).mono fun _μ hμ => ⟨g, hgm, hμ⟩

Depends on / 依赖: ae_ae_of_ae_join
-/
theorem _root_.AEMeasurable.ae_of_join {m : Measure (Measure α)} {f : α -> β}
    (h : AEMeasurable f m.join) : forallᵐ μ ∂m, AEMeasurable f μ :=
  let ⟨g, hgm, hg⟩ := h; (ae_ae_of_ae_join hg).mono fun _μ hμ => ⟨g, hgm, hμ⟩

/--
theorem `aemeasurable_lintegral` / 定理 `aemeasurable_lintegral`

English:
theorem aemeasurable_lintegral
  statement: {m : Measure (Measure α)} {f : α -> Real>=0∞}
  proof: let ⟨g, hgm, hfg⟩ := h
  ⟨fun μ => ∫⁻ a, g a ∂μ, measurable_lintegral hgm,
    (ae_ae_of_ae_join hfg).mono fun _ => lintegral_congr_ae⟩

@[simp]

中文:
定理 aemeasurable_lintegral
  结论: {m : Measure (Measure α)} {f : α -> 实数>=0∞}
  证明: let ⟨g, hgm, hfg⟩ := h
  ⟨fun μ => ∫⁻ a, g a ∂μ, measurable_lintegral hgm,
    (ae_ae_of_ae_join hfg).mono fun _ => lintegral_congr_ae⟩

@[simp]

Depends on / 依赖: ae_ae_of_ae_join, lintegral_congr_ae, measurable_lintegral
-/
theorem aemeasurable_lintegral {m : Measure (Measure α)} {f : α -> Real>=0∞}
    (h : AEMeasurable f m.join) : AEMeasurable (fun μ => ∫⁻ a, f a ∂μ) m :=
  let ⟨g, hgm, hfg⟩ := h
  ⟨fun μ => ∫⁻ a, g a ∂μ, measurable_lintegral hgm,
    (ae_ae_of_ae_join hfg).mono fun _ => lintegral_congr_ae⟩

@[simp]
/--
theorem `join_zero` / 定理 `join_zero`

English:
theorem join_zero
  statement: (0 : Measure (Measure α)).join = 0
  proof: by
  ext1 s hs
  simp [hs]

@[fun_prop]

中文:
定理 join_zero
  结论: (0 : Measure (Measure α)).join = 0
  证明: by
  ext1 s hs
  simp [hs]

@[fun_prop]
-/
theorem join_zero : (0 : Measure (Measure α)).join = 0 := by
  ext1 s hs
  simp [hs]

@[fun_prop]
/--
theorem `measurable_join` / 定理 `measurable_join`

English:
theorem measurable_join
  statement: Measurable (join : Measure (Measure α) -> Measure α)
  proof: measurable_of_measurable_coe _ fun s hs => by
    simp only [join_apply hs, measurable_lintegral (measurable_coe hs)]

中文:
定理 measurable_join
  结论: Measurable (join : Measure (Measure α) -> Measure α)
  证明: measurable_of_measurable_coe _ fun s hs => by
    simp only [join_apply hs, measurable_lintegral (measurable_coe hs)]

Depends on / 依赖: join_apply, measurable_coe, measurable_lintegral, measurable_of_measurable_coe, right_iff_left_not_left_of
-/
theorem measurable_join : Measurable (join : Measure (Measure α) -> Measure α) :=
  measurable_of_measurable_coe _ fun s hs => by
    simp only [join_apply hs, measurable_lintegral (measurable_coe hs)]

/--
theorem `lintegral_join` / 定理 `lintegral_join`

English:
theorem lintegral_join
  given: {m : Measure (Measure α)} {f : α -> Real>=0∞} (hf : AEMeasurable f (join m))
  proof: by
  wlog hfm : Measurable f generalizing f
  · rcases hf with ⟨g, hgm, hfg⟩
    rw [lintegral_congr_ae hfg]; rw [this hgm.aemeasurable hgm]
exact lintegral_congr_ae (ae_ae_of_ae_join hfg).mono fun μ hμ =>
.symm lintegral_congr_ae hμ
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hfm, SimpleFunc.lin

中文:
定理 lintegral_join
  条件: {m : Measure (Measure α)} {f : α -> 实数>=0∞} (hf : AEMeasurable f (join m))
  证明: by
  wlog hfm : Measurable f generalizing f
  · rcases hf with ⟨g, hgm, hfg⟩
    rw [lintegral_congr_ae hfg]; rw [this hgm.aemeasurable hgm]
exact lintegral_congr_ae (ae_ae_of_ae_join hfg).mono fun μ hμ =>
.symm lintegral_congr_ae hμ
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hfm, SimpleFunc.lin

Depends on / 依赖: Finset, Measurable, Measure, Monotone, SimpleFunc, SimpleFunc.lintegral, SimpleFunc.measurableSet_preimage, ae_ae_of_ae_join, aemeasurable, generalizing, hgm.aemeasurable, join_apply, lintegral, lintegral_congr_ae, lintegral_eq_iSup_eapprox_lintegral, measurableSet_preimage, simp_rw
-/
theorem lintegral_join {m : Measure (Measure α)} {f : α -> Real>=0∞} (hf : AEMeasurable f (join m)) :
    ∫⁻ x, f x ∂join m = ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m := by
  wlog hfm : Measurable f generalizing f
  · rcases hf with ⟨g, hgm, hfg⟩
    rw [lintegral_congr_ae hfg]; rw [this hgm.aemeasurable hgm]
exact lintegral_congr_ae (ae_ae_of_ae_join hfg).mono fun μ hμ =>
.symm lintegral_congr_ae hμ
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hfm, SimpleFunc.lintegral,
    join_apply (SimpleFunc.measurableSet_preimage _ _)]
  clear hf
  suffices
    forall (s : Nat -> Finset Real>=0∞) (f : Nat -> Real>=0∞ -> Measure α -> Real>=0∞), (forall n r, Measurable (f n r)) ->
      Monotone (fun n μ => ∑ r in s n, r * f n r μ) ->
      ⨆ n, ∑ r in s n, r * ∫⁻ μ, f n r μ ∂m = ∫⁻ μ, ⨆ n, ∑ r in s n, r * f n r μ ∂m by
    refine
      this (fun n => SimpleFunc.range (SimpleFunc.eapprox f n))
        (fun n r μ => μ (SimpleFunc.eapprox f n ⁻¹' {r})) ?_ ?_
    · exact fun n r => measurable_coe (SimpleFunc.measurableSet_preimage _ _)
    · exact fun n m h μ => SimpleFunc.lintegral_mono (SimpleFunc.monotone_eapprox _ h) le_rfl
  intro s f hf hm
  rw [lintegral_iSup _ hm]
  swap
  · fun_prop
  congr
  funext n
  rw [lintegral_finsetSum (s n)]
  · simp_rw [lintegral_const_mul _ (hf _ _)]
  · exact fun r _ => (hf _ _).const_mul _

/--
theorem `lintegral_join_le` / 定理 `lintegral_join_le`

English:
theorem lintegral_join_le
  given: (f : α -> Real>=0∞) (m : Measure (Measure α))
  proof: by
  rcases exists_measurable_le_lintegral_eq (join m) f with ⟨g, hgm, hgf, hfg_int⟩
  rw [hfg_int]; rw [lintegral_join hgm.aemeasurable]
  gcongr
  apply hgf

中文:
定理 lintegral_join_le
  条件: (f : α -> 实数>=0∞) (m : Measure (Measure α))
  证明: by
  rcases exists_measurable_le_lintegral_eq (join m) f with ⟨g, hgm, hgf, hfg_int⟩
  rw [hfg_int]; rw [lintegral_join hgm.aemeasurable]
  gcongr
  apply hgf

Depends on / 依赖: aemeasurable, exists_measurable_le_lintegral_eq, hfg_int, hgm.aemeasurable, lintegral_join
-/
theorem lintegral_join_le (f : α -> Real>=0∞) (m : Measure (Measure α)) :
    ∫⁻ x, f x ∂join m <= ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m := by
  rcases exists_measurable_le_lintegral_eq (join m) f with ⟨g, hgm, hgf, hfg_int⟩
  rw [hfg_int]; rw [lintegral_join hgm.aemeasurable]
  gcongr
  apply hgf

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (m : Measure α) (f : α -> Measure β)
  body: join (map f m)

@[simp]

中文:
定义 bind
  签名: (m : Measure α) (f : α -> Measure β)
  定义体: join (map f m)

@[simp]
-/
def bind (m : Measure α) (f : α -> Measure β) : Measure β :=
  join (map f m)

@[simp]
/--
theorem `bind_zero_left` / 定理 `bind_zero_left`

English:
theorem bind_zero_left
  given: (f : α -> Measure β)
  statement: bind (0 : Measure α) f = 0
  proof: by simp [bind]

@[simp]

中文:
定理 bind_zero_left
  条件: (f : α -> Measure β)
  结论: bind (0 : Measure α) f = 0
  证明: by simp [bind]

@[simp]
-/
theorem bind_zero_left (f : α -> Measure β) : bind (0 : Measure α) f = 0 := by simp [bind]

@[simp]
/--
theorem `bind_apply` / 定理 `bind_apply`

English:
theorem bind_apply
  statement: {m : Measure α} {f : α -> Measure β} {s : Set β} (hs : MeasurableSet s)
  proof: by
  rw [bind]; rw [join_apply hs]; rw [lintegral_map' (measurable_coe hs).aemeasurable hf]

中文:
定理 bind_apply
  结论: {m : Measure α} {f : α -> Measure β} {s : Set β} (hs : MeasurableSet s)
  证明: by
  rw [bind]; rw [join_apply hs]; rw [lintegral_map' (measurable_coe hs).aemeasurable hf]

Depends on / 依赖: aemeasurable, join_apply, lintegral_map, measurable_coe
-/
theorem bind_apply {m : Measure α} {f : α -> Measure β} {s : Set β} (hs : MeasurableSet s)
    (hf : AEMeasurable f m) : bind m f s = ∫⁻ a, f a s ∂m := by
  rw [bind]; rw [join_apply hs]; rw [lintegral_map' (measurable_coe hs).aemeasurable hf]

/--
theorem `bind_apply_le` / 定理 `bind_apply_le`

English:
theorem bind_apply_le
  given: {m : Measure α} (f : α -> Measure β) {s : Set β} (hs : MeasurableSet s)
  proof: by
  rw [bind]; rw [join_apply hs]
  apply lintegral_map_le

中文:
定理 bind_apply_le
  条件: {m : Measure α} (f : α -> Measure β) {s : Set β} (hs : MeasurableSet s)
  证明: by
  rw [bind]; rw [join_apply hs]
  apply lintegral_map_le

Depends on / 依赖: join_apply, lintegral_map_le
-/
theorem bind_apply_le {m : Measure α} (f : α -> Measure β) {s : Set β} (hs : MeasurableSet s) :
    bind m f s <= ∫⁻ a, f a s ∂m := by
  rw [bind]; rw [join_apply hs]
  apply lintegral_map_le

/--
theorem `ae_ae_of_ae_bind` / 定理 `ae_ae_of_ae_bind`

English:
theorem ae_ae_of_ae_bind
  statement: {m : Measure α} {f : α -> Measure β} {p : β -> Prop} (hf : AEMeasurable f m)
  proof: ae_of_ae_map hf ae_ae_of_ae_join h

中文:
定理 ae_ae_of_ae_bind
  结论: {m : Measure α} {f : α -> Measure β} {p : β -> 命题} (hf : AEMeasurable f m)
  证明: ae_of_ae_map hf ae_ae_of_ae_join h

Depends on / 依赖: ae_ae_of_ae_join, ae_of_ae_map
-/
theorem ae_ae_of_ae_bind {m : Measure α} {f : α -> Measure β} {p : β -> Prop} (hf : AEMeasurable f m)
    (h : forallᵐ b ∂m.bind f, p b) : forallᵐ a ∂m, forallᵐ b ∂f a, p b :=
ae_of_ae_map hf ae_ae_of_ae_join h

/--
theorem `_root_.AEMeasurable.ae_of_bind` / 定理 `_root_.AEMeasurable.ae_of_bind`

English:
theorem _root_.AEMeasurable.ae_of_bind
  statement: {γ : Type*} {_ : MeasurableSpace γ} {m : Measure α}
  proof: ae_of_ae_map hf hg.ae_of_join

中文:
定理 _root_.AEMeasurable.ae_of_bind
  结论: {γ : 类型} {_ : MeasurableSpace γ} {m : Measure α}
  证明: ae_of_ae_map hf hg.ae_of_join

Depends on / 依赖: ae_of_ae_map, ae_of_join, hg.ae_of_join
-/
theorem _root_.AEMeasurable.ae_of_bind {γ : Type*} {_ : MeasurableSpace γ} {m : Measure α}
    {f : α -> Measure β} {g : β -> γ} (hf : AEMeasurable f m) (hg : AEMeasurable g (m.bind f)) :
    forallᵐ a ∂m, AEMeasurable g (f a) :=
  ae_of_ae_map hf hg.ae_of_join

/--
theorem `bind_congr_right` / 定理 `bind_congr_right`

English:
theorem bind_congr_right
  given: {μ : Measure α} {f g : α -> Measure β} (h : f =ᵐ[μ] g)
  proof: congrArg join map_congr h

@[simp]

中文:
定理 bind_congr_right
  条件: {μ : Measure α} {f g : α -> Measure β} (h : f =ᵐ[μ] g)
  证明: congrArg join map_congr h

@[simp]

Depends on / 依赖: map_congr
-/
theorem bind_congr_right {μ : Measure α} {f g : α -> Measure β} (h : f =ᵐ[μ] g) :
    μ.bind f = μ.bind g :=
congrArg join map_congr h

@[simp]
/--
lemma `bind_const` / 引理 `bind_const`

English:
lemma bind_const
  given: {m : Measure α} {ν : Measure β}
  statement: m.bind (fun _ => ν) = m Set.univ • ν
  proof: by
  simp [bind]

中文:
引理 bind_const
  条件: {m : Measure α} {ν : Measure β}
  结论: m.bind (fun _ => ν) = m Set.univ • ν
  证明: by
  simp [bind]
-/
lemma bind_const {m : Measure α} {ν : Measure β} : m.bind (fun _ => ν) = m Set.univ • ν := by
  simp [bind]

/--
theorem `bind_zero_right'` / 定理 `bind_zero_right'`

English:
theorem bind_zero_right'
  given: (m : Measure α)
  statement: bind m (fun _ => 0 : α -> Measure β) = 0
  proof: by simp

@[simp]

中文:
定理 bind_zero_right'
  条件: (m : Measure α)
  结论: bind m (fun _ => 0 : α -> Measure β) = 0
  证明: by simp

@[simp]
-/
theorem bind_zero_right' (m : Measure α) : bind m (fun _ => 0 : α -> Measure β) = 0 := by simp

@[simp]
/--
theorem `bind_zero_right` / 定理 `bind_zero_right`

English:
theorem bind_zero_right
  given: (m : Measure α)
  statement: bind m (0 : α -> Measure β) = 0
  proof: bind_zero_right' m

@[fun_prop]

中文:
定理 bind_zero_right
  条件: (m : Measure α)
  结论: bind m (0 : α -> Measure β) = 0
  证明: bind_zero_right' m

@[fun_prop]

Depends on / 依赖: bind_zero_right
-/
theorem bind_zero_right (m : Measure α) : bind m (0 : α -> Measure β) = 0 := bind_zero_right' m

@[fun_prop]
/--
theorem `measurable_bind'` / 定理 `measurable_bind'`

English:
theorem measurable_bind'
  given: {g : α -> Measure β} (hg : Measurable g)
  proof: measurable_join.comp (measurable_map _ hg)

中文:
定理 measurable_bind'
  条件: {g : α -> Measure β} (hg : Measurable g)
  证明: measurable_join.comp (measurable_map _ hg)

Depends on / 依赖: measurable_join, measurable_join.comp, measurable_map
-/
theorem measurable_bind' {g : α -> Measure β} (hg : Measurable g) :
    Measurable fun m : Measure α => bind m g :=
  measurable_join.comp (measurable_map _ hg)

/--
theorem `aemeasurable_bind` / 定理 `aemeasurable_bind`

English:
theorem aemeasurable_bind
  statement: {g : α -> Measure β} {m : Measure (Measure α)}
  proof: let ⟨f, hfm, hf⟩ := hg
  ⟨(bind · f), measurable_bind' hfm, (ae_ae_of_ae_join hf).mono fun _ => bind_congr_right⟩

中文:
定理 aemeasurable_bind
  结论: {g : α -> Measure β} {m : Measure (Measure α)}
  证明: let ⟨f, hfm, hf⟩ := hg
  ⟨(bind · f), measurable_bind' hfm, (ae_ae_of_ae_join hf).mono fun _ => bind_congr_right⟩

Depends on / 依赖: ae_ae_of_ae_join, bind_congr_right, measurable_bind
-/
theorem aemeasurable_bind {g : α -> Measure β} {m : Measure (Measure α)}
    (hg : AEMeasurable g m.join) : AEMeasurable (bind · g) m :=
  let ⟨f, hfm, hf⟩ := hg
  ⟨(bind · f), measurable_bind' hfm, (ae_ae_of_ae_join hf).mono fun _ => bind_congr_right⟩

/--
theorem `bind_sum` / 定理 `bind_sum`

English:
theorem bind_sum
  statement: {ι : Type*} (m : ι -> Measure α) (f : α -> Measure β)
  proof: by
  simp_rw [bind, map_sum h, join_sum]

中文:
定理 bind_sum
  结论: {ι : 类型} (m : ι -> Measure α) (f : α -> Measure β)
  证明: by
  simp_rw [bind, map_sum h, join_sum]

Depends on / 依赖: join_sum, map_sum, simp_rw
-/
theorem bind_sum {ι : Type*} (m : ι -> Measure α) (f : α -> Measure β)
    (h : AEMeasurable f (sum fun i => m i)) :
    (sum fun (i : ι) => m i).bind f = sum fun (i : ι) => (m i).bind f := by
  simp_rw [bind, map_sum h, join_sum]

/--
lemma `bind_smul` / 引理 `bind_smul`

English:
lemma bind_smul
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (m : Measure α)
  proof: by
  simp_rw [bind, Measure.map_smul, join_smul]

中文:
引理 bind_smul
  结论: {R : 类型} [SMul R 实数>=0∞] [IsScalarTower R 实数>=0∞ 实数>=0∞] (c : R) (m : Measure α)
  证明: by
  simp_rw [bind, Measure.map_smul, join_smul]

Depends on / 依赖: Measure, Measure.map_smul, join_smul, map_smul, simp_rw
-/
lemma bind_smul {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (m : Measure α)
    (f : α -> Measure β) : (c • m).bind f = c • (m.bind f) := by
  simp_rw [bind, Measure.map_smul, join_smul]

/--
theorem `lintegral_bind` / 定理 `lintegral_bind`

English:
theorem lintegral_bind
  statement: {m : Measure α} {μ : α -> Measure β} {f : β -> Real>=0∞} (hμ : AEMeasurable μ m)
  proof: (lintegral_join hf).trans (lintegral_map' (aemeasurable_lintegral hf) hμ)

中文:
定理 lintegral_bind
  结论: {m : Measure α} {μ : α -> Measure β} {f : β -> 实数>=0∞} (hμ : AEMeasurable μ m)
  证明: (lintegral_join hf).trans (lintegral_map' (aemeasurable_lintegral hf) hμ)

Depends on / 依赖: LinearOrder, WellFoundedLT, aemeasurable_lintegral, isWellOrder_lt, lintegral_join, lintegral_map
-/
theorem lintegral_bind {m : Measure α} {μ : α -> Measure β} {f : β -> Real>=0∞} (hμ : AEMeasurable μ m)
    (hf : AEMeasurable f (bind m μ)) : ∫⁻ x, f x ∂bind m μ = ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  (lintegral_join hf).trans (lintegral_map' (aemeasurable_lintegral hf) hμ)

/--
theorem `lintegral_bind_le` / 定理 `lintegral_bind_le`

English:
theorem lintegral_bind_le
  given: (f : β -> Real>=0∞) (m : Measure α) (μ : α -> Measure β)
  proof: (lintegral_join_le _ _).trans (lintegral_map_le _ _)

中文:
定理 lintegral_bind_le
  条件: (f : β -> 实数>=0∞) (m : Measure α) (μ : α -> Measure β)
  证明: (lintegral_join_le _ _).trans (lintegral_map_le _ _)

Depends on / 依赖: lintegral_join_le, lintegral_map_le
-/
theorem lintegral_bind_le (f : β -> Real>=0∞) (m : Measure α) (μ : α -> Measure β) :
    ∫⁻ x, f x ∂bind m μ <= ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  (lintegral_join_le _ _).trans (lintegral_map_le _ _)

/--
theorem `bind_bind` / 定理 `bind_bind`

English:
theorem bind_bind
  statement: {γ} [MeasurableSpace γ] {m : Measure α} {f : α -> Measure β} {g : β -> Measure γ}
  proof: by
  ext1 s hs
  rw [bind_apply hs hg]; rw [lintegral_bind hf]; rw [bind_apply hs]
· exact lintegral_congr_ae (hf.ae_of_bind hg).mono fun a ha => .symm bind_apply hs ha
  · exact (aemeasurable_bind hg).comp_aemeasurable hf
  · exact (measurable_coe hs).comp_aemeasurable hg

@[simp]

中文:
定理 bind_bind
  结论: {γ} [MeasurableSpace γ] {m : Measure α} {f : α -> Measure β} {g : β -> Measure γ}
  证明: by
  ext1 s hs
  rw [bind_apply hs hg]; rw [lintegral_bind hf]; rw [bind_apply hs]
· exact lintegral_congr_ae (hf.ae_of_bind hg).mono fun a ha => .symm bind_apply hs ha
  · exact (aemeasurable_bind hg).comp_aemeasurable hf
  · exact (measurable_coe hs).comp_aemeasurable hg

@[simp]

Depends on / 依赖: ae_of_bind, aemeasurable_bind, bind_apply, comp_aemeasurable, hf.ae_of_bind, lintegral_bind, lintegral_congr_ae, measurable_coe
-/
theorem bind_bind {γ} [MeasurableSpace γ] {m : Measure α} {f : α -> Measure β} {g : β -> Measure γ}
    (hf : AEMeasurable f m) (hg : AEMeasurable g (m.bind f)) :
    bind (bind m f) g = bind m fun a => bind (f a) g := by
  ext1 s hs
  rw [bind_apply hs hg]; rw [lintegral_bind hf]; rw [bind_apply hs]
· exact lintegral_congr_ae (hf.ae_of_bind hg).mono fun a ha => .symm bind_apply hs ha
  · exact (aemeasurable_bind hg).comp_aemeasurable hf
  · exact (measurable_coe hs).comp_aemeasurable hg

@[simp]
/--
theorem `dirac_bind` / 定理 `dirac_bind`

English:
theorem dirac_bind
  given: {f : α -> Measure β} (hf : Measurable f) (a : α)
  statement: bind (dirac a) f = f a
  proof: by
  simp [bind, map_dirac' hf]

@[simp]

中文:
定理 dirac_bind
  条件: {f : α -> Measure β} (hf : Measurable f) (a : α)
  结论: bind (dirac a) f = f a
  证明: by
  simp [bind, map_dirac' hf]

@[simp]

Depends on / 依赖: map_dirac
-/
theorem dirac_bind {f : α -> Measure β} (hf : Measurable f) (a : α) : bind (dirac a) f = f a := by
  simp [bind, map_dirac' hf]

@[simp]
/--
theorem `bind_dirac` / 定理 `bind_dirac`

English:
theorem bind_dirac
  given: {m : Measure α}
  statement: bind m dirac = m
  proof: by
  ext1 s hs
  simp only [bind_apply hs measurable_dirac.aemeasurable, dirac_apply' _ hs, lintegral_indicator hs,
    Pi.one_apply, lintegral_one, restrict_apply, MeasurableSet.univ, univ_inter]

@[simp]

中文:
定理 bind_dirac
  条件: {m : Measure α}
  结论: bind m dirac = m
  证明: by
  ext1 s hs
  simp only [bind_apply hs measurable_dirac.aemeasurable, dirac_apply' _ hs, lintegral_indicator hs,
    Pi.one_apply, lintegral_one, restrict_apply, MeasurableSet.univ, univ_inter]

@[simp]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Pi.one_apply, aemeasurable, bind_apply, dirac_apply, lintegral_indicator, lintegral_one, measurable_dirac, measurable_dirac.aemeasurable, one_apply, restrict_apply, univ_inter
-/
theorem bind_dirac {m : Measure α} : bind m dirac = m := by
  ext1 s hs
  simp only [bind_apply hs measurable_dirac.aemeasurable, dirac_apply' _ hs, lintegral_indicator hs,
    Pi.one_apply, lintegral_one, restrict_apply, MeasurableSet.univ, univ_inter]

@[simp]
/--
lemma `bind_dirac_eq_map` / 引理 `bind_dirac_eq_map`

English:
lemma bind_dirac_eq_map
  given: (m : Measure α) {f : α -> β} (hf : Measurable f)
  proof: by
  rw [← bind_dirac (m := m.map f)]; rw [bind]; rw [bind]; rw [map_map]; rw [Function.comp_def]
  exacts [measurable_dirac, hf]

中文:
引理 bind_dirac_eq_map
  条件: (m : Measure α) {f : α -> β} (hf : Measurable f)
  证明: by
  rw [← bind_dirac (m := m.map f)]; rw [bind]; rw [bind]; rw [map_map]; rw [Function.comp_def]
  exacts [measurable_dirac, hf]

Depends on / 依赖: Function, Function.comp_def, bind_dirac, comp_def, exacts, m.map, map_map, measurable_dirac
-/
lemma bind_dirac_eq_map (m : Measure α) {f : α -> β} (hf : Measurable f) :
    m.bind (fun x => Measure.dirac (f x)) = m.map f := by
  rw [← bind_dirac (m := m.map f)]; rw [bind]; rw [bind]; rw [map_map]; rw [Function.comp_def]
  exacts [measurable_dirac, hf]

/--
theorem `join_eq_bind` / 定理 `join_eq_bind`

English:
theorem join_eq_bind
  given: (μ : Measure (Measure α))
  statement: join μ = bind μ id
  proof: by rw [bind, map_id]

中文:
定理 join_eq_bind
  条件: (μ : Measure (Measure α))
  结论: join μ = bind μ id
  证明: by rw [bind, map_id]

Depends on / 依赖: map_id
-/
theorem join_eq_bind (μ : Measure (Measure α)) : join μ = bind μ id := by rw [bind, map_id]

/--
theorem `join_map_map` / 定理 `join_map_map`

English:
theorem join_map_map
  given: {f : α -> β} (hf : Measurable f) (μ : Measure (Measure α))
  proof: by
  ext1 s hs
  rw [join_apply hs]; rw [map_apply hf hs]; rw [join_apply (hf hs)]; rw [lintegral_map (measurable_coe hs) (measurable_map f hf)]
  simp_rw [map_apply hf hs]

中文:
定理 join_map_map
  条件: {f : α -> β} (hf : Measurable f) (μ : Measure (Measure α))
  证明: by
  ext1 s hs
  rw [join_apply hs]; rw [map_apply hf hs]; rw [join_apply (hf hs)]; rw [lintegral_map (measurable_coe hs) (measurable_map f hf)]
  simp_rw [map_apply hf hs]

Depends on / 依赖: join_apply, lintegral_map, map_apply, measurable_coe, measurable_map, simp_rw
-/
theorem join_map_map {f : α -> β} (hf : Measurable f) (μ : Measure (Measure α)) :
    join (map (map f) μ) = map f (join μ) := by
  ext1 s hs
  rw [join_apply hs]; rw [map_apply hf hs]; rw [join_apply (hf hs)]; rw [lintegral_map (measurable_coe hs) (measurable_map f hf)]
  simp_rw [map_apply hf hs]

/--
theorem `join_map_join` / 定理 `join_map_join`

English:
theorem join_map_join
  given: (μ : Measure (Measure (Measure α)))
  statement: join (map join μ) = join (join μ)
  proof: by
  change bind μ join = join (join μ)
  rw [join_eq_bind]; rw [join_eq_bind]; rw [bind_bind aemeasurable_id aemeasurable_id]
  apply congr_arg (bind μ)
  funext ν
  exact join_eq_bind ν

中文:
定理 join_map_join
  条件: (μ : Measure (Measure (Measure α)))
  结论: join (map join μ) = join (join μ)
  证明: by
  change bind μ join = join (join μ)
  rw [join_eq_bind]; rw [join_eq_bind]; rw [bind_bind aemeasurable_id aemeasurable_id]
  apply congr_arg (bind μ)
  funext ν
  exact join_eq_bind ν

Depends on / 依赖: aemeasurable_id, bind_bind, congr_arg, join_eq_bind
-/
theorem join_map_join (μ : Measure (Measure (Measure α))) : join (map join μ) = join (join μ) := by
  change bind μ join = join (join μ)
  rw [join_eq_bind]; rw [join_eq_bind]; rw [bind_bind aemeasurable_id aemeasurable_id]
  apply congr_arg (bind μ)
  funext ν
  exact join_eq_bind ν

/--
theorem `join_map_dirac` / 定理 `join_map_dirac`

English:
theorem join_map_dirac
  given: (μ : Measure α)
  statement: join (map dirac μ) = μ
  proof: bind_dirac

中文:
定理 join_map_dirac
  条件: (μ : Measure α)
  结论: join (map dirac μ) = μ
  证明: bind_dirac

Depends on / 依赖: bind_dirac
-/
theorem join_map_dirac (μ : Measure α) : join (map dirac μ) = μ := bind_dirac

end Measure

end MeasureTheory
