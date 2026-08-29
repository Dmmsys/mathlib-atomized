/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Quasi-Measure-Preserving Functions

A map `f : α → β` is said to be *quasi-measure-preserving* (a.k.a. non-singular) w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`.
That last condition can also be written `μa.map f ≪ μb` (the map of `μa` by `f` is
absolutely continuous with respect to `μb`).

## Main definitions

* `MeasureTheory.Measure.QuasiMeasurePreserving f μa μb`: `f` is quasi-measure-preserving with
  respect to `μa` and `μb`.

-/

public section

variable {α β γ δ : Type*}

namespace MeasureTheory

open Set Function ENNReal
open Filter hiding map

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {s : Set α}

namespace Measure

/-- A map `f : α → β` is said to be *quasi-measure-preserving* (a.k.a. non-singular) w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`. -/
@[fun_prop]
/--
Definition of `QuasiMeasurePreserving` / `QuasiMeasurePreserving` 的定义

English:
structure QuasiMeasurePreserving
  parameters: {m0 : MeasurableSpace α} (f : α -> β)
  axioms and operations (2):
    - measurable : Measurable f
    - absolutelyContinuous : μa.map f ≪ μb

中文:
结构 拟保测
  参数: {m0 : 可测空间 α} (f : α -> β)
  公理与运算 (2 个):
    - measurable : 可测 f
    - absolutelyContinuous : μa.map f ≪ μb

Depends on / 依赖: Measurable, Measure, a.map, absolutelyContinuous, measurable, protected, volume_tac
-/
structure QuasiMeasurePreserving {m0 : MeasurableSpace α} (f : α -> β)
  (μa : Measure α := by volume_tac)
  (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected absolutelyContinuous : μa.map f ≪ μb

attribute [fun_prop] QuasiMeasurePreserving.measurable

namespace QuasiMeasurePreserving

@[fun_prop]
/--
theorem `id` / 定理 `id`

English:
theorem id
  given: {_m0 : MeasurableSpace α} (μ : Measure α)
  statement: QuasiMeasurePreserving id μ μ
  proof: ⟨measurable_id, map_id.absolutelyContinuous⟩

中文:
定理 id
  条件: {_m0 : 可测空间 α} (μ : 测度 α)
  结论: 拟保测 id μ μ
  证明: ⟨measurable_id, map_id.absolutelyContinuous⟩
-/
protected theorem id {_m0 : MeasurableSpace α} (μ : Measure α) : QuasiMeasurePreserving id μ μ :=
  ⟨measurable_id, map_id.absolutelyContinuous⟩

variable {μa μa' : Measure α} {μb μb' : Measure β} {μc : Measure γ} {f : α -> β}

/--
theorem `_root_.Measurable.quasiMeasurePreserving` / 定理 `_root_.Measurable.quasiMeasurePreserving`

English:
theorem _root_.Measurable.quasiMeasurePreserving
  proof: ⟨hf, AbsolutelyContinuous.rfl⟩

中文:
定理 _root_.可测.quasiMeasurePreserving
  证明: ⟨hf, AbsolutelyContinuous.rfl⟩
-/
protected theorem _root_.Measurable.quasiMeasurePreserving
    {_m0 : MeasurableSpace α} (hf : Measurable f) (μ : Measure α) :
    QuasiMeasurePreserving f μ (μ.map f) :=
  ⟨hf, AbsolutelyContinuous.rfl⟩

/--
theorem `mono_left` / 定理 `mono_left`

English:
theorem mono_left
  given: (h : QuasiMeasurePreserving f μa μb) (ha : μa' ≪ μa)
  proof: ⟨h.1, (ha.map h.1).trans h.2⟩

中文:
定理 mono_left
  条件: (h : 拟保测 f μa μb) (ha : μa' ≪ μa)
  证明: ⟨h.1, (ha.map h.1).trans h.2⟩

Depends on / 依赖: ha.map
-/
theorem mono_left (h : QuasiMeasurePreserving f μa μb) (ha : μa' ≪ μa) :
    QuasiMeasurePreserving f μa' μb :=
  ⟨h.1, (ha.map h.1).trans h.2⟩

/--
theorem `mono_right` / 定理 `mono_right`

English:
theorem mono_right
  given: (h : QuasiMeasurePreserving f μa μb) (ha : μb ≪ μb')
  proof: ⟨h.1, h.2.trans ha⟩

@[gcongr, mono]

中文:
定理 mono_right
  条件: (h : 拟保测 f μa μb) (ha : μb ≪ μb')
  证明: ⟨h.1, h.2.trans ha⟩

@[gcongr, mono]
-/
theorem mono_right (h : QuasiMeasurePreserving f μa μb) (ha : μb ≪ μb') :
    QuasiMeasurePreserving f μa μb' :=
  ⟨h.1, h.2.trans ha⟩

@[gcongr, mono]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb)
  proof: (h.mono_left ha).mono_right hb

@[fun_prop]

中文:
定理 mono
  条件: (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : 拟保测 f μa μb)
  证明: (h.mono_left ha).mono_right hb

@[fun_prop]

Depends on / 依赖: h.mono_left, mono_left, mono_right
-/
theorem mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa' μb' :=
  (h.mono_left ha).mono_right hb

@[fun_prop]
/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {g : β -> γ} {f : α -> β} (hg : QuasiMeasurePreserving g μb μc)
  proof: ⟨hg.measurable.comp hf.measurable, by
    rw [← map_map hg.1 hf.1]
    exact (hf.2.map hg.1).trans hg.2⟩

中文:
定理 comp
  结论: {g : β -> γ} {f : α -> β} (hg : 拟保测 g μb μc)
  证明: ⟨hg.measurable.comp hf.measurable, by
    rw [← map_map hg.1 hf.1]
    exact (hf.2.map hg.1).trans hg.2⟩
-/
protected theorem comp {g : β -> γ} {f : α -> β} (hg : QuasiMeasurePreserving g μb μc)
    (hf : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.measurable.comp hf.measurable, by
    rw [← map_map hg.1 hf.1]
    exact (hf.2.map hg.1).trans hg.2⟩

/--
theorem `iterate` / 定理 `iterate`

English:
theorem iterate
  given: {f : α -> α} (hf : QuasiMeasurePreserving f μa μa)

中文:
定理 iterate
  条件: {f : α -> α} (hf : 拟保测 f μa μa)
-/
protected theorem iterate {f : α -> α} (hf : QuasiMeasurePreserving f μa μa) :
    forall n, QuasiMeasurePreserving f^[n] μa μa
  | 0 => QuasiMeasurePreserving.id μa
  | n + 1 => (hf.iterate n).comp hf

/--
theorem `aemeasurable` / 定理 `aemeasurable`

English:
theorem aemeasurable
  given: (hf : QuasiMeasurePreserving f μa μb)
  statement: AEMeasurable f μa
  proof: hf.1.aemeasurable

中文:
定理 aemeasurable
  条件: (hf : 拟保测 f μa μb)
  结论: 几乎处处可测 f μa
  证明: hf.1.aemeasurable
-/
protected theorem aemeasurable (hf : QuasiMeasurePreserving f μa μb) : AEMeasurable f μa :=
  hf.1.aemeasurable

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  statement: (hf : QuasiMeasurePreserving f μa μb) {f' : α -> β} (hf' : Measurable f')
  proof: by
  refine ⟨hf', ?_⟩
  rw [Measure.map_congr h.symm]
  exact hf.absolutelyContinuous

中文:
定理 congr
  结论: (hf : 拟保测 f μa μb) {f' : α -> β} (hf' : 可测 f')
  证明: by
  refine ⟨hf', ?_⟩
  rw [Measure.map_congr h.symm]
  exact hf.absolutelyContinuous
-/
protected theorem congr (hf : QuasiMeasurePreserving f μa μb) {f' : α -> β} (hf' : Measurable f')
    (h : f =ᵐ[μa] f') : QuasiMeasurePreserving f' μa μb := by
  refine ⟨hf', ?_⟩
  rw [Measure.map_congr h.symm]
  exact hf.absolutelyContinuous

/--
theorem `smul_measure` / 定理 `smul_measure`

English:
theorem smul_measure
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: ⟨hf.1, by rw [Measure.map_smul]; exact hf.2.smul c⟩

中文:
定理 smul_measure
  结论: {R : 类型} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  证明: ⟨hf.1, by rw [Measure.map_smul]; exact hf.2.smul c⟩

Depends on / 依赖: Measure, Measure.map_smul, map_smul
-/
theorem smul_measure {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (hf : QuasiMeasurePreserving f μa μb) (c : R) : QuasiMeasurePreserving f (c • μa) (c • μb) :=
  ⟨hf.1, by rw [Measure.map_smul]; exact hf.2.smul c⟩

/--
theorem `ae_map_le` / 定理 `ae_map_le`

English:
theorem ae_map_le
  given: (h : QuasiMeasurePreserving f μa μb)
  statement: ae (μa.map f) <= ae μb
  proof: h.2.ae_le

中文:
定理 ae_map_le
  条件: (h : 拟保测 f μa μb)
  结论: ae (μa.map f) <= ae μb
  证明: h.2.ae_le

Depends on / 依赖: ae_le
-/
theorem ae_map_le (h : QuasiMeasurePreserving f μa μb) : ae (μa.map f) <= ae μb :=
  h.2.ae_le

/--
theorem `tendsto_ae` / 定理 `tendsto_ae`

English:
theorem tendsto_ae
  given: (h : QuasiMeasurePreserving f μa μb)
  statement: Tendsto f (ae μa) (ae μb)
  proof: (tendsto_ae_map h.aemeasurable).mono_right h.ae_map_le

中文:
定理 tendsto_ae
  条件: (h : 拟保测 f μa μb)
  结论: 收敛 f (ae μa) (ae μb)
  证明: (tendsto_ae_map h.aemeasurable).mono_right h.ae_map_le

Depends on / 依赖: ae_map_le, aemeasurable, h.ae_map_le, h.aemeasurable, mono_right, tendsto_ae_map
-/
theorem tendsto_ae (h : QuasiMeasurePreserving f μa μb) : Tendsto f (ae μa) (ae μb) :=
  (tendsto_ae_map h.aemeasurable).mono_right h.ae_map_le

/--
theorem `ae` / 定理 `ae`

English:
theorem ae
  given: (h : QuasiMeasurePreserving f μa μb) {p : β -> Prop} (hg : forallᵐ x ∂μb, p x)
  proof: h.tendsto_ae hg

@[gcongr]

中文:
定理 ae
  条件: (h : 拟保测 f μa μb) {p : β -> 命题} (hg : 对任意ᵐ x ∂μb, p x)
  证明: h.tendsto_ae hg

@[gcongr]

Depends on / 依赖: h.tendsto_ae, tendsto_ae
-/
theorem ae (h : QuasiMeasurePreserving f μa μb) {p : β -> Prop} (hg : forallᵐ x ∂μb, p x) :
    forallᵐ x ∂μa, p (f x) :=
  h.tendsto_ae hg

@[gcongr]
/--
theorem `ae_eq` / 定理 `ae_eq`

English:
theorem ae_eq
  given: (h : QuasiMeasurePreserving f μa μb) {g₁ g₂ : β -> δ} (hg : g₁ =ᵐ[μb] g₂)
  proof: h.ae hg

中文:
定理 ae_eq
  条件: (h : 拟保测 f μa μb) {g₁ g₂ : β -> δ} (hg : g₁ =ᵐ[μb] g₂)
  证明: h.ae hg

Depends on / 依赖: h.ae
-/
theorem ae_eq (h : QuasiMeasurePreserving f μa μb) {g₁ g₂ : β -> δ} (hg : g₁ =ᵐ[μb] g₂) :
    g₁ ∘ f =ᵐ[μa] g₂ ∘ f :=
  h.ae hg

/--
theorem `preimage_null` / 定理 `preimage_null`

English:
theorem preimage_null
  given: (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0)
  proof: preimage_null_of_map_null h.aemeasurable (h.2 hs)

中文:
定理 preimage_null
  条件: (h : 拟保测 f μa μb) {s : 集合 β} (hs : μb s = 0)
  证明: preimage_null_of_map_null h.aemeasurable (h.2 hs)

Depends on / 依赖: aemeasurable, h.aemeasurable, preimage_null_of_map_null
-/
theorem preimage_null (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) :
    μa (f ⁻¹' s) = 0 :=
  preimage_null_of_map_null h.aemeasurable (h.2 hs)

/--
theorem `preimage_mono_ae` / 定理 `preimage_mono_ae`

English:
theorem preimage_mono_ae
  given: {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s <=ᵐ[μb] t)
  proof: eventually_map.mp
    Eventually.filter_mono (tendsto_ae_map hf.aemeasurable) (Eventually.filter_mono hf.ae_map_le h)

中文:
定理 preimage_mono_ae
  条件: {s t : 集合 β} (hf : 拟保测 f μa μb) (h : s <=ᵐ[μb] t)
  证明: eventually_map.mp
    Eventually.filter_mono (tendsto_ae_map hf.aemeasurable) (Eventually.filter_mono hf.ae_map_le h)

Depends on / 依赖: Eventually, Eventually.filter_mono, ae_map_le, aemeasurable, eventually_map, eventually_map.mp, filter_mono, hf.ae_map_le, hf.aemeasurable, tendsto_ae_map
-/
theorem preimage_mono_ae {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s <=ᵐ[μb] t) :
    f ⁻¹' s <=ᵐ[μa] f ⁻¹' t :=
eventually_map.mp
    Eventually.filter_mono (tendsto_ae_map hf.aemeasurable) (Eventually.filter_mono hf.ae_map_le h)

/--
theorem `preimage_ae_eq` / 定理 `preimage_ae_eq`

English:
theorem preimage_ae_eq
  given: {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t)
  proof: EventuallyLE.antisymm (hf.preimage_mono_ae h.le) (hf.preimage_mono_ae h.symm.le)

中文:
定理 preimage_ae_eq
  条件: {s t : 集合 β} (hf : 拟保测 f μa μb) (h : s =ᵐ[μb] t)
  证明: EventuallyLE.antisymm (hf.preimage_mono_ae h.le) (hf.preimage_mono_ae h.symm.le)

Depends on / 依赖: EventuallyLE, EventuallyLE.antisymm, antisymm, h.le, h.symm.le, hf.preimage_mono_ae, preimage_mono_ae
-/
theorem preimage_ae_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t) :
    f ⁻¹' s =ᵐ[μa] f ⁻¹' t :=
  EventuallyLE.antisymm (hf.preimage_mono_ae h.le) (hf.preimage_mono_ae h.symm.le)

/--
theorem `_root_.MeasureTheory.NullMeasurableSet.preimage` / 定理 `_root_.MeasureTheory.NullMeasurableSet.preimage`

English:
theorem _root_.MeasureTheory.NullMeasurableSet.preimage
  statement: {s : Set β} (hs : NullMeasurableSet s μb)
  proof: let ⟨t, htm, hst⟩ := hs
  ⟨f ⁻¹' t, hf.measurable htm, hf.preimage_ae_eq hst⟩

中文:
定理 _root_.测度论.NullMeasurableSet.原像
  结论: {s : 集合 β} (hs : NullMeasurableSet s μb)
  证明: let ⟨t, htm, hst⟩ := hs
  ⟨f ⁻¹' t, hf.measurable htm, hf.preimage_ae_eq hst⟩

Depends on / 依赖: hf.measurable, hf.preimage_ae_eq, measurable, preimage_ae_eq
-/
theorem _root_.MeasureTheory.NullMeasurableSet.preimage {s : Set β} (hs : NullMeasurableSet s μb)
    (hf : QuasiMeasurePreserving f μa μb) : NullMeasurableSet (f ⁻¹' s) μa :=
  let ⟨t, htm, hst⟩ := hs
  ⟨f ⁻¹' t, hf.measurable htm, hf.preimage_ae_eq hst⟩

/--
theorem `preimage_iterate_ae_eq` / 定理 `preimage_iterate_ae_eq`

English:
theorem preimage_iterate_ae_eq
  statement: {s : Set α} {f : α -> α} (hf : QuasiMeasurePreserving f μ μ) (k : Nat)
  proof: by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ]; rw [preimage_comp]
    exact EventuallyEq.trans (hf.preimage_ae_eq ih) hs

中文:
定理 preimage_iterate_ae_eq
  结论: {s : 集合 α} {f : α -> α} (hf : 拟保测 f μ μ) (k : 自然数)
  证明: by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ]; rw [preimage_comp]
    exact EventuallyEq.trans (hf.preimage_ae_eq ih) hs

Depends on / 依赖: EventuallyEq, EventuallyEq.trans, hf.preimage_ae_eq, iterate_succ, preimage_ae_eq, preimage_comp
-/
theorem preimage_iterate_ae_eq {s : Set α} {f : α -> α} (hf : QuasiMeasurePreserving f μ μ) (k : Nat)
    (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ]; rw [preimage_comp]
    exact EventuallyEq.trans (hf.preimage_ae_eq ih) hs

/--
theorem `image_zpow_ae_eq` / 定理 `image_zpow_ae_eq`

English:
theorem image_zpow_ae_eq
  statement: {s : Set α} {e : α ≃ α} (he : QuasiMeasurePreserving e μ μ)
  proof: by
  rw [Equiv.image_eq_preimage_symm]
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · replace hs : (⇑e⁻¹) ⁻¹' s =ᵐ[μ] s := by rwa [Equiv.image_eq_preimage_symm] at hs
    replace he' : (⇑e⁻¹)^[k] ⁻¹' s =ᵐ[μ] s := he'.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e⁻¹ k, inv_pow e k] at he'
  · rw [zpow_neg, zpow_natCast]
    replace hs : e ⁻¹' s =ᵐ[μ] s := by
      convert! he.preimage_ae_eq hs.symm
      rw [Equiv.preimage_image]
    replace he : (⇑e)^[k] ⁻¹' s =ᵐ[μ] s := he.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e k] at he

中文:
定理 image_zpow_ae_eq
  结论: {s : 集合 α} {e : α ≃ α} (he : 拟保测 e μ μ)
  证明: by
  rw [Equiv.image_eq_preimage_symm]
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · replace hs : (⇑e⁻¹) ⁻¹' s =ᵐ[μ] s := by rwa [Equiv.image_eq_preimage_symm] at hs
    replace he' : (⇑e⁻¹)^[k] ⁻¹' s =ᵐ[μ] s := he'.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e⁻¹ k, inv_pow e k] at he'
  · rw [zpow_neg, zpow_natCast]
    replace hs : e ⁻¹' s =ᵐ[μ] s := by
      convert! he.preimage_ae_eq hs.symm
      rw [Equiv.preimage_image]
    replace he : (⇑e)^[k] ⁻¹' s =ᵐ[μ] s := he.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e k] at he

Depends on / 依赖: Equiv.Perm.iterate_eq_pow, Equiv.image_eq_preimage_symm, Equiv.preimage_image, convert, eq_nat_or_neg, he.preimage_ae_eq, he.preimage_iterate_ae_eq, hs.symm, image_eq_preimage_symm, inv_pow, iterate_eq_pow, k.eq_nat_or_neg, preimage_ae_eq, preimage_image, preimage_iterate_ae_eq, replace, zpow_natCast, zpow_neg
-/
theorem image_zpow_ae_eq {s : Set α} {e : α ≃ α} (he : QuasiMeasurePreserving e μ μ)
    (he' : QuasiMeasurePreserving e.symm μ μ) (k : Int) (hs : e '' s =ᵐ[μ] s) :
    (⇑(e ^ k)) '' s =ᵐ[μ] s := by
  rw [Equiv.image_eq_preimage_symm]
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · replace hs : (⇑e⁻¹) ⁻¹' s =ᵐ[μ] s := by rwa [Equiv.image_eq_preimage_symm] at hs
    replace he' : (⇑e⁻¹)^[k] ⁻¹' s =ᵐ[μ] s := he'.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e⁻¹ k, inv_pow e k] at he'
  · rw [zpow_neg, zpow_natCast]
    replace hs : e ⁻¹' s =ᵐ[μ] s := by
      convert! he.preimage_ae_eq hs.symm
      rw [Equiv.preimage_image]
    replace he : (⇑e)^[k] ⁻¹' s =ᵐ[μ] s := he.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e k] at he

-- Need to specify `α := Set α` below because of diamond; see https://github.com/leanprover-community/mathlib4/issues/10941
/--
theorem `limsup_preimage_iterate_ae_eq` / 定理 `limsup_preimage_iterate_ae_eq`

English:
theorem limsup_preimage_iterate_ae_eq
  statement: {f : α -> α} (hf : QuasiMeasurePreserving f μ μ)
  proof: limsup_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n => by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs

中文:
定理 limsup_preimage_iterate_ae_eq
  结论: {f : α -> α} (hf : 拟保测 f μ μ)
  证明: limsup_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n => by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs

Depends on / 依赖: preimage
-/
theorem limsup_preimage_iterate_ae_eq {f : α -> α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : limsup (α := Set α) (fun n => (preimage f)^[n] s) atTop =ᵐ[μ] s :=
  limsup_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n => by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs

-- Need to specify `α := Set α` below because of diamond; see https://github.com/leanprover-community/mathlib4/issues/10941
/--
theorem `liminf_preimage_iterate_ae_eq` / 定理 `liminf_preimage_iterate_ae_eq`

English:
theorem liminf_preimage_iterate_ae_eq
  statement: {f : α -> α} (hf : QuasiMeasurePreserving f μ μ)
  proof: liminf_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n => by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs

中文:
定理 liminf_preimage_iterate_ae_eq
  结论: {f : α -> α} (hf : 拟保测 f μ μ)
  证明: liminf_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n => by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs

Depends on / 依赖: preimage
-/
theorem liminf_preimage_iterate_ae_eq {f : α -> α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : liminf (α := Set α) (fun n => (preimage f)^[n] s) atTop =ᵐ[μ] s :=
  liminf_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n => by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs

/--
theorem `exists_preimage_eq_of_preimage_ae` / 定理 `exists_preimage_eq_of_preimage_ae`

English:
theorem exists_preimage_eq_of_preimage_ae
  statement: {f : α -> α} (h : QuasiMeasurePreserving f μ μ)
  proof: by
  obtain ⟨t, htm, ht⟩ := hs
  refine ⟨limsup (f^[·] ⁻¹' t) atTop, ?_, ?_, ?_⟩
  · exact .measurableSet_limsup fun n => h.measurable.iterate n htm
  · have : f ⁻¹' t =ᵐ[μ] t := (h.preimage_ae_eq ht.symm).trans (hs'.trans ht)
    exact limsup_ae_eq_of_forall_ae_eq _ fun n => .trans (h.preimage_iterate_ae_eq _ this) ht.symm
  · simp only [Set.preimage_iterate_eq]
    exact CompleteLatticeHom.apply_limsup_iterate (CompleteLatticeHom.setPreimage f) t

中文:
定理 存在_preimage_eq_of_preimage_ae
  结论: {f : α -> α} (h : 拟保测 f μ μ)
  证明: by
  obtain ⟨t, htm, ht⟩ := hs
  refine ⟨limsup (f^[·] ⁻¹' t) atTop, ?_, ?_, ?_⟩
  · exact .measurableSet_limsup fun n => h.measurable.iterate n htm
  · have : f ⁻¹' t =ᵐ[μ] t := (h.preimage_ae_eq ht.symm).trans (hs'.trans ht)
    exact limsup_ae_eq_of_forall_ae_eq _ fun n => .trans (h.preimage_iterate_ae_eq _ this) ht.symm
  · simp only [Set.preimage_iterate_eq]
    exact CompleteLatticeHom.apply_limsup_iterate (CompleteLatticeHom.setPreimage f) t

Depends on / 依赖: CompleteLatticeHom, CompleteLatticeHom.apply_limsup_iterate, CompleteLatticeHom.setPreimage, Set.preimage_iterate_eq, apply_limsup_iterate, h.measurable.iterate, h.preimage_ae_eq, h.preimage_iterate_ae_eq, ht.symm, iterate, limsup, limsup_ae_eq_of_forall_ae_eq, measurable, measurableSet_limsup, preimage_ae_eq, preimage_iterate_ae_eq, preimage_iterate_eq, setPreimage
-/
theorem exists_preimage_eq_of_preimage_ae {f : α -> α} (h : QuasiMeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) (hs' : f ⁻¹' s =ᵐ[μ] s) :
    exists t : Set α, MeasurableSet t ∧ t =ᵐ[μ] s ∧ f ⁻¹' t = t := by
  obtain ⟨t, htm, ht⟩ := hs
  refine ⟨limsup (f^[·] ⁻¹' t) atTop, ?_, ?_, ?_⟩
  · exact .measurableSet_limsup fun n => h.measurable.iterate n htm
  · have : f ⁻¹' t =ᵐ[μ] t := (h.preimage_ae_eq ht.symm).trans (hs'.trans ht)
    exact limsup_ae_eq_of_forall_ae_eq _ fun n => .trans (h.preimage_iterate_ae_eq _ this) ht.symm
  · simp only [Set.preimage_iterate_eq]
    exact CompleteLatticeHom.apply_limsup_iterate (CompleteLatticeHom.setPreimage f) t

open scoped Pointwise

@[to_additive]
/--
theorem `smul_ae_eq_of_ae_eq` / 定理 `smul_ae_eq_of_ae_eq`

English:
theorem smul_ae_eq_of_ae_eq
  statement: {G α : Type*} [Group G] [MulAction G α] {_ : MeasurableSpace α}
  proof: by
  simpa only [← preimage_smul_inv] using! h_qmp.ae_eq h_ae_eq

中文:
定理 smul_ae_eq_of_ae_eq
  结论: {G α : 类型} [群 G] [乘法作用 G α] {_ : 可测空间 α}
  证明: by
  simpa only [← preimage_smul_inv] using! h_qmp.ae_eq h_ae_eq

Depends on / 依赖: ae_eq, h_ae_eq, h_qmp, h_qmp.ae_eq, preimage_smul_inv
-/
theorem smul_ae_eq_of_ae_eq {G α : Type*} [Group G] [MulAction G α] {_ : MeasurableSpace α}
    {s t : Set α} {μ : Measure α} (g : G)
    (h_qmp : QuasiMeasurePreserving (g⁻¹ • · : α -> α) μ μ)
    (h_ae_eq : s =ᵐ[μ] t) : (g • s : Set α) =ᵐ[μ] (g • t : Set α) := by
  simpa only [← preimage_smul_inv] using! h_qmp.ae_eq h_ae_eq

end QuasiMeasurePreserving

section Pointwise

open scoped Pointwise

@[to_additive]
/--
theorem `pairwise_aedisjoint_of_aedisjoint_forall_ne_one` / 定理 `pairwise_aedisjoint_of_aedisjoint_forall_ne_one`

English:
theorem pairwise_aedisjoint_of_aedisjoint_forall_ne_one
  statement: {G α : Type*} [Group G] [MulAction G α]
  proof: by
  intro g₁ g₂ hg
  let g := g₂⁻¹ * g₁
  replace hg : g != 1 := by
    rw [Ne]; rw [inv_mul_eq_one]
    exact hg.symm
  have : (g₂⁻¹ • ·) ⁻¹' (g • s inter s) = g₁ • s inter g₂ • s := by
    rw [preimage_eq_iff_eq_image (MulAction.bijective g₂⁻¹)]; rw [image_smul]; rw [smul_set_inter]; rw [smul_smul]; rw [smul_smul]; rw [inv_mul_cancel]; rw [one_smul]
  change μ (g₁ • s inter g₂ • s) = 0
  exact this ▸ (h_qmp g₂⁻¹).preimage_null (h_ae_disjoint g hg)

中文:
定理 pairwise_aedisjoint_of_aedisjoint_对任意_ne_one
  结论: {G α : 类型} [群 G] [乘法作用 G α]
  证明: by
  intro g₁ g₂ hg
  let g := g₂⁻¹ * g₁
  replace hg : g != 1 := by
    rw [Ne]; rw [inv_mul_eq_one]
    exact hg.symm
  have : (g₂⁻¹ • ·) ⁻¹' (g • s inter s) = g₁ • s inter g₂ • s := by
    rw [preimage_eq_iff_eq_image (MulAction.bijective g₂⁻¹)]; rw [image_smul]; rw [smul_set_inter]; rw [smul_smul]; rw [smul_smul]; rw [inv_mul_cancel]; rw [one_smul]
  change μ (g₁ • s inter g₂ • s) = 0
  exact this ▸ (h_qmp g₂⁻¹).preimage_null (h_ae_disjoint g hg)

Depends on / 依赖: MulAction, MulAction.bijective, bijective, h_ae_disjoint, h_qmp, hg.symm, image_smul, inv_mul_cancel, inv_mul_eq_one, one_smul, preimage_eq_iff_eq_image, preimage_null, replace, smul_set_inter, smul_smul
-/
theorem pairwise_aedisjoint_of_aedisjoint_forall_ne_one {G α : Type*} [Group G] [MulAction G α]
    {_ : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (h_ae_disjoint : forall g != (1 : G), AEDisjoint μ (g • s) s)
    (h_qmp : forall g : G, QuasiMeasurePreserving (g • ·) μ μ) :
    Pairwise (AEDisjoint μ on fun g : G => g • s) := by
  intro g₁ g₂ hg
  let g := g₂⁻¹ * g₁
  replace hg : g != 1 := by
    rw [Ne]; rw [inv_mul_eq_one]
    exact hg.symm
  have : (g₂⁻¹ • ·) ⁻¹' (g • s inter s) = g₁ • s inter g₂ • s := by
    rw [preimage_eq_iff_eq_image (MulAction.bijective g₂⁻¹)]; rw [image_smul]; rw [smul_set_inter]; rw [smul_smul]; rw [smul_smul]; rw [inv_mul_cancel]; rw [one_smul]
  change μ (g₁ • s inter g₂ • s) = 0
  exact this ▸ (h_qmp g₂⁻¹).preimage_null (h_ae_disjoint g hg)

end Pointwise

end Measure

open Measure

/--
theorem `NullMeasurable.comp_quasiMeasurePreserving` / 定理 `NullMeasurable.comp_quasiMeasurePreserving`

English:
theorem NullMeasurable.comp_quasiMeasurePreserving
  statement: {ν : Measure β}
  proof: fun _s hs => (hg hs).preimage hf

中文:
定理 NullMeasurable.comp_quasiMeasurePreserving
  结论: {ν : 测度 β}
  证明: fun _s hs => (hg hs).preimage hf

Depends on / 依赖: preimage
-/
theorem NullMeasurable.comp_quasiMeasurePreserving {ν : Measure β}
    {f : α -> β} {g : β -> γ} (hg : NullMeasurable g ν) (hf : QuasiMeasurePreserving f μ ν) :
    NullMeasurable (g ∘ f) μ := fun _s hs => (hg hs).preimage hf

/--
theorem `NullMeasurableSet.mono_ac` / 定理 `NullMeasurableSet.mono_ac`

English:
theorem NullMeasurableSet.mono_ac
  given: (h : NullMeasurableSet s μ) (hle : ν ≪ μ)
  proof: h.preimage (QuasiMeasurePreserving.id μ).mono_left hle

中文:
定理 NullMeasurableSet.mono_ac
  条件: (h : NullMeasurableSet s μ) (hle : ν ≪ μ)
  证明: h.preimage (QuasiMeasurePreserving.id μ).mono_left hle

Depends on / 依赖: QuasiMeasurePreserving, QuasiMeasurePreserving.id, h.preimage, mono_left, preimage
-/
theorem NullMeasurableSet.mono_ac (h : NullMeasurableSet s μ) (hle : ν ≪ μ) :
    NullMeasurableSet s ν :=
h.preimage (QuasiMeasurePreserving.id μ).mono_left hle

/--
theorem `NullMeasurableSet.mono` / 定理 `NullMeasurableSet.mono`

English:
theorem NullMeasurableSet.mono
  given: (h : NullMeasurableSet s μ) (hle : ν <= μ)
  statement: NullMeasurableSet s ν
  proof: h.mono_ac hle.absolutelyContinuous

中文:
定理 NullMeasurableSet.mono
  条件: (h : NullMeasurableSet s μ) (hle : ν <= μ)
  结论: NullMeasurableSet s ν
  证明: h.mono_ac hle.absolutelyContinuous

Depends on / 依赖: absolutelyContinuous, h.mono_ac, hle.absolutelyContinuous, mono_ac
-/
theorem NullMeasurableSet.mono (h : NullMeasurableSet s μ) (hle : ν <= μ) : NullMeasurableSet s ν :=
  h.mono_ac hle.absolutelyContinuous

/--
lemma `NullMeasurableSet.smul_measure` / 引理 `NullMeasurableSet.smul_measure`

English:
lemma NullMeasurableSet.smul_measure
  given: (h : NullMeasurableSet s μ) (c : Real>=0∞)
  proof: h.mono_ac (Measure.AbsolutelyContinuous.rfl.smul_left c)

中文:
引理 NullMeasurableSet.smul_measure
  条件: (h : NullMeasurableSet s μ) (c : 实数>=0∞)
  证明: h.mono_ac (Measure.AbsolutelyContinuous.rfl.smul_left c)

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.rfl.smul_left, h.mono_ac, mono_ac, smul_left
-/
lemma NullMeasurableSet.smul_measure (h : NullMeasurableSet s μ) (c : Real>=0∞) :
    NullMeasurableSet s (c • μ) :=
  h.mono_ac (Measure.AbsolutelyContinuous.rfl.smul_left c)

/--
lemma `nullMeasurableSet_smul_measure_iff` / 引理 `nullMeasurableSet_smul_measure_iff`

English:
lemma nullMeasurableSet_smul_measure_iff
  given: {c : Real>=0∞} (hc : c != 0)
  proof: ⟨fun h => h.mono_ac (Measure.absolutelyContinuous_smul hc), fun h => h.smul_measure c⟩

中文:
引理 nullMeasurableSet_smul_measure_iff
  条件: {c : 实数>=0∞} (hc : c != 0)
  证明: ⟨fun h => h.mono_ac (Measure.absolutelyContinuous_smul hc), fun h => h.smul_measure c⟩

Depends on / 依赖: Measure, Measure.absolutelyContinuous_smul, absolutelyContinuous_smul, h.mono_ac, h.smul_measure, mono_ac, smul_measure
-/
lemma nullMeasurableSet_smul_measure_iff {c : Real>=0∞} (hc : c != 0) :
    NullMeasurableSet s (c • μ) ↔ NullMeasurableSet s μ :=
  ⟨fun h => h.mono_ac (Measure.absolutelyContinuous_smul hc), fun h => h.smul_measure c⟩

/--
theorem `AEDisjoint.preimage` / 定理 `AEDisjoint.preimage`

English:
theorem AEDisjoint.preimage
  statement: {ν : Measure β} {f : α -> β} {s t : Set β} (ht : AEDisjoint ν s t)
  proof: hf.preimage_null ht

中文:
定理 AEDisjoint.原像
  结论: {ν : 测度 β} {f : α -> β} {s t : 集合 β} (ht : AEDisjoint ν s t)
  证明: hf.preimage_null ht

Depends on / 依赖: hf.preimage_null, preimage_null
-/
theorem AEDisjoint.preimage {ν : Measure β} {f : α -> β} {s t : Set β} (ht : AEDisjoint ν s t)
    (hf : QuasiMeasurePreserving f μ ν) : AEDisjoint μ (f ⁻¹' s) (f ⁻¹' t) :=
  hf.preimage_null ht

end MeasureTheory

open MeasureTheory

namespace MeasurableEquiv

variable {_ : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/--
theorem `quasiMeasurePreserving_symm` / 定理 `quasiMeasurePreserving_symm`

English:
theorem quasiMeasurePreserving_symm
  given: (μ : Measure α) (e : α ≃ᵐ β)
  proof: ⟨e.symm.measurable, by rw [Measure.map_map, e.symm_comp_self, Measure.map_id] <;> measurability⟩

中文:
定理 quasiMeasurePreserving_symm
  条件: (μ : 测度 α) (e : α ≃ᵐ β)
  证明: ⟨e.symm.measurable, by rw [Measure.map_map, e.symm_comp_self, Measure.map_id] <;> measurability⟩

Depends on / 依赖: Measure, Measure.map_id, Measure.map_map, e.symm.measurable, e.symm_comp_self, map_id, map_map, measurability, measurable, symm_comp_self
-/
theorem quasiMeasurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) :
    Measure.QuasiMeasurePreserving e.symm (μ.map e) μ :=
  ⟨e.symm.measurable, by rw [Measure.map_map, e.symm_comp_self, Measure.map_id] <;> measurability⟩

end MeasurableEquiv
