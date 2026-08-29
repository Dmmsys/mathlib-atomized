/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Isometries

We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `PseudoMetricSpace` and we specialize to `MetricSpace` when needed.
-/

@[expose] public section

open Topology

noncomputable section

universe u v w

variable {F ι : Type*} {α : Type u} {β : Type v} {γ : Type w}

open Function Set

open scoped Topology ENNReal

/--
Definition of `Isometry` / `Isometry` 的定义

English:
definition Isometry
  signature: [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α -> β)
  body: forall x1 x2 : α, edist (f x1) (f x2) = edist x1 x2

中文:
定义 等距
  签名: [PseudoEMetric空间 α] [PseudoEMetric空间 β] (f : α -> β)
  定义体: forall x1 x2 : α, edist (f x1) (f x2) = edist x1 x2
-/
def Isometry [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α -> β) : Prop :=
  forall x1 x2 : α, edist (f x1) (f x2) = edist x1 x2

/--
theorem `isometry_iff_nndist_eq` / 定理 `isometry_iff_nndist_eq`

English:
theorem isometry_iff_nndist_eq
  given: [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α -> β}
  proof: by
  simp only [Isometry, edist_nndist, ENNReal.coe_inj]

中文:
定理 isometry_iff_nndist_eq
  条件: [伪度量空间 α] [伪度量空间 β] {f : α -> β}
  证明: by
  simp only [Isometry, edist_nndist, ENNReal.coe_inj]

Depends on / 依赖: ENNReal, ENNReal.coe_inj, Isometry, coe_inj, edist_nndist
-/
theorem isometry_iff_nndist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α -> β} :
    Isometry f ↔ forall x y, nndist (f x) (f y) = nndist x y := by
  simp only [Isometry, edist_nndist, ENNReal.coe_inj]

/--
theorem `isometry_iff_dist_eq` / 定理 `isometry_iff_dist_eq`

English:
theorem isometry_iff_dist_eq
  given: [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α -> β}
  proof: by
  simp only [isometry_iff_nndist_eq, ← coe_nndist, NNReal.coe_inj]

中文:
定理 isometry_iff_dist_eq
  条件: [伪度量空间 α] [伪度量空间 β] {f : α -> β}
  证明: by
  simp only [isometry_iff_nndist_eq, ← coe_nndist, NNReal.coe_inj]

Depends on / 依赖: NNReal, NNReal.coe_inj, coe_inj, coe_nndist, isometry_iff_nndist_eq
-/
theorem isometry_iff_dist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α -> β} :
    Isometry f ↔ forall x y, dist (f x) (f y) = dist x y := by
  simp only [isometry_iff_nndist_eq, ← coe_nndist, NNReal.coe_inj]

/-- An isometry preserves distances. -/
alias ⟨Isometry.dist_eq, _⟩ := isometry_iff_dist_eq

/-- A map that preserves distances is an isometry -/
alias ⟨_, Isometry.of_dist_eq⟩ := isometry_iff_dist_eq

/-- An isometry preserves non-negative distances. -/
alias ⟨Isometry.nndist_eq, _⟩ := isometry_iff_nndist_eq

/-- A map that preserves non-negative distances is an isometry. -/
alias ⟨_, Isometry.of_nndist_eq⟩ := isometry_iff_nndist_eq

namespace Isometry

section PseudoEMetricIsometry

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {f : α -> β} {x : α}

/--
theorem `edist_eq` / 定理 `edist_eq`

English:
theorem edist_eq
  given: (hf : Isometry f) (x y : α)
  statement: edist (f x) (f y) = edist x y
  proof: hf x y

中文:
定理 edist_eq
  条件: (hf : 等距 f) (x y : α)
  结论: edist (f x) (f y) = edist x y
  证明: hf x y
-/
theorem edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f y) = edist x y :=
  hf x y

/--
theorem `lipschitz` / 定理 `lipschitz`

English:
theorem lipschitz
  given: (h : Isometry f)
  statement: LipschitzWith 1 f
  proof: LipschitzWith.of_edist_le fun x y => (h x y).le

中文:
定理 lipschitz
  条件: (h : 等距 f)
  结论: LipschitzWith 1 f
  证明: LipschitzWith.of_edist_le fun x y => (h x y).le

Depends on / 依赖: LipschitzWith, LipschitzWith.of_edist_le, of_edist_le
-/
theorem lipschitz (h : Isometry f) : LipschitzWith 1 f :=
  LipschitzWith.of_edist_le fun x y => (h x y).le

/--
theorem `antilipschitz` / 定理 `antilipschitz`

English:
theorem antilipschitz
  given: (h : Isometry f)
  statement: AntilipschitzWith 1 f
  proof: fun x y => by
  simp only [h x y, ENNReal.coe_one, one_mul, le_refl]

中文:
定理 antilipschitz
  条件: (h : 等距 f)
  结论: AntilipschitzWith 1 f
  证明: fun x y => by
  simp only [h x y, ENNReal.coe_one, one_mul, le_refl]

Depends on / 依赖: ENNReal, ENNReal.coe_one, coe_one, le_refl, one_mul
-/
theorem antilipschitz (h : Isometry f) : AntilipschitzWith 1 f := fun x y => by
  simp only [h x y, ENNReal.coe_one, one_mul, le_refl]

/-- Any map on a subsingleton is an isometry -/
@[nontriviality]
/--
theorem `_root_.isometry_subsingleton` / 定理 `_root_.isometry_subsingleton`

English:
theorem _root_.isometry_subsingleton
  given: [Subsingleton α]
  statement: Isometry f
  proof: fun x y => by
  rw [Subsingleton.elim x y]; simp

中文:
定理 _root_.isometry_subsingleton
  条件: [子单例 α]
  结论: 等距 f
  证明: fun x y => by
  rw [Subsingleton.elim x y]; simp

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem _root_.isometry_subsingleton [Subsingleton α] : Isometry f := fun x y => by
  rw [Subsingleton.elim x y]; simp

/--
theorem `_root_.isometry_id` / 定理 `_root_.isometry_id`

English:
theorem _root_.isometry_id
  statement: Isometry (id : α -> α)
  proof: fun _ _ => rfl

中文:
定理 _root_.isometry_id
  结论: 等距 (id : α -> α)
  证明: fun _ _ => rfl
-/
theorem _root_.isometry_id : Isometry (id : α -> α) := fun _ _ => rfl

/--
theorem `prodMap` / 定理 `prodMap`

English:
theorem prodMap
  statement: {δ} [PseudoEMetricSpace δ] {f : α -> β} {g : γ -> δ} (hf : Isometry f)
  proof: fun x y => by
  simp only [Prod.edist_eq, Prod.map_fst, hf.edist_eq, Prod.map_snd, hg.edist_eq]

中文:
定理 prodMap
  结论: {δ} [PseudoEMetric空间 δ] {f : α -> β} {g : γ -> δ} (hf : 等距 f)
  证明: fun x y => by
  simp only [Prod.edist_eq, Prod.map_fst, hf.edist_eq, Prod.map_snd, hg.edist_eq]

Depends on / 依赖: Prod.edist_eq, Prod.map_fst, Prod.map_snd, edist_eq, hf.edist_eq, hg.edist_eq, map_fst, map_snd
-/
theorem prodMap {δ} [PseudoEMetricSpace δ] {f : α -> β} {g : γ -> δ} (hf : Isometry f)
    (hg : Isometry g) : Isometry (Prod.map f g) := fun x y => by
  simp only [Prod.edist_eq, Prod.map_fst, hf.edist_eq, Prod.map_snd, hg.edist_eq]

/--
theorem `piMap` / 定理 `piMap`

English:
theorem piMap
  statement: {ι} [Fintype ι] {α β : ι -> Type*} [forall i, PseudoEMetricSpace (α i)]
  proof: fun x y => by
  simp only [edist_pi_def, (hf _).edist_eq, Pi.map_apply]

中文:
定理 piMap
  结论: {ι} [有限类型 ι] {α β : ι -> 类型} [对任意 i, PseudoEMetric空间 (α i)]
  证明: fun x y => by
  simp only [edist_pi_def, (hf _).edist_eq, Pi.map_apply]
-/
protected theorem piMap {ι} [Fintype ι] {α β : ι -> Type*} [forall i, PseudoEMetricSpace (α i)]
    [forall i, PseudoEMetricSpace (β i)] (f : forall i, α i -> β i) (hf : forall i, Isometry (f i)) :
    Isometry (Pi.map f) := fun x y => by
  simp only [edist_pi_def, (hf _).edist_eq, Pi.map_apply]

/--
lemma `single` / 引理 `single`

English:
lemma single
  statement: [Fintype ι] [DecidableEq ι] {E : ι -> Type*} [forall i, PseudoEMetricSpace (E i)]
  proof: by
  intro x y
  rw [edist_pi_def]
  refine le_antisymm (Finset.sup_le fun j => ?_) (Finset.le_sup_of_le (Finset.mem_univ i) (by simp))
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp [h]

中文:
引理 single
  结论: [有限类型 ι] [DecidableEq ι] {E : ι -> 类型} [对任意 i, PseudoEMetric空间 (E i)]
  证明: by
  intro x y
  rw [edist_pi_def]
  refine le_antisymm (Finset.sup_le fun j => ?_) (Finset.le_sup_of_le (Finset.mem_univ i) (by simp))
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp [h]
-/
protected lemma single [Fintype ι] [DecidableEq ι] {E : ι -> Type*} [forall i, PseudoEMetricSpace (E i)]
    [forall i, Zero (E i)] (i : ι) :
    Isometry (Pi.single (M := E) i) := by
  intro x y
  rw [edist_pi_def]
  refine le_antisymm (Finset.sup_le fun j => ?_) (Finset.le_sup_of_le (Finset.mem_univ i) (by simp))
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp [h]

/--
lemma `inl` / 引理 `inl`

English:
lemma inl
  given: [AddZeroClass α] [AddZeroClass β]
  statement: Isometry (AddMonoidHom.inl α β)
  proof: by
  intro x y
  rw [Prod.edist_eq]
  simp

中文:
引理 inl
  条件: [加法零类 α] [加法零类 β]
  结论: 等距 (加法幺半群态射.inl α β)
  证明: by
  intro x y
  rw [Prod.edist_eq]
  simp
-/
protected lemma inl [AddZeroClass α] [AddZeroClass β] : Isometry (AddMonoidHom.inl α β) := by
  intro x y
  rw [Prod.edist_eq]
  simp

/--
lemma `inr` / 引理 `inr`

English:
lemma inr
  given: [AddZeroClass α] [AddZeroClass β]
  statement: Isometry (AddMonoidHom.inr α β)
  proof: by
  intro x y
  rw [Prod.edist_eq]
  simp

中文:
引理 inr
  条件: [加法零类 α] [加法零类 β]
  结论: 等距 (加法幺半群态射.inr α β)
  证明: by
  intro x y
  rw [Prod.edist_eq]
  simp
-/
protected lemma inr [AddZeroClass α] [AddZeroClass β] : Isometry (AddMonoidHom.inr α β) := by
  intro x y
  rw [Prod.edist_eq]
  simp

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Isometry f)
  statement: Isometry (g ∘ f)
  proof: fun _ _ => (hg _ _).trans (hf _ _)

omit [PseudoEMetricSpace α] in

中文:
定理 comp
  条件: {g : β -> γ} {f : α -> β} (hg : 等距 g) (hf : 等距 f)
  结论: 等距 (g ∘ f)
  证明: fun _ _ => (hg _ _).trans (hf _ _)

omit [PseudoEMetricSpace α] in
-/
theorem comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Isometry f) : Isometry (g ∘ f) :=
  fun _ _ => (hg _ _).trans (hf _ _)

omit [PseudoEMetricSpace α] in
/--
lemma `postcomp_pi` / 引理 `postcomp_pi`

English:
lemma postcomp_pi
  given: [Fintype α] {g : β -> γ} (hg : Isometry g)
  statement: Isometry (fun f : α -> β => g ∘ f)
  proof: fun _ _ => by simp [edist_pi_def, hg.edist_eq]

中文:
引理 postcomp_pi
  条件: [有限类型 α] {g : β -> γ} (hg : 等距 g)
  结论: 等距 (fun f : α -> β => g ∘ f)
  证明: fun _ _ => by simp [edist_pi_def, hg.edist_eq]

Depends on / 依赖: edist_eq, edist_pi_def, hg.edist_eq
-/
lemma postcomp_pi [Fintype α] {g : β -> γ} (hg : Isometry g) : Isometry (fun f : α -> β => g ∘ f) :=
  fun _ _ => by simp [edist_pi_def, hg.edist_eq]

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  given: (hf : Isometry f)
  statement: UniformContinuous f
  proof: hf.lipschitz.uniformContinuous

中文:
定理 uniformContinuous
  条件: (hf : 等距 f)
  结论: 一致连续 f
  证明: hf.lipschitz.uniformContinuous
-/
protected theorem uniformContinuous (hf : Isometry f) : UniformContinuous f :=
  hf.lipschitz.uniformContinuous

/--
theorem `isUniformInducing` / 定理 `isUniformInducing`

English:
theorem isUniformInducing
  given: (hf : Isometry f)
  statement: IsUniformInducing f
  proof: hf.antilipschitz.isUniformInducing hf.uniformContinuous

中文:
定理 isUniformInducing
  条件: (hf : 等距 f)
  结论: 是UniformInducing f
  证明: hf.antilipschitz.isUniformInducing hf.uniformContinuous

Depends on / 依赖: antilipschitz, hf.antilipschitz.isUniformInducing, hf.uniformContinuous, isUniformInducing, uniformContinuous
-/
theorem isUniformInducing (hf : Isometry f) : IsUniformInducing f :=
  hf.antilipschitz.isUniformInducing hf.uniformContinuous

/--
theorem `tendsto_nhds_iff` / 定理 `tendsto_nhds_iff`

English:
theorem tendsto_nhds_iff
  statement: {ι : Type*} {f : α -> β} {g : ι -> α} {a : Filter ι} {b : α}
  proof: hf.isUniformInducing.isInducing.tendsto_nhds_iff

中文:
定理 tendsto_nhds_iff
  结论: {ι : 类型} {f : α -> β} {g : ι -> α} {a : 滤子 ι} {b : α}
  证明: hf.isUniformInducing.isInducing.tendsto_nhds_iff

Depends on / 依赖: hf.isUniformInducing.isInducing.tendsto_nhds_iff, isInducing, isUniformInducing, tendsto_nhds_iff
-/
theorem tendsto_nhds_iff {ι : Type*} {f : α -> β} {g : ι -> α} {a : Filter ι} {b : α}
    (hf : Isometry f) : Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto (f ∘ g) a (𝓝 (f b)) :=
  hf.isUniformInducing.isInducing.tendsto_nhds_iff

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (hf : Isometry f)
  statement: Continuous f
  proof: hf.lipschitz.continuous

中文:
定理 continuous
  条件: (hf : 等距 f)
  结论: 连续 f
  证明: hf.lipschitz.continuous
-/
protected theorem continuous (hf : Isometry f) : Continuous f :=
  hf.lipschitz.continuous

/--
theorem `right_inv` / 定理 `right_inv`

English:
theorem right_inv
  given: {f : α -> β} {g : β -> α} (h : Isometry f) (hg : RightInverse g f)
  statement: Isometry g
  proof: fun x y => by rw [← h, hg _, hg _]

中文:
定理 right_inv
  条件: {f : α -> β} {g : β -> α} (h : 等距 f) (hg : 右逆 g f)
  结论: 等距 g
  证明: fun x y => by rw [← h, hg _, hg _]
-/
theorem right_inv {f : α -> β} {g : β -> α} (h : Isometry f) (hg : RightInverse g f) : Isometry g :=
  fun x y => by rw [← h, hg _, hg _]

/--
theorem `preimage_closedEBall` / 定理 `preimage_closedEBall`

English:
theorem preimage_closedEBall
  given: (h : Isometry f) (x : α) (r : Real>=0∞)
  proof: by
  ext y
  simp [h.edist_eq]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_closedBall := preimage_closedEBall

中文:
定理 preimage_closedEBall
  条件: (h : 等距 f) (x : α) (r : 实数>=0∞)
  证明: by
  ext y
  simp [h.edist_eq]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_closedBall := preimage_closedEBall

Depends on / 依赖: edist_eq, h.edist_eq
-/
theorem preimage_closedEBall (h : Isometry f) (x : α) (r : Real>=0∞) :
    f ⁻¹' Metric.closedEBall (f x) r = Metric.closedEBall x r := by
  ext y
  simp [h.edist_eq]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_closedBall := preimage_closedEBall

/--
theorem `preimage_eball` / 定理 `preimage_eball`

English:
theorem preimage_eball
  given: (h : Isometry f) (x : α) (r : Real>=0∞)
  proof: by
  ext y
  simp [h.edist_eq]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_ball := preimage_eball

中文:
定理 preimage_eball
  条件: (h : 等距 f) (x : α) (r : 实数>=0∞)
  证明: by
  ext y
  simp [h.edist_eq]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_ball := preimage_eball

Depends on / 依赖: edist_eq, h.edist_eq
-/
theorem preimage_eball (h : Isometry f) (x : α) (r : Real>=0∞) :
    f ⁻¹' Metric.eball (f x) r = Metric.eball x r := by
  ext y
  simp [h.edist_eq]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_ball := preimage_eball

/--
theorem `ediam_image` / 定理 `ediam_image`

English:
theorem ediam_image
  given: (hf : Isometry f) (s : Set α)
  statement: Metric.ediam (f '' s) = Metric.ediam s
  proof: eq_of_forall_ge_iff fun d => by simp only [Metric.ediam_le_iff, forall_mem_image, hf.edist_eq]

中文:
定理 ediam_image
  条件: (hf : 等距 f) (s : 集合 α)
  结论: Metric.ediam (f '' s) = Metric.ediam s
  证明: eq_of_forall_ge_iff fun d => by simp only [Metric.ediam_le_iff, forall_mem_image, hf.edist_eq]

Depends on / 依赖: Metric, Metric.ediam_le_iff, ediam_le_iff, edist_eq, eq_of_forall_ge_iff, forall_mem_image, hf.edist_eq
-/
theorem ediam_image (hf : Isometry f) (s : Set α) : Metric.ediam (f '' s) = Metric.ediam s :=
  eq_of_forall_ge_iff fun d => by simp only [Metric.ediam_le_iff, forall_mem_image, hf.edist_eq]

/--
theorem `ediam_range` / 定理 `ediam_range`

English:
theorem ediam_range
  given: (hf : Isometry f)
  statement: Metric.ediam (range f) = Metric.ediam (univ : Set α)
  proof: by
  rw [← image_univ]
  exact hf.ediam_image univ

中文:
定理 ediam_range
  条件: (hf : 等距 f)
  结论: Metric.ediam (range f) = Metric.ediam (univ : 集合 α)
  证明: by
  rw [← image_univ]
  exact hf.ediam_image univ

Depends on / 依赖: ediam_image, hf.ediam_image, image_univ
-/
theorem ediam_range (hf : Isometry f) : Metric.ediam (range f) = Metric.ediam (univ : Set α) := by
  rw [← image_univ]
  exact hf.ediam_image univ

/--
theorem `mapsTo_eball` / 定理 `mapsTo_eball`

English:
theorem mapsTo_eball
  given: (hf : Isometry f) (x : α) (r : Real>=0∞)
  proof: (hf.preimage_eball x r).ge

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

中文:
定理 mapsTo_eball
  条件: (hf : 等距 f) (x : α) (r : 实数>=0∞)
  证明: (hf.preimage_eball x r).ge

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

Depends on / 依赖: hf.preimage_eball, preimage_eball
-/
theorem mapsTo_eball (hf : Isometry f) (x : α) (r : Real>=0∞) :
    MapsTo f (Metric.eball x r) (Metric.eball (f x) r) :=
  (hf.preimage_eball x r).ge

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

/--
theorem `mapsTo_closedEBall` / 定理 `mapsTo_closedEBall`

English:
theorem mapsTo_closedEBall
  given: (hf : Isometry f) (x : α) (r : Real>=0∞)
  proof: (hf.preimage_closedEBall x r).ge

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

中文:
定理 mapsTo_closedEBall
  条件: (hf : 等距 f) (x : α) (r : 实数>=0∞)
  证明: (hf.preimage_closedEBall x r).ge

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

Depends on / 依赖: hf.preimage_closedEBall, preimage_closedEBall
-/
theorem mapsTo_closedEBall (hf : Isometry f) (x : α) (r : Real>=0∞) :
    MapsTo f (Metric.closedEBall x r) (Metric.closedEBall (f x) r) :=
  (hf.preimage_closedEBall x r).ge

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

/--
theorem `_root_.isometry_subtype_coe` / 定理 `_root_.isometry_subtype_coe`

English:
theorem _root_.isometry_subtype_coe
  given: {s : Set α}
  statement: Isometry ((↑) : s -> α)
  proof: fun _ _ => rfl

中文:
定理 _root_.isometry_subtype_coe
  条件: {s : 集合 α}
  结论: 等距 ((↑) : s -> α)
  证明: fun _ _ => rfl
-/
theorem _root_.isometry_subtype_coe {s : Set α} : Isometry ((↑) : s -> α) := fun _ _ => rfl

/--
theorem `_root_.NNReal.isometry_coe` / 定理 `_root_.NNReal.isometry_coe`

English:
theorem _root_.NNReal.isometry_coe
  statement: Isometry ((↑) : NNReal -> Real)
  proof: fun _ _ => rfl

中文:
定理 _root_.非负实数.isometry_coe
  结论: 等距 ((↑) : 非负实数 -> 实数)
  证明: fun _ _ => rfl
-/
theorem _root_.NNReal.isometry_coe : Isometry ((↑) : NNReal -> Real) := fun _ _ => rfl

/--
theorem `comp_continuousOn_iff` / 定理 `comp_continuousOn_iff`

English:
theorem comp_continuousOn_iff
  given: {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ -> α} {s : Set γ}
  proof: hf.isUniformInducing.isInducing.continuousOn_iff.symm

中文:
定理 comp_continuousOn_iff
  条件: {γ} [拓扑空间 γ] (hf : 等距 f) {g : γ -> α} {s : 集合 γ}
  证明: hf.isUniformInducing.isInducing.continuousOn_iff.symm

Depends on / 依赖: continuousOn_iff, hf.isUniformInducing.isInducing.continuousOn_iff.symm, isInducing, isUniformInducing
-/
theorem comp_continuousOn_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ -> α} {s : Set γ} :
    ContinuousOn (f ∘ g) s ↔ ContinuousOn g s :=
  hf.isUniformInducing.isInducing.continuousOn_iff.symm

/--
theorem `comp_continuous_iff` / 定理 `comp_continuous_iff`

English:
theorem comp_continuous_iff
  given: {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ -> α}
  proof: hf.isUniformInducing.isInducing.continuous_iff.symm

中文:
定理 comp_continuous_iff
  条件: {γ} [拓扑空间 γ] (hf : 等距 f) {g : γ -> α}
  证明: hf.isUniformInducing.isInducing.continuous_iff.symm

Depends on / 依赖: continuous_iff, hf.isUniformInducing.isInducing.continuous_iff.symm, isInducing, isUniformInducing
-/
theorem comp_continuous_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ -> α} :
    Continuous (f ∘ g) ↔ Continuous g :=
  hf.isUniformInducing.isInducing.continuous_iff.symm

end PseudoEMetricIsometry

--section
section EMetricIsometry

variable [EMetricSpace α] [PseudoEMetricSpace β] {f : α -> β}

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (h : Isometry f)
  statement: Injective f
  proof: h.antilipschitz.injective

中文:
定理 injective
  条件: (h : 等距 f)
  结论: 单射 f
  证明: h.antilipschitz.injective
-/
protected theorem injective (h : Isometry f) : Injective f :=
  h.antilipschitz.injective

/--
lemma `isUniformEmbedding` / 引理 `isUniformEmbedding`

English:
lemma isUniformEmbedding
  given: (hf : Isometry f)
  statement: IsUniformEmbedding f
  proof: hf.antilipschitz.isUniformEmbedding hf.lipschitz.uniformContinuous

中文:
引理 isUniformEmbedding
  条件: (hf : 等距 f)
  结论: 是一致嵌入 f
  证明: hf.antilipschitz.isUniformEmbedding hf.lipschitz.uniformContinuous

Depends on / 依赖: antilipschitz, hf.antilipschitz.isUniformEmbedding, hf.lipschitz.uniformContinuous, isUniformEmbedding, lipschitz, uniformContinuous
-/
lemma isUniformEmbedding (hf : Isometry f) : IsUniformEmbedding f :=
  hf.antilipschitz.isUniformEmbedding hf.lipschitz.uniformContinuous

/--
theorem `isEmbedding` / 定理 `isEmbedding`

English:
theorem isEmbedding
  given: (hf : Isometry f)
  statement: IsEmbedding f
  proof: hf.isUniformEmbedding.isEmbedding

中文:
定理 isEmbedding
  条件: (hf : 等距 f)
  结论: 是嵌入 f
  证明: hf.isUniformEmbedding.isEmbedding

Depends on / 依赖: hf.isUniformEmbedding.isEmbedding, isEmbedding, isUniformEmbedding
-/
theorem isEmbedding (hf : Isometry f) : IsEmbedding f := hf.isUniformEmbedding.isEmbedding

/--
theorem `isClosedEmbedding` / 定理 `isClosedEmbedding`

English:
theorem isClosedEmbedding
  given: [CompleteSpace α] [EMetricSpace γ] {f : α -> γ} (hf : Isometry f)
  proof: hf.antilipschitz.isClosedEmbedding hf.lipschitz.uniformContinuous

中文:
定理 isClosedEmbedding
  条件: [完备空间 α] [广义度量空间 γ] {f : α -> γ} (hf : 等距 f)
  证明: hf.antilipschitz.isClosedEmbedding hf.lipschitz.uniformContinuous

Depends on / 依赖: antilipschitz, hf.antilipschitz.isClosedEmbedding, hf.lipschitz.uniformContinuous, isClosedEmbedding, lipschitz, uniformContinuous
-/
theorem isClosedEmbedding [CompleteSpace α] [EMetricSpace γ] {f : α -> γ} (hf : Isometry f) :
    IsClosedEmbedding f :=
  hf.antilipschitz.isClosedEmbedding hf.lipschitz.uniformContinuous

end EMetricIsometry

--section
section PseudoMetricIsometry

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α -> β}

/--
theorem `diam_image` / 定理 `diam_image`

English:
theorem diam_image
  given: (hf : Isometry f) (s : Set α)
  statement: Metric.diam (f '' s) = Metric.diam s
  proof: by
  rw [Metric.diam]; rw [Metric.diam]; rw [hf.ediam_image]

中文:
定理 diam_image
  条件: (hf : 等距 f) (s : 集合 α)
  结论: Metric.diam (f '' s) = Metric.diam s
  证明: by
  rw [Metric.diam]; rw [Metric.diam]; rw [hf.ediam_image]

Depends on / 依赖: Metric, Metric.diam, ediam_image, hf.ediam_image
-/
theorem diam_image (hf : Isometry f) (s : Set α) : Metric.diam (f '' s) = Metric.diam s := by
  rw [Metric.diam]; rw [Metric.diam]; rw [hf.ediam_image]

/--
theorem `diam_range` / 定理 `diam_range`

English:
theorem diam_range
  given: (hf : Isometry f)
  statement: Metric.diam (range f) = Metric.diam (univ : Set α)
  proof: by
  rw [← image_univ]
  exact hf.diam_image univ

中文:
定理 diam_range
  条件: (hf : 等距 f)
  结论: Metric.diam (range f) = Metric.diam (univ : 集合 α)
  证明: by
  rw [← image_univ]
  exact hf.diam_image univ

Depends on / 依赖: diam_image, hf.diam_image, image_univ
-/
theorem diam_range (hf : Isometry f) : Metric.diam (range f) = Metric.diam (univ : Set α) := by
  rw [← image_univ]
  exact hf.diam_image univ

/--
theorem `preimage_setOfPred_dist` / 定理 `preimage_setOfPred_dist`

English:
theorem preimage_setOfPred_dist
  given: (hf : Isometry f) (x : α) (p : Real -> Prop)
  proof: by
  simp [hf.dist_eq]

@[deprecated (since := "2026-07-09")] alias preimage_setOf_dist := preimage_setOfPred_dist

中文:
定理 preimage_setOfPred_dist
  条件: (hf : 等距 f) (x : α) (p : 实数 -> 命题)
  证明: by
  simp [hf.dist_eq]

@[deprecated (since := "2026-07-09")] alias preimage_setOf_dist := preimage_setOfPred_dist

Depends on / 依赖: dist_eq, hf.dist_eq
-/
theorem preimage_setOfPred_dist (hf : Isometry f) (x : α) (p : Real -> Prop) :
    f ⁻¹' { y | p (dist y (f x)) } = { y | p (dist y x) } := by
  simp [hf.dist_eq]

@[deprecated (since := "2026-07-09")] alias preimage_setOf_dist := preimage_setOfPred_dist

/--
theorem `preimage_closedBall` / 定理 `preimage_closedBall`

English:
theorem preimage_closedBall
  given: (hf : Isometry f) (x : α) (r : Real)
  proof: hf.preimage_setOfPred_dist x (· <= r)

中文:
定理 preimage_closedBall
  条件: (hf : 等距 f) (x : α) (r : 实数)
  证明: hf.preimage_setOfPred_dist x (· <= r)

Depends on / 依赖: hf.preimage_setOfPred_dist, preimage_setOfPred_dist
-/
theorem preimage_closedBall (hf : Isometry f) (x : α) (r : Real) :
    f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r :=
  hf.preimage_setOfPred_dist x (· <= r)

/--
theorem `preimage_ball` / 定理 `preimage_ball`

English:
theorem preimage_ball
  given: (hf : Isometry f) (x : α) (r : Real)
  proof: hf.preimage_setOfPred_dist x (· < r)

中文:
定理 preimage_ball
  条件: (hf : 等距 f) (x : α) (r : 实数)
  证明: hf.preimage_setOfPred_dist x (· < r)

Depends on / 依赖: hf.preimage_setOfPred_dist, preimage_setOfPred_dist
-/
theorem preimage_ball (hf : Isometry f) (x : α) (r : Real) :
    f ⁻¹' Metric.ball (f x) r = Metric.ball x r :=
  hf.preimage_setOfPred_dist x (· < r)

/--
theorem `preimage_sphere` / 定理 `preimage_sphere`

English:
theorem preimage_sphere
  given: (hf : Isometry f) (x : α) (r : Real)
  proof: hf.preimage_setOfPred_dist x (· = r)

中文:
定理 preimage_sphere
  条件: (hf : 等距 f) (x : α) (r : 实数)
  证明: hf.preimage_setOfPred_dist x (· = r)

Depends on / 依赖: hf.preimage_setOfPred_dist, preimage_setOfPred_dist
-/
theorem preimage_sphere (hf : Isometry f) (x : α) (r : Real) :
    f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r :=
  hf.preimage_setOfPred_dist x (· = r)

/--
theorem `mapsTo_ball` / 定理 `mapsTo_ball`

English:
theorem mapsTo_ball
  given: (hf : Isometry f) (x : α) (r : Real)
  proof: (hf.preimage_ball x r).ge

中文:
定理 mapsTo_ball
  条件: (hf : 等距 f) (x : α) (r : 实数)
  证明: (hf.preimage_ball x r).ge

Depends on / 依赖: hf.preimage_ball, preimage_ball
-/
theorem mapsTo_ball (hf : Isometry f) (x : α) (r : Real) :
    MapsTo f (Metric.ball x r) (Metric.ball (f x) r) :=
  (hf.preimage_ball x r).ge

/--
theorem `mapsTo_sphere` / 定理 `mapsTo_sphere`

English:
theorem mapsTo_sphere
  given: (hf : Isometry f) (x : α) (r : Real)
  proof: (hf.preimage_sphere x r).ge

中文:
定理 mapsTo_sphere
  条件: (hf : 等距 f) (x : α) (r : 实数)
  证明: (hf.preimage_sphere x r).ge

Depends on / 依赖: hf.preimage_sphere, preimage_sphere
-/
theorem mapsTo_sphere (hf : Isometry f) (x : α) (r : Real) :
    MapsTo f (Metric.sphere x r) (Metric.sphere (f x) r) :=
  (hf.preimage_sphere x r).ge

/--
theorem `mapsTo_closedBall` / 定理 `mapsTo_closedBall`

English:
theorem mapsTo_closedBall
  given: (hf : Isometry f) (x : α) (r : Real)
  proof: (hf.preimage_closedBall x r).ge

中文:
定理 mapsTo_closedBall
  条件: (hf : 等距 f) (x : α) (r : 实数)
  证明: (hf.preimage_closedBall x r).ge

Depends on / 依赖: hf.preimage_closedBall, preimage_closedBall
-/
theorem mapsTo_closedBall (hf : Isometry f) (x : α) (r : Real) :
    MapsTo f (Metric.closedBall x r) (Metric.closedBall (f x) r) :=
  (hf.preimage_closedBall x r).ge

end PseudoMetricIsometry

-- section
end Isometry

-- namespace
/--
theorem `IsUniformEmbedding.to_isometry` / 定理 `IsUniformEmbedding.to_isometry`

English:
theorem IsUniformEmbedding.to_isometry
  statement: {α β} [UniformSpace α] [MetricSpace β] {f : α -> β}
  proof: let _ := h.comapMetricSpace f
  Isometry.of_dist_eq fun _ _ => rfl

中文:
定理 是一致嵌入.to_isometry
  结论: {α β} [一致空间 α] [度量空间 β] {f : α -> β}
  证明: let _ := h.comapMetricSpace f
  Isometry.of_dist_eq fun _ _ => rfl

Depends on / 依赖: Isometry, comapMetricSpace, h.comapMetricSpace
-/
theorem IsUniformEmbedding.to_isometry {α β} [UniformSpace α] [MetricSpace β] {f : α -> β}
    (h : IsUniformEmbedding f) : (letI := h.comapMetricSpace f; Isometry f) :=
  let _ := h.comapMetricSpace f
  Isometry.of_dist_eq fun _ _ => rfl

/--
theorem `Topology.IsEmbedding.to_isometry` / 定理 `Topology.IsEmbedding.to_isometry`

English:
theorem Topology.IsEmbedding.to_isometry
  statement: {α β} [TopologicalSpace α] [PseudoMetricSpace β]
  proof: let _ := h.comapPseudoMetricSpace
  Isometry.of_dist_eq fun _ _ => rfl

中文:
定理 拓扑.是嵌入.to_isometry
  结论: {α β} [拓扑空间 α] [伪度量空间 β]
  证明: let _ := h.comapPseudoMetricSpace
  Isometry.of_dist_eq fun _ _ => rfl

Depends on / 依赖: Isometry, comapPseudoMetricSpace, h.comapPseudoMetricSpace
-/
theorem Topology.IsEmbedding.to_isometry {α β} [TopologicalSpace α] [PseudoMetricSpace β]
    {f : α -> β} (h : IsEmbedding f) : (letI := h.comapPseudoMetricSpace; Isometry f) :=
  let _ := h.comapPseudoMetricSpace
  Isometry.of_dist_eq fun _ _ => rfl

/--
theorem `PseudoEMetricSpace.isometry_induced` / 定理 `PseudoEMetricSpace.isometry_induced`

English:
theorem PseudoEMetricSpace.isometry_induced
  given: (f : α -> β) [m : PseudoEMetricSpace β]
  proof: m.induced f; Isometry f := fun _ _ => rfl

中文:
定理 PseudoEMetric空间.isometry_induced
  条件: (f : α -> β) [m : PseudoEMetric空间 β]
  证明: m.induced f; Isometry f := fun _ _ => rfl

Depends on / 依赖: Isometry, induced, m.induced
-/
theorem PseudoEMetricSpace.isometry_induced (f : α -> β) [m : PseudoEMetricSpace β] :
    letI := m.induced f; Isometry f := fun _ _ => rfl

/--
theorem `PseudoMetricSpace.isometry_induced` / 定理 `PseudoMetricSpace.isometry_induced`

English:
theorem PseudoMetricSpace.isometry_induced
  given: (f : α -> β) [m : PseudoMetricSpace β]
  proof: m.induced f; Isometry f := fun _ _ => rfl

中文:
定理 伪度量空间.isometry_induced
  条件: (f : α -> β) [m : 伪度量空间 β]
  证明: m.induced f; Isometry f := fun _ _ => rfl

Depends on / 依赖: Isometry, induced, m.induced
-/
theorem PseudoMetricSpace.isometry_induced (f : α -> β) [m : PseudoMetricSpace β] :
    letI := m.induced f; Isometry f := fun _ _ => rfl

/--
theorem `EMetricSpace.isometry_induced` / 定理 `EMetricSpace.isometry_induced`

English:
theorem EMetricSpace.isometry_induced
  given: (f : α -> β) (hf : f.Injective) [m : EMetricSpace β]
  proof: m.induced f hf; Isometry f := fun _ _ => rfl

中文:
定理 广义度量空间.isometry_induced
  条件: (f : α -> β) (hf : f.单射) [m : 广义度量空间 β]
  证明: m.induced f hf; Isometry f := fun _ _ => rfl

Depends on / 依赖: Isometry, induced, m.induced
-/
theorem EMetricSpace.isometry_induced (f : α -> β) (hf : f.Injective) [m : EMetricSpace β] :
    letI := m.induced f hf; Isometry f := fun _ _ => rfl

/--
theorem `MetricSpace.isometry_induced` / 定理 `MetricSpace.isometry_induced`

English:
theorem MetricSpace.isometry_induced
  given: (f : α -> β) (hf : f.Injective) [m : MetricSpace β]
  proof: m.induced f hf; Isometry f := fun _ _ => rfl

中文:
定理 度量空间.isometry_induced
  条件: (f : α -> β) (hf : f.单射) [m : 度量空间 β]
  证明: m.induced f hf; Isometry f := fun _ _ => rfl

Depends on / 依赖: Isometry, induced, m.induced
-/
theorem MetricSpace.isometry_induced (f : α -> β) (hf : f.Injective) [m : MetricSpace β] :
    letI := m.induced f hf; Isometry f := fun _ _ => rfl

/--
Definition of `IsometryClass` / `IsometryClass` 的定义

English:
class IsometryClass
  parameters: (F : Type*) (α β : outParam Type*)
  axioms and operations (1):
    - isometry((f : F)) : Isometry f

中文:
类 等距类
  参数: (F : 类型) (α β : outParam 类型)
  公理与运算 (1 个):
    - isometry((f : F)) : 等距 f
-/
class IsometryClass (F : Type*) (α β : outParam Type*)
    [PseudoEMetricSpace α] [PseudoEMetricSpace β] [FunLike F α β] : Prop where
  protected isometry (f : F) : Isometry f

namespace IsometryClass

section PseudoEMetricSpace
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

section
variable [FunLike F α β] [IsometryClass F α β] (f : F)

/--
theorem `edist_eq` / 定理 `edist_eq`

English:
theorem edist_eq
  given: (x y : α)
  statement: edist (f x) (f y) = edist x y
  proof: (IsometryClass.isometry f).edist_eq x y

中文:
定理 edist_eq
  条件: (x y : α)
  结论: edist (f x) (f y) = edist x y
  证明: (IsometryClass.isometry f).edist_eq x y
-/
protected theorem edist_eq (x y : α) : edist (f x) (f y) = edist x y :=
  (IsometryClass.isometry f).edist_eq x y

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous f
  proof: (IsometryClass.isometry f).continuous

中文:
定理 continuous
  结论: 连续 f
  证明: (IsometryClass.isometry f).continuous
-/
protected theorem continuous : Continuous f :=
  (IsometryClass.isometry f).continuous

/--
theorem `lipschitz` / 定理 `lipschitz`

English:
theorem lipschitz
  statement: LipschitzWith 1 f
  proof: (IsometryClass.isometry f).lipschitz

中文:
定理 lipschitz
  结论: LipschitzWith 1 f
  证明: (IsometryClass.isometry f).lipschitz
-/
protected theorem lipschitz : LipschitzWith 1 f :=
  (IsometryClass.isometry f).lipschitz

/--
theorem `antilipschitz` / 定理 `antilipschitz`

English:
theorem antilipschitz
  statement: AntilipschitzWith 1 f
  proof: (IsometryClass.isometry f).antilipschitz

中文:
定理 antilipschitz
  结论: AntilipschitzWith 1 f
  证明: (IsometryClass.isometry f).antilipschitz
-/
protected theorem antilipschitz : AntilipschitzWith 1 f :=
  (IsometryClass.isometry f).antilipschitz

/--
theorem `ediam_image` / 定理 `ediam_image`

English:
theorem ediam_image
  given: (s : Set α)
  statement: Metric.ediam (f '' s) = Metric.ediam s
  proof: (IsometryClass.isometry f).ediam_image s

中文:
定理 ediam_image
  条件: (s : 集合 α)
  结论: Metric.ediam (f '' s) = Metric.ediam s
  证明: (IsometryClass.isometry f).ediam_image s

Depends on / 依赖: IsometryClass, IsometryClass.isometry, ediam_image, isometry
-/
theorem ediam_image (s : Set α) : Metric.ediam (f '' s) = Metric.ediam s :=
  (IsometryClass.isometry f).ediam_image s

/--
theorem `ediam_range` / 定理 `ediam_range`

English:
theorem ediam_range
  statement: Metric.ediam (range f) = Metric.ediam (univ : Set α)
  proof: (IsometryClass.isometry f).ediam_range

中文:
定理 ediam_range
  结论: Metric.ediam (range f) = Metric.ediam (univ : 集合 α)
  证明: (IsometryClass.isometry f).ediam_range

Depends on / 依赖: IsometryClass, IsometryClass.isometry, ediam_range, isometry
-/
theorem ediam_range : Metric.ediam (range f) = Metric.ediam (univ : Set α) :=
  (IsometryClass.isometry f).ediam_range

/--
Instance `toContinuousMapClass` / 实例 `toContinuousMapClass`

English:
instance toContinuousMapClass
  signature: : ContinuousMapClass F α β where
  body: IsometryClass.continuous

中文:
实例 toContinuousMapClass
  签名: : 连续映射类 F α β where
  定义体: IsometryClass.continuous

Depends on / 依赖: IsometryClass, IsometryClass.continuous, continuous
-/
instance toContinuousMapClass : ContinuousMapClass F α β where
  map_continuous := IsometryClass.continuous

end

/--
Instance `toHomeomorphClass` / 实例 `toHomeomorphClass`

English:
instance toHomeomorphClass
  signature: [EquivLike F α β] [IsometryClass F α β]
  body: IsometryClass.continuous
  inv_continuous f := ((IsometryClass.isometry f).right_inv (EquivLike.right_inv f)).continuous

中文:
实例 toHomeomorphClass
  签名: [等价状 F α β] [等距类 F α β]
  定义体: IsometryClass.continuous
  inv_continuous f := ((IsometryClass.isometry f).right_inv (EquivLike.right_inv f)).continuous

Depends on / 依赖: IsometryClass, IsometryClass.continuous, continuous
-/
instance toHomeomorphClass [EquivLike F α β] [IsometryClass F α β] : HomeomorphClass F α β where
  map_continuous := IsometryClass.continuous
  inv_continuous f := ((IsometryClass.isometry f).right_inv (EquivLike.right_inv f)).continuous

end PseudoEMetricSpace

section PseudoMetricSpace
variable [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β] [IsometryClass F α β] (f : F)

/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  given: (x y : α)
  statement: dist (f x) (f y) = dist x y
  proof: (IsometryClass.isometry f).dist_eq x y

中文:
定理 dist_eq
  条件: (x y : α)
  结论: dist (f x) (f y) = dist x y
  证明: (IsometryClass.isometry f).dist_eq x y
-/
protected theorem dist_eq (x y : α) : dist (f x) (f y) = dist x y :=
  (IsometryClass.isometry f).dist_eq x y

/--
theorem `nndist_eq` / 定理 `nndist_eq`

English:
theorem nndist_eq
  given: (x y : α)
  statement: nndist (f x) (f y) = nndist x y
  proof: (IsometryClass.isometry f).nndist_eq x y

中文:
定理 nndist_eq
  条件: (x y : α)
  结论: nndist (f x) (f y) = nndist x y
  证明: (IsometryClass.isometry f).nndist_eq x y
-/
protected theorem nndist_eq (x y : α) : nndist (f x) (f y) = nndist x y :=
  (IsometryClass.isometry f).nndist_eq x y

/--
theorem `diam_image` / 定理 `diam_image`

English:
theorem diam_image
  given: (s : Set α)
  statement: Metric.diam (f '' s) = Metric.diam s
  proof: (IsometryClass.isometry f).diam_image s

中文:
定理 diam_image
  条件: (s : 集合 α)
  结论: Metric.diam (f '' s) = Metric.diam s
  证明: (IsometryClass.isometry f).diam_image s

Depends on / 依赖: IsometryClass, IsometryClass.isometry, diam_image, isometry
-/
theorem diam_image (s : Set α) : Metric.diam (f '' s) = Metric.diam s :=
  (IsometryClass.isometry f).diam_image s

/--
theorem `diam_range` / 定理 `diam_range`

English:
theorem diam_range
  statement: Metric.diam (range f) = Metric.diam (univ : Set α)
  proof: (IsometryClass.isometry f).diam_range

中文:
定理 diam_range
  结论: Metric.diam (range f) = Metric.diam (univ : 集合 α)
  证明: (IsometryClass.isometry f).diam_range

Depends on / 依赖: IsometryClass, IsometryClass.isometry, diam_range, isometry
-/
theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set α) :=
  (IsometryClass.isometry f).diam_range

end PseudoMetricSpace

end IsometryClass

-- such a bijection need not exist
/--
Definition of `IsometryEquiv` / `IsometryEquiv` 的定义

English:
structure IsometryEquiv
  parameters: (α : Type u) (β : Type v) [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  extends: α ≃ β
  axioms and operations (1):
    - isometry_toFun : Isometry toFun

中文:
结构 等距等价
  参数: (α : 类型u) (β : 类型v) [PseudoEMetric空间 α] [PseudoEMetric空间 β]
  继承: α ≃ β
  公理与运算 (1 个):
    - isometry_toFun : 等距 toFun
-/
structure IsometryEquiv (α : Type u) (β : Type v) [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    extends α ≃ β where
  isometry_toFun : Isometry toFun

@[inherit_doc]
infixl:25 " ≃ᵢ " => IsometryEquiv

namespace IsometryEquiv

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  statement: Injective (toEquiv : (α ≃ᵢ β) -> (α ≃ β))

中文:
定理 toEquiv_injective
  结论: 单射 (toEquiv : (α ≃ᵢ β) -> (α ≃ β))
-/
theorem toEquiv_injective : Injective (toEquiv : (α ≃ᵢ β) -> (α ≃ β))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/--
theorem `toEquiv_inj` / 定理 `toEquiv_inj`

English:
theorem toEquiv_inj
  given: {e₁ e₂ : α ≃ᵢ β}
  statement: e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
  proof: toEquiv_injective.eq_iff

中文:
定理 toEquiv_inj
  条件: {e₁ e₂ : α ≃ᵢ β}
  结论: e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
  证明: toEquiv_injective.eq_iff
-/
@[simp] theorem toEquiv_inj {e₁ e₂ : α ≃ᵢ β} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (α ≃ᵢ β) α β
  body: e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.left_inv
  right_inv e := e.right_inv
coe_injective' _ _ h _ := toEquiv_injective DFunLike.ext' h

中文:
实例 :
  签名: 等价状 (α ≃ᵢ β) α β
  定义体: e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.left_inv
  right_inv e := e.right_inv
coe_injective' _ _ h _ := toEquiv_injective DFunLike.ext' h

Depends on / 依赖: e.toEquiv, toEquiv
-/
instance : EquivLike (α ≃ᵢ β) α β where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.left_inv
  right_inv e := e.right_inv
coe_injective' _ _ h _ := toEquiv_injective DFunLike.ext' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsometryClass (IsometryEquiv α β) α β
  body: isometry_toFun

中文:
实例 :
  签名: 等距类 (等距等价 α β) α β
  定义体: isometry_toFun

Depends on / 依赖: isometry_toFun
-/
instance : IsometryClass (IsometryEquiv α β) α β where
  isometry := isometry_toFun

/--
theorem `coe_eq_toEquiv` / 定理 `coe_eq_toEquiv`

English:
theorem coe_eq_toEquiv
  given: (h : α ≃ᵢ β) (a : α)
  statement: h a = h.toEquiv a
  proof: rfl

中文:
定理 coe_eq_toEquiv
  条件: (h : α ≃ᵢ β) (a : α)
  结论: h a = h.toEquiv a
  证明: rfl
-/
theorem coe_eq_toEquiv (h : α ≃ᵢ β) (a : α) : h a = h.toEquiv a := rfl

/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (h : α ≃ᵢ β)
  statement: ⇑h.toEquiv = h
  proof: rfl

中文:
定理 coe_toEquiv
  条件: (h : α ≃ᵢ β)
  结论: ⇑h.toEquiv = h
  证明: rfl
-/
@[simp] theorem coe_toEquiv (h : α ≃ᵢ β) : ⇑h.toEquiv = h := rfl

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : α ≃ β) (h)
  statement: ⇑(mk e h) = e
  proof: rfl

中文:
定理 coe_mk
  条件: (e : α ≃ β) (h)
  结论: ⇑(mk e h) = e
  证明: rfl
-/
@[simp] theorem coe_mk (e : α ≃ β) (h) : ⇑(mk e h) = e := rfl

/--
theorem `isometry` / 定理 `isometry`

English:
theorem isometry
  given: (h : α ≃ᵢ β)
  statement: Isometry h
  proof: h.isometry_toFun

中文:
定理 isometry
  条件: (h : α ≃ᵢ β)
  结论: 等距 h
  证明: h.isometry_toFun
-/
protected theorem isometry (h : α ≃ᵢ β) : Isometry h :=
  h.isometry_toFun

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (h : α ≃ᵢ β)
  statement: Bijective h
  proof: h.toEquiv.bijective

中文:
定理 bijective
  条件: (h : α ≃ᵢ β)
  结论: 双射 h
  证明: h.toEquiv.bijective
-/
protected theorem bijective (h : α ≃ᵢ β) : Bijective h :=
  h.toEquiv.bijective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (h : α ≃ᵢ β)
  statement: Injective h
  proof: h.toEquiv.injective

中文:
定理 injective
  条件: (h : α ≃ᵢ β)
  结论: 单射 h
  证明: h.toEquiv.injective
-/
protected theorem injective (h : α ≃ᵢ β) : Injective h :=
  h.toEquiv.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (h : α ≃ᵢ β)
  statement: Surjective h
  proof: h.toEquiv.surjective

中文:
定理 surjective
  条件: (h : α ≃ᵢ β)
  结论: 满射 h
  证明: h.toEquiv.surjective
-/
protected theorem surjective (h : α ≃ᵢ β) : Surjective h :=
  h.toEquiv.surjective

/--
theorem `edist_eq` / 定理 `edist_eq`

English:
theorem edist_eq
  given: (h : α ≃ᵢ β) (x y : α)
  statement: edist (h x) (h y) = edist x y
  proof: h.isometry.edist_eq x y

中文:
定理 edist_eq
  条件: (h : α ≃ᵢ β) (x y : α)
  结论: edist (h x) (h y) = edist x y
  证明: h.isometry.edist_eq x y
-/
protected theorem edist_eq (h : α ≃ᵢ β) (x y : α) : edist (h x) (h y) = edist x y :=
  h.isometry.edist_eq x y

/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  statement: {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)
  proof: h.isometry.dist_eq x y

中文:
定理 dist_eq
  结论: {α β : 类型} [伪度量空间 α] [伪度量空间 β] (h : α ≃ᵢ β)
  证明: h.isometry.dist_eq x y
-/
protected theorem dist_eq {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)
    (x y : α) : dist (h x) (h y) = dist x y :=
  h.isometry.dist_eq x y

/--
theorem `nndist_eq` / 定理 `nndist_eq`

English:
theorem nndist_eq
  statement: {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)
  proof: h.isometry.nndist_eq x y

中文:
定理 nndist_eq
  结论: {α β : 类型} [伪度量空间 α] [伪度量空间 β] (h : α ≃ᵢ β)
  证明: h.isometry.nndist_eq x y
-/
protected theorem nndist_eq {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)
    (x y : α) : nndist (h x) (h y) = nndist x y :=
  h.isometry.nndist_eq x y

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (h : α ≃ᵢ β)
  statement: Continuous h
  proof: h.isometry.continuous

@[simp]

中文:
定理 continuous
  条件: (h : α ≃ᵢ β)
  结论: 连续 h
  证明: h.isometry.continuous

@[simp]
-/
protected theorem continuous (h : α ≃ᵢ β) : Continuous h :=
  h.isometry.continuous

@[simp]
/--
theorem `ediam_image` / 定理 `ediam_image`

English:
theorem ediam_image
  given: (h : α ≃ᵢ β) (s : Set α)
  statement: Metric.ediam (h '' s) = Metric.ediam s
  proof: h.isometry.ediam_image s

@[ext]

中文:
定理 ediam_image
  条件: (h : α ≃ᵢ β) (s : 集合 α)
  结论: Metric.ediam (h '' s) = Metric.ediam s
  证明: h.isometry.ediam_image s

@[ext]

Depends on / 依赖: ediam_image, h.isometry.ediam_image, isometry
-/
theorem ediam_image (h : α ≃ᵢ β) (s : Set α) : Metric.ediam (h '' s) = Metric.ediam s :=
  h.isometry.ediam_image s

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃h₁ h₂
  statement: α ≃ᵢ β⦄ (H : forall x, h₁ x = h₂ x) : h₁ = h₂
  proof: DFunLike.ext _ _ H

中文:
定理 ext
  条件: ⦃h₁ h₂
  结论: α ≃ᵢ β⦄ (H : 对任意 x, h₁ x = h₂ x) : h₁ = h₂
  证明: DFunLike.ext _ _ H

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : forall x, h₁ x = h₂ x) : h₁ = h₂ :=
  DFunLike.ext _ _ H

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: {α : Type u} [EMetricSpace α] (f : α -> β) (g : β -> α) (hfg : forall x, f (g x) = x)
  body: f
  invFun := g
left_inv _ := hf.injective hfg _
  right_inv := hfg
  isometry_toFun := hf

中文:
定义 mk'
  签名: {α : 类型u} [广义度量空间 α] (f : α -> β) (g : β -> α) (hfg : 对任意 x, f (g x) = x)
  定义体: f
  invFun := g
left_inv _ := hf.injective hfg _
  right_inv := hfg
  isometry_toFun := hf
-/
def mk' {α : Type u} [EMetricSpace α] (f : α -> β) (g : β -> α) (hfg : forall x, f (g x) = x)
    (hf : Isometry f) : α ≃ᵢ β where
  toFun := f
  invFun := g
left_inv _ := hf.injective hfg _
  right_inv := hfg
  isometry_toFun := hf

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (α : Type*) [PseudoEMetricSpace α]
  body: { Equiv.refl α with isometry_toFun := isometry_id }

中文:
定义 refl
  签名: (α : 类型) [PseudoEMetric空间 α]
  定义体: { Equiv.refl α with isometry_toFun := isometry_id }
-/
protected def refl (α : Type*) [PseudoEMetricSpace α] : α ≃ᵢ α :=
  { Equiv.refl α with isometry_toFun := isometry_id }

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ)
  body: { Equiv.trans h₁.toEquiv h₂.toEquiv with
    isometry_toFun := h₂.isometry_toFun.comp h₁.isometry_toFun }

@[simp]

中文:
定义 trans
  签名: (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ)
  定义体: { Equiv.trans h₁.toEquiv h₂.toEquiv with
    isometry_toFun := h₂.isometry_toFun.comp h₁.isometry_toFun }

@[simp]
-/
protected def trans (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
  { Equiv.trans h₁.toEquiv h₂.toEquiv with
    isometry_toFun := h₂.isometry_toFun.comp h₁.isometry_toFun }

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α)
  statement: h₁.trans h₂ x = h₂ (h₁ x)
  proof: rfl

中文:
定理 trans_apply
  条件: (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α)
  结论: h₁.trans h₂ x = h₂ (h₁ x)
  证明: rfl
-/
theorem trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α) : h₁.trans h₂ x = h₂ (h₁ x) :=
  rfl

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (h : α ≃ᵢ β)
  body: h.isometry.right_inv h.right_inv
  toEquiv := h.toEquiv.symm

中文:
定义 symm
  签名: (h : α ≃ᵢ β)
  定义体: h.isometry.right_inv h.right_inv
  toEquiv := h.toEquiv.symm
-/
protected def symm (h : α ≃ᵢ β) : β ≃ᵢ α where
  isometry_toFun := h.isometry.right_inv h.right_inv
  toEquiv := h.toEquiv.symm

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : α ≃ᵢ β)
  body: h

中文:
定义 Simps.apply
  签名: (h : α ≃ᵢ β)
  定义体: h
-/
def Simps.apply (h : α ≃ᵢ β) : α -> β := h

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (h : α ≃ᵢ β)
  body: h.symm

initialize_simps_projections IsometryEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]

中文:
定义 Simps.symm_apply
  签名: (h : α ≃ᵢ β)
  定义体: h.symm

initialize_simps_projections IsometryEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
-/
def Simps.symm_apply (h : α ≃ᵢ β) : β -> α :=
  h.symm

initialize_simps_projections IsometryEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
/--
theorem `coe_symm_toEquiv` / 定理 `coe_symm_toEquiv`

English:
theorem coe_symm_toEquiv
  given: (h : α ≃ᵢ β)
  statement: ⇑h.toEquiv.symm = h.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toEquiv
  条件: (h : α ≃ᵢ β)
  结论: ⇑h.toEquiv.symm = h.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toEquiv (h : α ≃ᵢ β) : ⇑h.toEquiv.symm = h.symm := rfl

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (h : α ≃ᵢ β)
  statement: h.symm.symm = h
  proof: rfl

中文:
定理 symm_symm
  条件: (h : α ≃ᵢ β)
  结论: h.symm.symm = h
  证明: rfl
-/
theorem symm_symm (h : α ≃ᵢ β) : h.symm.symm = h := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Bijective (IsometryEquiv.symm : (α ≃ᵢ β) -> β ≃ᵢ α)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: 双射 (等距等价.symm : (α ≃ᵢ β) -> β ≃ᵢ α)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Bijective (IsometryEquiv.symm : (α ≃ᵢ β) -> β ≃ᵢ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (h : α ≃ᵢ β) (y : β)
  statement: h (h.symm y) = y
  proof: h.toEquiv.apply_symm_apply y

@[simp]

中文:
定理 apply_symm_apply
  条件: (h : α ≃ᵢ β) (y : β)
  结论: h (h.symm y) = y
  证明: h.toEquiv.apply_symm_apply y

@[simp]

Depends on / 依赖: apply_symm_apply, h.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (h : α ≃ᵢ β) (y : β) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (h : α ≃ᵢ β) (x : α)
  statement: h.symm (h x) = x
  proof: h.toEquiv.symm_apply_apply x

中文:
定理 symm_apply_apply
  条件: (h : α ≃ᵢ β) (x : α)
  结论: h.symm (h x) = x
  证明: h.toEquiv.symm_apply_apply x

Depends on / 依赖: h.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (h : α ≃ᵢ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (h : α ≃ᵢ β) {x : α} {y : β}
  statement: h.symm y = x ↔ y = h x
  proof: h.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (h : α ≃ᵢ β) {x : α} {y : β}
  结论: h.symm y = x ↔ y = h x
  证明: h.toEquiv.symm_apply_eq

Depends on / 依赖: h.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (h : α ≃ᵢ β) {x : α} {y : β} : h.symm y = x ↔ y = h x :=
  h.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (h : α ≃ᵢ β) {x : α} {y : β}
  statement: x = h.symm y ↔ h x = y
  proof: h.toEquiv.eq_symm_apply

中文:
定理 eq_symm_apply
  条件: (h : α ≃ᵢ β) {x : α} {y : β}
  结论: x = h.symm y ↔ h x = y
  证明: h.toEquiv.eq_symm_apply

Depends on / 依赖: eq_symm_apply, h.toEquiv.eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (h : α ≃ᵢ β) {x : α} {y : β} : x = h.symm y ↔ h x = y :=
  h.toEquiv.eq_symm_apply

/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (h : α ≃ᵢ β)
  statement: (h.symm : β -> α) ∘ h = id
  proof: funext h.left_inv

中文:
定理 symm_comp_self
  条件: (h : α ≃ᵢ β)
  结论: (h.symm : β -> α) ∘ h = id
  证明: funext h.left_inv

Depends on / 依赖: h.left_inv, left_inv
-/
theorem symm_comp_self (h : α ≃ᵢ β) : (h.symm : β -> α) ∘ h = id := funext h.left_inv

/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (h : α ≃ᵢ β)
  statement: (h : α -> β) ∘ h.symm = id
  proof: funext h.right_inv

中文:
定理 self_comp_symm
  条件: (h : α ≃ᵢ β)
  结论: (h : α -> β) ∘ h.symm = id
  证明: funext h.right_inv

Depends on / 依赖: h.right_inv, right_inv
-/
theorem self_comp_symm (h : α ≃ᵢ β) : (h : α -> β) ∘ h.symm = id := funext h.right_inv

/--
theorem `range_eq_univ` / 定理 `range_eq_univ`

English:
theorem range_eq_univ
  given: (h : α ≃ᵢ β)
  statement: range h = univ
  proof: by simp

中文:
定理 range_eq_univ
  条件: (h : α ≃ᵢ β)
  结论: range h = univ
  证明: by simp
-/
theorem range_eq_univ (h : α ≃ᵢ β) : range h = univ := by simp

/--
theorem `image_symm` / 定理 `image_symm`

English:
theorem image_symm
  given: (h : α ≃ᵢ β)
  statement: image h.symm = preimage h
  proof: image_eq_preimage_of_inverse h.symm.toEquiv.left_inv h.symm.toEquiv.right_inv

中文:
定理 image_symm
  条件: (h : α ≃ᵢ β)
  结论: 像 h.symm = 原像 h
  证明: image_eq_preimage_of_inverse h.symm.toEquiv.left_inv h.symm.toEquiv.right_inv

Depends on / 依赖: h.symm.toEquiv.left_inv, h.symm.toEquiv.right_inv, image_eq_preimage_of_inverse, left_inv, right_inv, toEquiv
-/
theorem image_symm (h : α ≃ᵢ β) : image h.symm = preimage h :=
  image_eq_preimage_of_inverse h.symm.toEquiv.left_inv h.symm.toEquiv.right_inv

/--
theorem `preimage_symm` / 定理 `preimage_symm`

English:
theorem preimage_symm
  given: (h : α ≃ᵢ β)
  statement: preimage h.symm = image h
  proof: (image_eq_preimage_of_inverse h.toEquiv.left_inv h.toEquiv.right_inv).symm

@[simp]

中文:
定理 preimage_symm
  条件: (h : α ≃ᵢ β)
  结论: 原像 h.symm = 像 h
  证明: (image_eq_preimage_of_inverse h.toEquiv.left_inv h.toEquiv.right_inv).symm

@[simp]

Depends on / 依赖: h.toEquiv.left_inv, h.toEquiv.right_inv, image_eq_preimage_of_inverse, left_inv, right_inv, toEquiv
-/
theorem preimage_symm (h : α ≃ᵢ β) : preimage h.symm = image h :=
  (image_eq_preimage_of_inverse h.toEquiv.left_inv h.toEquiv.right_inv).symm

@[simp]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ)
  proof: rfl

中文:
定理 symm_trans_apply
  条件: (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ)
  证明: rfl
-/
theorem symm_trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ) :
    (h₁.trans h₂).symm x = h₁.symm (h₂.symm x) :=
  rfl

/--
theorem `ediam_univ` / 定理 `ediam_univ`

English:
theorem ediam_univ
  given: (h : α ≃ᵢ β)
  statement: Metric.ediam (univ : Set α) = Metric.ediam (univ : Set β)
  proof: by
  rw [← h.range_eq_univ]; rw [h.isometry.ediam_range]

@[simp]

中文:
定理 ediam_univ
  条件: (h : α ≃ᵢ β)
  结论: Metric.ediam (univ : 集合 α) = Metric.ediam (univ : 集合 β)
  证明: by
  rw [← h.range_eq_univ]; rw [h.isometry.ediam_range]

@[simp]

Depends on / 依赖: ediam_range, h.isometry.ediam_range, h.range_eq_univ, isometry, range_eq_univ
-/
theorem ediam_univ (h : α ≃ᵢ β) : Metric.ediam (univ : Set α) = Metric.ediam (univ : Set β) := by
  rw [← h.range_eq_univ]; rw [h.isometry.ediam_range]

@[simp]
/--
theorem `ediam_preimage` / 定理 `ediam_preimage`

English:
theorem ediam_preimage
  given: (h : α ≃ᵢ β) (s : Set β)
  statement: Metric.ediam (h ⁻¹' s) = Metric.ediam s
  proof: by
  rw [← image_symm]; rw [ediam_image]

@[simp]

中文:
定理 ediam_preimage
  条件: (h : α ≃ᵢ β) (s : 集合 β)
  结论: Metric.ediam (h ⁻¹' s) = Metric.ediam s
  证明: by
  rw [← image_symm]; rw [ediam_image]

@[simp]

Depends on / 依赖: ediam_image, image_symm
-/
theorem ediam_preimage (h : α ≃ᵢ β) (s : Set β) : Metric.ediam (h ⁻¹' s) = Metric.ediam s := by
  rw [← image_symm]; rw [ediam_image]

@[simp]
/--
theorem `preimage_eball` / 定理 `preimage_eball`

English:
theorem preimage_eball
  given: (h : α ≃ᵢ β) (x : β) (r : Real>=0∞)
  proof: by
  rw [← h.isometry.preimage_eball (h.symm x) r]; rw [h.apply_symm_apply]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_ball := preimage_eball

@[simp]

中文:
定理 preimage_eball
  条件: (h : α ≃ᵢ β) (x : β) (r : 实数>=0∞)
  证明: by
  rw [← h.isometry.preimage_eball (h.symm x) r]; rw [h.apply_symm_apply]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_ball := preimage_eball

@[simp]

Depends on / 依赖: apply_symm_apply, h.apply_symm_apply, h.isometry.preimage_eball, h.symm, isometry, preimage_eball
-/
theorem preimage_eball (h : α ≃ᵢ β) (x : β) (r : Real>=0∞) :
    h ⁻¹' Metric.eball x r = Metric.eball (h.symm x) r := by
  rw [← h.isometry.preimage_eball (h.symm x) r]; rw [h.apply_symm_apply]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_ball := preimage_eball

@[simp]
/--
theorem `preimage_closedEBall` / 定理 `preimage_closedEBall`

English:
theorem preimage_closedEBall
  given: (h : α ≃ᵢ β) (x : β) (r : Real>=0∞)
  proof: by
  rw [← h.isometry.preimage_closedEBall (h.symm x) r]; rw [h.apply_symm_apply]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_closedBall := preimage_closedEBall

@[simp]

中文:
定理 preimage_closedEBall
  条件: (h : α ≃ᵢ β) (x : β) (r : 实数>=0∞)
  证明: by
  rw [← h.isometry.preimage_closedEBall (h.symm x) r]; rw [h.apply_symm_apply]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_closedBall := preimage_closedEBall

@[simp]

Depends on / 依赖: apply_symm_apply, h.apply_symm_apply, h.isometry.preimage_closedEBall, h.symm, isometry, preimage_closedEBall
-/
theorem preimage_closedEBall (h : α ≃ᵢ β) (x : β) (r : Real>=0∞) :
    h ⁻¹' Metric.closedEBall x r = Metric.closedEBall (h.symm x) r := by
  rw [← h.isometry.preimage_closedEBall (h.symm x) r]; rw [h.apply_symm_apply]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_closedBall := preimage_closedEBall

@[simp]
/--
theorem `image_eball` / 定理 `image_eball`

English:
theorem image_eball
  given: (h : α ≃ᵢ β) (x : α) (r : Real>=0∞)
  proof: by
  rw [← h.preimage_symm]; rw [h.symm.preimage_eball]; rw [symm_symm]

@[deprecated (since := "2026-01-24")]
alias image_emetric_ball := image_eball

@[simp]

中文:
定理 image_eball
  条件: (h : α ≃ᵢ β) (x : α) (r : 实数>=0∞)
  证明: by
  rw [← h.preimage_symm]; rw [h.symm.preimage_eball]; rw [symm_symm]

@[deprecated (since := "2026-01-24")]
alias image_emetric_ball := image_eball

@[simp]

Depends on / 依赖: h.preimage_symm, h.symm.preimage_eball, preimage_eball, preimage_symm, symm_symm
-/
theorem image_eball (h : α ≃ᵢ β) (x : α) (r : Real>=0∞) :
    h '' Metric.eball x r = Metric.eball (h x) r := by
  rw [← h.preimage_symm]; rw [h.symm.preimage_eball]; rw [symm_symm]

@[deprecated (since := "2026-01-24")]
alias image_emetric_ball := image_eball

@[simp]
/--
theorem `image_closedEBall` / 定理 `image_closedEBall`

English:
theorem image_closedEBall
  given: (h : α ≃ᵢ β) (x : α) (r : Real>=0∞)
  proof: by
  rw [← h.preimage_symm]; rw [h.symm.preimage_closedEBall]; rw [symm_symm]

@[deprecated (since := "2026-01-24")]
alias image_emetric_closedBall := image_closedEBall

中文:
定理 image_closedEBall
  条件: (h : α ≃ᵢ β) (x : α) (r : 实数>=0∞)
  证明: by
  rw [← h.preimage_symm]; rw [h.symm.preimage_closedEBall]; rw [symm_symm]

@[deprecated (since := "2026-01-24")]
alias image_emetric_closedBall := image_closedEBall

Depends on / 依赖: h.preimage_symm, h.symm.preimage_closedEBall, preimage_closedEBall, preimage_symm, symm_symm
-/
theorem image_closedEBall (h : α ≃ᵢ β) (x : α) (r : Real>=0∞) :
    h '' Metric.closedEBall x r = Metric.closedEBall (h x) r := by
  rw [← h.preimage_symm]; rw [h.symm.preimage_closedEBall]; rw [symm_symm]

@[deprecated (since := "2026-01-24")]
alias image_emetric_closedBall := image_closedEBall

/-- The (bundled) homeomorphism associated to an isometric isomorphism. -/
@[simps toEquiv]
/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: (h : α ≃ᵢ β)
  body: h.continuous
  continuous_invFun := h.symm.continuous
  toEquiv := h.toEquiv

@[simp]

中文:
定义 toHomeomorph
  签名: (h : α ≃ᵢ β)
  定义体: h.continuous
  continuous_invFun := h.symm.continuous
  toEquiv := h.toEquiv

@[simp]
-/
protected def toHomeomorph (h : α ≃ᵢ β) : α ≃ₜ β where
  continuous_toFun := h.continuous
  continuous_invFun := h.symm.continuous
  toEquiv := h.toEquiv

@[simp]
/--
theorem `coe_toHomeomorph` / 定理 `coe_toHomeomorph`

English:
theorem coe_toHomeomorph
  given: (h : α ≃ᵢ β)
  statement: ⇑h.toHomeomorph = h
  proof: rfl

@[simp]

中文:
定理 coe_toHomeomorph
  条件: (h : α ≃ᵢ β)
  结论: ⇑h.toHomeomorph = h
  证明: rfl

@[simp]
-/
theorem coe_toHomeomorph (h : α ≃ᵢ β) : ⇑h.toHomeomorph = h :=
  rfl

@[simp]
/--
theorem `coe_toHomeomorph_symm` / 定理 `coe_toHomeomorph_symm`

English:
theorem coe_toHomeomorph_symm
  given: (h : α ≃ᵢ β)
  statement: ⇑h.toHomeomorph.symm = h.symm
  proof: rfl

@[simp]

中文:
定理 coe_toHomeomorph_symm
  条件: (h : α ≃ᵢ β)
  结论: ⇑h.toHomeomorph.symm = h.symm
  证明: rfl

@[simp]
-/
theorem coe_toHomeomorph_symm (h : α ≃ᵢ β) : ⇑h.toHomeomorph.symm = h.symm :=
  rfl

@[simp]
/--
theorem `comp_continuousOn_iff` / 定理 `comp_continuousOn_iff`

English:
theorem comp_continuousOn_iff
  given: {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ -> α} {s : Set γ}
  proof: h.toHomeomorph.comp_continuousOn_iff _ _

@[simp]

中文:
定理 comp_continuousOn_iff
  条件: {γ} [拓扑空间 γ] (h : α ≃ᵢ β) {f : γ -> α} {s : 集合 γ}
  证明: h.toHomeomorph.comp_continuousOn_iff _ _

@[simp]

Depends on / 依赖: comp_continuousOn_iff, h.toHomeomorph.comp_continuousOn_iff, toHomeomorph
-/
theorem comp_continuousOn_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ -> α} {s : Set γ} :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.toHomeomorph.comp_continuousOn_iff _ _

@[simp]
/--
theorem `comp_continuous_iff` / 定理 `comp_continuous_iff`

English:
theorem comp_continuous_iff
  given: {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ -> α}
  proof: h.toHomeomorph.comp_continuous_iff

@[simp]

中文:
定理 comp_continuous_iff
  条件: {γ} [拓扑空间 γ] (h : α ≃ᵢ β) {f : γ -> α}
  证明: h.toHomeomorph.comp_continuous_iff

@[simp]

Depends on / 依赖: comp_continuous_iff, h.toHomeomorph.comp_continuous_iff, toHomeomorph
-/
theorem comp_continuous_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ -> α} :
    Continuous (h ∘ f) ↔ Continuous f :=
  h.toHomeomorph.comp_continuous_iff

@[simp]
/--
theorem `comp_continuous_iff'` / 定理 `comp_continuous_iff'`

English:
theorem comp_continuous_iff'
  given: {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : β -> γ}
  proof: h.toHomeomorph.comp_continuous_iff'

中文:
定理 comp_continuous_iff'
  条件: {γ} [拓扑空间 γ] (h : α ≃ᵢ β) {f : β -> γ}
  证明: h.toHomeomorph.comp_continuous_iff'

Depends on / 依赖: comp_continuous_iff, h.toHomeomorph.comp_continuous_iff, toHomeomorph
-/
theorem comp_continuous_iff' {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : β -> γ} :
    Continuous (f ∘ h) ↔ Continuous f :=
  h.toHomeomorph.comp_continuous_iff'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (α ≃ᵢ α)
  body: IsometryEquiv.refl _
  mul e₁ e₂ := e₂.trans e₁
  inv := IsometryEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel e := ext e.symm_apply_apply

中文:
实例 :
  签名: 群 (α ≃ᵢ α)
  定义体: IsometryEquiv.refl _
  mul e₁ e₂ := e₂.trans e₁
  inv := IsometryEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel e := ext e.symm_apply_apply

Depends on / 依赖: IsometryEquiv, IsometryEquiv.refl
-/
instance : Group (α ≃ᵢ α) where
  one := IsometryEquiv.refl _
  mul e₁ e₂ := e₂.trans e₁
  inv := IsometryEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel e := ext e.symm_apply_apply

/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : α ≃ᵢ α) = id
  proof: rfl

中文:
定理 coe_one
  结论: ⇑(1 : α ≃ᵢ α) = id
  证明: rfl
-/
@[simp] theorem coe_one : ⇑(1 : α ≃ᵢ α) = id := rfl

/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (e₁ e₂ : α ≃ᵢ α)
  statement: ⇑(e₁ * e₂) = e₁ ∘ e₂
  proof: rfl

中文:
定理 coe_mul
  条件: (e₁ e₂ : α ≃ᵢ α)
  结论: ⇑(e₁ * e₂) = e₁ ∘ e₂
  证明: rfl
-/
@[simp] theorem coe_mul (e₁ e₂ : α ≃ᵢ α) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (e₁ e₂ : α ≃ᵢ α) (x : α)
  statement: (e₁ * e₂) x = e₁ (e₂ x)
  proof: rfl

中文:
定理 mul_apply
  条件: (e₁ e₂ : α ≃ᵢ α) (x : α)
  结论: (e₁ * e₂) x = e₁ (e₂ x)
  证明: rfl
-/
theorem mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

/--
theorem `inv_apply_self` / 定理 `inv_apply_self`

English:
theorem inv_apply_self
  given: (e : α ≃ᵢ α) (x : α)
  statement: e⁻¹ (e x) = x
  proof: e.symm_apply_apply x

中文:
定理 inv_apply_self
  条件: (e : α ≃ᵢ α) (x : α)
  结论: e⁻¹ (e x) = x
  证明: e.symm_apply_apply x
-/
@[simp] theorem inv_apply_self (e : α ≃ᵢ α) (x : α) : e⁻¹ (e x) = x := e.symm_apply_apply x

/--
theorem `apply_inv_self` / 定理 `apply_inv_self`

English:
theorem apply_inv_self
  given: (e : α ≃ᵢ α) (x : α)
  statement: e (e⁻¹ x) = x
  proof: e.apply_symm_apply x

中文:
定理 apply_inv_self
  条件: (e : α ≃ᵢ α) (x : α)
  结论: e (e⁻¹ x) = x
  证明: e.apply_symm_apply x
-/
@[simp] theorem apply_inv_self (e : α ≃ᵢ α) (x : α) : e (e⁻¹ x) = x := e.apply_symm_apply x

/--
theorem `completeSpace_iff` / 定理 `completeSpace_iff`

English:
theorem completeSpace_iff
  given: (e : α ≃ᵢ β)
  statement: CompleteSpace α ↔ CompleteSpace β
  proof: by
  simp only [completeSpace_iff_isComplete_univ, ← e.range_eq_univ, ← image_univ,
    isComplete_image_iff e.isometry.isUniformInducing]

中文:
定理 completeSpace_iff
  条件: (e : α ≃ᵢ β)
  结论: 完备空间 α ↔ 完备空间 β
  证明: by
  simp only [completeSpace_iff_isComplete_univ, ← e.range_eq_univ, ← image_univ,
    isComplete_image_iff e.isometry.isUniformInducing]

Depends on / 依赖: completeSpace_iff_isComplete_univ, e.isometry.isUniformInducing, e.range_eq_univ, image_univ, isComplete_image_iff, isUniformInducing, isometry, range_eq_univ
-/
theorem completeSpace_iff (e : α ≃ᵢ β) : CompleteSpace α ↔ CompleteSpace β := by
  simp only [completeSpace_iff_isComplete_univ, ← e.range_eq_univ, ← image_univ,
    isComplete_image_iff e.isometry.isUniformInducing]

/--
theorem `completeSpace` / 定理 `completeSpace`

English:
theorem completeSpace
  given: [CompleteSpace β] (e : α ≃ᵢ β)
  statement: CompleteSpace α
  proof: e.completeSpace_iff.2 ‹_›

中文:
定理 completeSpace
  条件: [完备空间 β] (e : α ≃ᵢ β)
  结论: 完备空间 α
  证明: e.completeSpace_iff.2 ‹_›
-/
protected theorem completeSpace [CompleteSpace β] (e : α ≃ᵢ β) : CompleteSpace α :=
  e.completeSpace_iff.2 ‹_›

/-- The natural isometry `∀ i, Y i ≃ᵢ ∀ j, Y (e.symm j)` obtained from a bijection `ι ≃ ι'` of
fintypes. `Equiv.piCongrLeft'` as an `IsometryEquiv`. -/
@[simps!]
/--
Definition of `piCongrLeft'` / `piCongrLeft'` 的定义

English:
definition piCongrLeft'
  signature: {ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι -> Type*}
  body: Equiv.piCongrLeft' _ e
  isometry_toFun x1 x2 := by
    simp_rw [edist_pi_def, Finset.sup_univ_eq_iSup]
    exact (Equiv.iSup_comp (g := fun b => edist (x1 b) (x2 b)) e.symm)

#adaptation_note

中文:
定义 piCongrLeft'
  签名: {ι' : 类型} [有限类型 ι] [有限类型 ι'] {Y : ι -> 类型}
  定义体: Equiv.piCongrLeft' _ e
  isometry_toFun x1 x2 := by
    simp_rw [edist_pi_def, Finset.sup_univ_eq_iSup]
    exact (Equiv.iSup_comp (g := fun b => edist (x1 b) (x2 b)) e.symm)

#adaptation_note

Depends on / 依赖: Equiv.piCongrLeft, piCongrLeft
-/
def piCongrLeft' {ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι -> Type*}
    [forall j, PseudoEMetricSpace (Y j)] (e : ι ≃ ι') : (forall i, Y i) ≃ᵢ forall j, Y (e.symm j) where
  toEquiv := Equiv.piCongrLeft' _ e
  isometry_toFun x1 x2 := by
    simp_rw [edist_pi_def, Finset.sup_univ_eq_iSup]
    exact (Equiv.iSup_comp (g := fun b => edist (x1 b) (x2 b)) e.symm)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural isometry `∀ i, Y (e i) ≃ᵢ ∀ j, Y j` obtained from a bijection `ι ≃ ι'` of fintypes.
`Equiv.piCongrLeft` as an `IsometryEquiv`. -/
@[simps!]
/--
Definition of `piCongrLeft` / `piCongrLeft` 的定义

English:
definition piCongrLeft
  signature: {ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι' -> Type*}
  body: (piCongrLeft' e.symm).symm

中文:
定义 piCongrLeft
  签名: {ι' : 类型} [有限类型 ι] [有限类型 ι'] {Y : ι' -> 类型}
  定义体: (piCongrLeft' e.symm).symm

Depends on / 依赖: e.symm, piCongrLeft
-/
def piCongrLeft {ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι' -> Type*}
    [forall j, PseudoEMetricSpace (Y j)] (e : ι ≃ ι') : (forall i, Y (e i)) ≃ᵢ forall j, Y j :=
  (piCongrLeft' e.symm).symm

/-- The natural isometry `(α ⊕ β → γ) ≃ᵢ (α → γ) × (β → γ)` between the type of maps on a sum of
fintypes `α ⊕ β` and the pairs of functions on the types `α` and `β`.
`Equiv.sumArrowEquivProdArrow` as an `IsometryEquiv`. -/
@[simps!]
/--
Definition of `sumArrowIsometryEquivProdArrow` / `sumArrowIsometryEquivProdArrow` 的定义

English:
definition sumArrowIsometryEquivProdArrow
  signature: [Fintype α] [Fintype β]
  body: Equiv.sumArrowEquivProdArrow _ _ _
  isometry_toFun _ _ := by simp [Prod.edist_eq, edist_pi_def, Finset.sup_univ_eq_iSup, iSup_sum]

@[simp]

中文:
定义 sumArrowIsometryEquivProdArrow
  签名: [有限类型 α] [有限类型 β]
  定义体: Equiv.sumArrowEquivProdArrow _ _ _
  isometry_toFun _ _ := by simp [Prod.edist_eq, edist_pi_def, Finset.sup_univ_eq_iSup, iSup_sum]

@[simp]

Depends on / 依赖: Equiv.sumArrowEquivProdArrow, sumArrowEquivProdArrow
-/
def sumArrowIsometryEquivProdArrow [Fintype α] [Fintype β] : (α oplus β -> γ) ≃ᵢ (α -> γ) × (β -> γ) where
  toEquiv := Equiv.sumArrowEquivProdArrow _ _ _
  isometry_toFun _ _ := by simp [Prod.edist_eq, edist_pi_def, Finset.sup_univ_eq_iSup, iSup_sum]

@[simp]
/--
theorem `sumArrowIsometryEquivProdArrow_toHomeomorph` / 定理 `sumArrowIsometryEquivProdArrow_toHomeomorph`

English:
theorem sumArrowIsometryEquivProdArrow_toHomeomorph
  given: {α β : Type*} [Fintype α] [Fintype β]
  proof: rfl

中文:
定理 sumArrowIsometryEquivProdArrow_toHomeomorph
  条件: {α β : 类型} [有限类型 α] [有限类型 β]
  证明: rfl
-/
theorem sumArrowIsometryEquivProdArrow_toHomeomorph {α β : Type*} [Fintype α] [Fintype β] :
    sumArrowIsometryEquivProdArrow.toHomeomorph
    = Homeomorph.sumArrowHomeomorphProdArrow (ι := α) (ι' := β) (X := γ) :=
  rfl

/--
theorem `_root_.Fin.edist_append_eq_max_edist` / 定理 `_root_.Fin.edist_append_eq_max_edist`

English:
theorem _root_.Fin.edist_append_eq_max_edist
  given: (m n : Nat) {x x2 : Fin m -> α} {y y2 : Fin n -> α}
  proof: by
  simp [edist_pi_def, Finset.sup_univ_eq_iSup, ← Equiv.iSup_comp (e := finSumFinEquiv),
    iSup_sum]

中文:
定理 _root_.有限集.edist_append_eq_max_edist
  条件: (m n : 自然数) {x x2 : 有限集 m -> α} {y y2 : 有限集 n -> α}
  证明: by
  simp [edist_pi_def, Finset.sup_univ_eq_iSup, ← Equiv.iSup_comp (e := finSumFinEquiv),
    iSup_sum]

Depends on / 依赖: Equiv.iSup_comp, Finset, Finset.sup_univ_eq_iSup, edist_pi_def, finSumFinEquiv, iSup_comp, iSup_sum, sup_univ_eq_iSup
-/
theorem _root_.Fin.edist_append_eq_max_edist (m n : Nat) {x x2 : Fin m -> α} {y y2 : Fin n -> α} :
    edist (Fin.append x y) (Fin.append x2 y2) = max (edist x x2) (edist y y2) := by
  simp [edist_pi_def, Finset.sup_univ_eq_iSup, ← Equiv.iSup_comp (e := finSumFinEquiv),
    iSup_sum]

/-- The natural `IsometryEquiv` between `(Fin m → α) × (Fin n → α)` and `Fin (m + n) → α`.
`Fin.appendEquiv` as an `IsometryEquiv`. -/
@[simps!]
/--
Definition of `_root_.Fin.appendIsometry` / `_root_.Fin.appendIsometry` 的定义

English:
definition _root_.Fin.appendIsometry
  signature: (m n : Nat)
  body: Fin.appendEquiv _ _
  isometry_toFun _ _ := by simp_rw [Fin.appendEquiv, Fin.edist_append_eq_max_edist, Prod.edist_eq]

@[simp]

中文:
定义 _root_.有限集.appendIsometry
  签名: (m n : 自然数)
  定义体: Fin.appendEquiv _ _
  isometry_toFun _ _ := by simp_rw [Fin.appendEquiv, Fin.edist_append_eq_max_edist, Prod.edist_eq]

@[simp]

Depends on / 依赖: Fin.appendEquiv, appendEquiv
-/
def _root_.Fin.appendIsometry (m n : Nat) : (Fin m -> α) × (Fin n -> α) ≃ᵢ (Fin (m + n) -> α) where
  toEquiv := Fin.appendEquiv _ _
  isometry_toFun _ _ := by simp_rw [Fin.appendEquiv, Fin.edist_append_eq_max_edist, Prod.edist_eq]

@[simp]
/--
theorem `_root_.Fin.appendIsometry_toHomeomorph` / 定理 `_root_.Fin.appendIsometry_toHomeomorph`

English:
theorem _root_.Fin.appendIsometry_toHomeomorph
  given: (m n : Nat)
  proof: rfl

#adaptation_note

中文:
定理 _root_.有限集.appendIsometry_toHomeomorph
  条件: (m n : 自然数)
  证明: rfl

#adaptation_note
-/
theorem _root_.Fin.appendIsometry_toHomeomorph (m n : Nat) :
    (Fin.appendIsometry m n).toHomeomorph = Fin.appendHomeomorph (X := α) m n :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural `IsometryEquiv` `(Fin m → ℝ) × (Fin l → ℝ) ≃ᵢ (Fin n → ℝ)` when `m + l = n`. -/
@[simps!]
/--
Definition of `_root_.Fin.appendIsometryOfEq` / `_root_.Fin.appendIsometryOfEq` 的定义

English:
definition _root_.Fin.appendIsometryOfEq
  signature: {n m l : Nat} (hmln : m + l = n)
  body: (Fin.appendIsometry m l).trans (IsometryEquiv.piCongrLeft (Y := fun _ => α) (finCongr hmln))

中文:
定义 _root_.有限集.appendIsometryOfEq
  签名: {n m l : 自然数} (hmln : m + l = n)
  定义体: (Fin.appendIsometry m l).trans (IsometryEquiv.piCongrLeft (Y := fun _ => α) (finCongr hmln))

Depends on / 依赖: Fin.appendIsometry, IsometryEquiv, IsometryEquiv.piCongrLeft, appendIsometry, finCongr, piCongrLeft
-/
def _root_.Fin.appendIsometryOfEq {n m l : Nat} (hmln : m + l = n) :
    (Fin m -> α) × (Fin l -> α) ≃ᵢ (Fin n -> α) :=
  (Fin.appendIsometry m l).trans (IsometryEquiv.piCongrLeft (Y := fun _ => α) (finCongr hmln))

variable (ι α)

/-- `Equiv.funUnique` as an `IsometryEquiv`. -/
@[simps!]
/--
Definition of `funUnique` / `funUnique` 的定义

English:
definition funUnique
  signature: [Unique ι] [Fintype ι]
  body: Equiv.funUnique ι α
  isometry_toFun x hx := by simp [edist_pi_def, Finset.univ_unique, Finset.sup_singleton]

中文:
定义 funUnique
  签名: [唯一 ι] [有限类型 ι]
  定义体: Equiv.funUnique ι α
  isometry_toFun x hx := by simp [edist_pi_def, Finset.univ_unique, Finset.sup_singleton]

Depends on / 依赖: Equiv.funUnique, funUnique
-/
def funUnique [Unique ι] [Fintype ι] : (ι -> α) ≃ᵢ α where
  toEquiv := Equiv.funUnique ι α
  isometry_toFun x hx := by simp [edist_pi_def, Finset.univ_unique, Finset.sup_singleton]

/-- `piFinTwoEquiv` as an `IsometryEquiv`. -/
@[simps!]
/--
Definition of `piFinTwo` / `piFinTwo` 的定义

English:
definition piFinTwo
  signature: (α : Fin 2 -> Type*) [forall i, PseudoEMetricSpace (α i)]
  body: piFinTwoEquiv α
  isometry_toFun x hx := by simp [edist_pi_def, Fin.univ_succ, Prod.edist_eq]

中文:
定义 piFinTwo
  签名: (α : 有限集 2 -> 类型) [对任意 i, PseudoEMetric空间 (α i)]
  定义体: piFinTwoEquiv α
  isometry_toFun x hx := by simp [edist_pi_def, Fin.univ_succ, Prod.edist_eq]

Depends on / 依赖: piFinTwoEquiv
-/
def piFinTwo (α : Fin 2 -> Type*) [forall i, PseudoEMetricSpace (α i)] : (forall i, α i) ≃ᵢ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  isometry_toFun x hx := by simp [edist_pi_def, Fin.univ_succ, Prod.edist_eq]

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)

@[simp]
/--
theorem `diam_image` / 定理 `diam_image`

English:
theorem diam_image
  given: (s : Set α)
  statement: Metric.diam (h '' s) = Metric.diam s
  proof: h.isometry.diam_image s

@[simp]

中文:
定理 diam_image
  条件: (s : 集合 α)
  结论: Metric.diam (h '' s) = Metric.diam s
  证明: h.isometry.diam_image s

@[simp]

Depends on / 依赖: diam_image, h.isometry.diam_image, isometry
-/
theorem diam_image (s : Set α) : Metric.diam (h '' s) = Metric.diam s :=
  h.isometry.diam_image s

@[simp]
/--
theorem `diam_preimage` / 定理 `diam_preimage`

English:
theorem diam_preimage
  given: (s : Set β)
  statement: Metric.diam (h ⁻¹' s) = Metric.diam s
  proof: by
  rw [← image_symm]; rw [diam_image]

include h in

中文:
定理 diam_preimage
  条件: (s : 集合 β)
  结论: Metric.diam (h ⁻¹' s) = Metric.diam s
  证明: by
  rw [← image_symm]; rw [diam_image]

include h in

Depends on / 依赖: diam_image, image_symm
-/
theorem diam_preimage (s : Set β) : Metric.diam (h ⁻¹' s) = Metric.diam s := by
  rw [← image_symm]; rw [diam_image]

include h in
/--
theorem `diam_univ` / 定理 `diam_univ`

English:
theorem diam_univ
  statement: Metric.diam (univ : Set α) = Metric.diam (univ : Set β)
  proof: congr_arg ENNReal.toReal h.ediam_univ

@[simp]

中文:
定理 diam_univ
  结论: Metric.diam (univ : 集合 α) = Metric.diam (univ : 集合 β)
  证明: congr_arg ENNReal.toReal h.ediam_univ

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toReal, congr_arg, ediam_univ, h.ediam_univ, toReal
-/
theorem diam_univ : Metric.diam (univ : Set α) = Metric.diam (univ : Set β) :=
  congr_arg ENNReal.toReal h.ediam_univ

@[simp]
/--
theorem `preimage_ball` / 定理 `preimage_ball`

English:
theorem preimage_ball
  given: (h : α ≃ᵢ β) (x : β) (r : Real)
  proof: by
  rw [← h.isometry.preimage_ball (h.symm x) r]; rw [h.apply_symm_apply]

@[simp]

中文:
定理 preimage_ball
  条件: (h : α ≃ᵢ β) (x : β) (r : 实数)
  证明: by
  rw [← h.isometry.preimage_ball (h.symm x) r]; rw [h.apply_symm_apply]

@[simp]

Depends on / 依赖: apply_symm_apply, h.apply_symm_apply, h.isometry.preimage_ball, h.symm, isometry, preimage_ball
-/
theorem preimage_ball (h : α ≃ᵢ β) (x : β) (r : Real) :
    h ⁻¹' Metric.ball x r = Metric.ball (h.symm x) r := by
  rw [← h.isometry.preimage_ball (h.symm x) r]; rw [h.apply_symm_apply]

@[simp]
/--
theorem `preimage_sphere` / 定理 `preimage_sphere`

English:
theorem preimage_sphere
  given: (h : α ≃ᵢ β) (x : β) (r : Real)
  proof: by
  rw [← h.isometry.preimage_sphere (h.symm x) r]; rw [h.apply_symm_apply]

@[simp]

中文:
定理 preimage_sphere
  条件: (h : α ≃ᵢ β) (x : β) (r : 实数)
  证明: by
  rw [← h.isometry.preimage_sphere (h.symm x) r]; rw [h.apply_symm_apply]

@[simp]

Depends on / 依赖: apply_symm_apply, h.apply_symm_apply, h.isometry.preimage_sphere, h.symm, isometry, preimage_sphere
-/
theorem preimage_sphere (h : α ≃ᵢ β) (x : β) (r : Real) :
    h ⁻¹' Metric.sphere x r = Metric.sphere (h.symm x) r := by
  rw [← h.isometry.preimage_sphere (h.symm x) r]; rw [h.apply_symm_apply]

@[simp]
/--
theorem `preimage_closedBall` / 定理 `preimage_closedBall`

English:
theorem preimage_closedBall
  given: (h : α ≃ᵢ β) (x : β) (r : Real)
  proof: by
  rw [← h.isometry.preimage_closedBall (h.symm x) r]; rw [h.apply_symm_apply]

@[simp]

中文:
定理 preimage_closedBall
  条件: (h : α ≃ᵢ β) (x : β) (r : 实数)
  证明: by
  rw [← h.isometry.preimage_closedBall (h.symm x) r]; rw [h.apply_symm_apply]

@[simp]

Depends on / 依赖: apply_symm_apply, h.apply_symm_apply, h.isometry.preimage_closedBall, h.symm, isometry, preimage_closedBall
-/
theorem preimage_closedBall (h : α ≃ᵢ β) (x : β) (r : Real) :
    h ⁻¹' Metric.closedBall x r = Metric.closedBall (h.symm x) r := by
  rw [← h.isometry.preimage_closedBall (h.symm x) r]; rw [h.apply_symm_apply]

@[simp]
/--
theorem `image_ball` / 定理 `image_ball`

English:
theorem image_ball
  given: (h : α ≃ᵢ β) (x : α) (r : Real)
  statement: h '' Metric.ball x r = Metric.ball (h x) r
  proof: by
  rw [← h.preimage_symm]; rw [h.symm.preimage_ball]; rw [symm_symm]

@[simp]

中文:
定理 image_ball
  条件: (h : α ≃ᵢ β) (x : α) (r : 实数)
  结论: h '' Metric.ball x r = Metric.ball (h x) r
  证明: by
  rw [← h.preimage_symm]; rw [h.symm.preimage_ball]; rw [symm_symm]

@[simp]

Depends on / 依赖: h.preimage_symm, h.symm.preimage_ball, preimage_ball, preimage_symm, symm_symm
-/
theorem image_ball (h : α ≃ᵢ β) (x : α) (r : Real) : h '' Metric.ball x r = Metric.ball (h x) r := by
  rw [← h.preimage_symm]; rw [h.symm.preimage_ball]; rw [symm_symm]

@[simp]
/--
theorem `image_sphere` / 定理 `image_sphere`

English:
theorem image_sphere
  given: (h : α ≃ᵢ β) (x : α) (r : Real)
  proof: by
  rw [← h.preimage_symm]; rw [h.symm.preimage_sphere]; rw [symm_symm]

@[simp]

中文:
定理 image_sphere
  条件: (h : α ≃ᵢ β) (x : α) (r : 实数)
  证明: by
  rw [← h.preimage_symm]; rw [h.symm.preimage_sphere]; rw [symm_symm]

@[simp]

Depends on / 依赖: h.preimage_symm, h.symm.preimage_sphere, preimage_sphere, preimage_symm, symm_symm
-/
theorem image_sphere (h : α ≃ᵢ β) (x : α) (r : Real) :
    h '' Metric.sphere x r = Metric.sphere (h x) r := by
  rw [← h.preimage_symm]; rw [h.symm.preimage_sphere]; rw [symm_symm]

@[simp]
/--
theorem `image_closedBall` / 定理 `image_closedBall`

English:
theorem image_closedBall
  given: (h : α ≃ᵢ β) (x : α) (r : Real)
  proof: by
  rw [← h.preimage_symm]; rw [h.symm.preimage_closedBall]; rw [symm_symm]

中文:
定理 image_closedBall
  条件: (h : α ≃ᵢ β) (x : α) (r : 实数)
  证明: by
  rw [← h.preimage_symm]; rw [h.symm.preimage_closedBall]; rw [symm_symm]

Depends on / 依赖: h.preimage_symm, h.symm.preimage_closedBall, preimage_closedBall, preimage_symm, symm_symm
-/
theorem image_closedBall (h : α ≃ᵢ β) (x : α) (r : Real) :
    h '' Metric.closedBall x r = Metric.closedBall (h x) r := by
  rw [← h.preimage_symm]; rw [h.symm.preimage_closedBall]; rw [symm_symm]

end PseudoMetricSpace

end IsometryEquiv

/-- An isometry induces an isometric isomorphism between the source space and the
range of the isometry. -/
@[simps! +simpRhs toEquiv apply]
/--
Definition of `Isometry.isometryEquivOnRange` / `Isometry.isometryEquivOnRange` 的定义

English:
definition Isometry.isometryEquivOnRange
  signature: [EMetricSpace α] [PseudoEMetricSpace β] {f : α -> β}
  body: h
  toEquiv := Equiv.ofInjective f h.injective

中文:
定义 等距.isometryEquivOnRange
  签名: [广义度量空间 α] [PseudoEMetric空间 β] {f : α -> β}
  定义体: h
  toEquiv := Equiv.ofInjective f h.injective
-/
def Isometry.isometryEquivOnRange [EMetricSpace α] [PseudoEMetricSpace β] {f : α -> β}
    (h : Isometry f) : α ≃ᵢ range f where
  isometry_toFun := h
  toEquiv := Equiv.ofInjective f h.injective

open NNReal in
/--
lemma `Isometry.lipschitzWith_iff` / 引理 `Isometry.lipschitzWith_iff`

English:
lemma Isometry.lipschitzWith_iff
  statement: {α β γ : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: by
  simp [LipschitzWith, h.edist_eq]

中文:
引理 等距.lipschitzWith_iff
  结论: {α β γ : 类型} [PseudoEMetric空间 α] [PseudoEMetric空间 β]
  证明: by
  simp [LipschitzWith, h.edist_eq]

Depends on / 依赖: LipschitzWith, edist_eq, h.edist_eq
-/
lemma Isometry.lipschitzWith_iff {α β γ : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    [PseudoEMetricSpace γ] {f : α -> β} {g : β -> γ} (K : Real>=0) (h : Isometry g) :
    LipschitzWith K (g ∘ f) ↔ LipschitzWith K f := by
  simp [LipschitzWith, h.edist_eq]

namespace IsometryClass

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [EquivLike F α β] [IsometryClass F α β]

/-- Turn an element of a type `F` satisfying `EquivLike F α β` and `IsometryClass F α β` into
an actual `IsometryEquiv`. This is declared as the default coercion from `F` to `α ≃ᵢ β`. -/
@[coe]
/--
Definition of `toIsometryEquiv` / `toIsometryEquiv` 的定义

English:
definition toIsometryEquiv
  signature: (f : F)
  body: { (f : α ≃ β) with
    isometry_toFun := IsometryClass.isometry f }

@[simp]

中文:
定义 toIsometryEquiv
  签名: (f : F)
  定义体: { (f : α ≃ β) with
    isometry_toFun := IsometryClass.isometry f }

@[simp]

Depends on / 依赖: IsometryClass, IsometryClass.isometry, isometry, isometry_toFun
-/
def toIsometryEquiv (f : F) : α ≃ᵢ β :=
  { (f : α ≃ β) with
    isometry_toFun := IsometryClass.isometry f }

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (f : F)
  statement: ⇑(toIsometryEquiv f) = ⇑f
  proof: rfl

中文:
定理 coe_coe
  条件: (f : F)
  结论: ⇑(toIsometryEquiv f) = ⇑f
  证明: rfl
-/
theorem coe_coe (f : F) : ⇑(toIsometryEquiv f) = ⇑f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut F (α ≃ᵢ β)
  body: ⟨toIsometryEquiv⟩

中文:
实例 :
  签名: CoeOut F (α ≃ᵢ β)
  定义体: ⟨toIsometryEquiv⟩

Depends on / 依赖: toIsometryEquiv
-/
instance : CoeOut F (α ≃ᵢ β) :=
  ⟨toIsometryEquiv⟩

/--
theorem `toIsometryEquiv_injective` / 定理 `toIsometryEquiv_injective`

English:
theorem toIsometryEquiv_injective
  statement: Function.Injective ((↑) : F -> α ≃ᵢ β)
  proof: fun _ _ e => DFunLike.ext _ _ fun a => DFunLike.congr_fun e a

中文:
定理 toIsometryEquiv_injective
  结论: 函数.单射 ((↑) : F -> α ≃ᵢ β)
  证明: fun _ _ e => DFunLike.ext _ _ fun a => DFunLike.congr_fun e a

Depends on / 依赖: DFunLike, DFunLike.congr_fun, DFunLike.ext, congr_fun
-/
theorem toIsometryEquiv_injective : Function.Injective ((↑) : F -> α ≃ᵢ β) :=
  fun _ _ e => DFunLike.ext _ _ fun a => DFunLike.congr_fun e a

end IsometryClass
