/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Rat
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.MetricSpace.DilationEquiv
import Mathlib.Analysis.Normed.MulAction

/-!
# Normed fields

In this file we continue building the theory of normed division rings and fields.

Some useful results that relate the topology of the normed field to the discrete topology include:
* `discreteTopology_or_nontriviallyNormedField`
* `discreteTopology_of_bddAbove_range_norm`

-/

@[expose] public section

-- Guard against import creep.
assert_not_exists RestrictScalars

variable {α β ι : Type*}

open Filter Bornology Metric
open scoped Topology NNReal Pointwise Uniformity

section NormedDivisionRing

variable [NormedDivisionRing α]

/-- Multiplication by a nonzero element `a` on the left
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
/--
Definition of `DilationEquiv.mulLeft` / `DilationEquiv.mulLeft` 的定义

English:
definition DilationEquiv.mulLeft
  signature: (a : α) (ha : a != 0)
  body: Dilation.mulLeft a ha
  toEquiv := Equiv.mulLeft₀ a ha

中文:
定义 DilationEquiv.mulLeft
  签名: (a : α) (ha : a != 0)
  定义体: Dilation.mulLeft a ha
  toEquiv := Equiv.mulLeft₀ a ha

Depends on / 依赖: Dilation, Dilation.mulLeft, mulLeft
-/
def DilationEquiv.mulLeft (a : α) (ha : a != 0) : α ≃ᵈ α where
  __ := Dilation.mulLeft a ha
  toEquiv := Equiv.mulLeft₀ a ha

/-- Multiplication by a nonzero element `a` on the right
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
/--
Definition of `DilationEquiv.mulRight` / `DilationEquiv.mulRight` 的定义

English:
definition DilationEquiv.mulRight
  signature: (a : α) (ha : a != 0)
  body: Dilation.mulRight a ha
  toEquiv := Equiv.mulRight₀ a ha

中文:
定义 DilationEquiv.mulRight
  签名: (a : α) (ha : a != 0)
  定义体: Dilation.mulRight a ha
  toEquiv := Equiv.mulRight₀ a ha

Depends on / 依赖: Dilation, Dilation.mulRight, mulRight
-/
def DilationEquiv.mulRight (a : α) (ha : a != 0) : α ≃ᵈ α where
  __ := Dilation.mulRight a ha
  toEquiv := Equiv.mulRight₀ a ha

namespace Filter

@[simp]
/--
lemma `map_mul_left_cobounded` / 引理 `map_mul_left_cobounded`

English:
lemma map_mul_left_cobounded
  given: {a : α} (ha : a != 0)
  proof: DilationEquiv.map_cobounded (DilationEquiv.mulLeft a ha)

@[simp]

中文:
引理 map_mul_left_cobounded
  条件: {a : α} (ha : a != 0)
  证明: DilationEquiv.map_cobounded (DilationEquiv.mulLeft a ha)

@[simp]

Depends on / 依赖: DilationEquiv, DilationEquiv.map_cobounded, DilationEquiv.mulLeft, map_cobounded, mulLeft
-/
lemma map_mul_left_cobounded {a : α} (ha : a != 0) :
    map (a * ·) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulLeft a ha)

@[simp]
/--
lemma `map_mul_right_cobounded` / 引理 `map_mul_right_cobounded`

English:
lemma map_mul_right_cobounded
  given: {a : α} (ha : a != 0)
  proof: DilationEquiv.map_cobounded (DilationEquiv.mulRight a ha)

中文:
引理 map_mul_right_cobounded
  条件: {a : α} (ha : a != 0)
  证明: DilationEquiv.map_cobounded (DilationEquiv.mulRight a ha)

Depends on / 依赖: DilationEquiv, DilationEquiv.map_cobounded, DilationEquiv.mulRight, map_cobounded, mulRight
-/
lemma map_mul_right_cobounded {a : α} (ha : a != 0) :
    map (· * a) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulRight a ha)

/--
theorem `tendsto_mul_left_cobounded` / 定理 `tendsto_mul_left_cobounded`

English:
theorem tendsto_mul_left_cobounded
  given: {a : α} (ha : a != 0)
  proof: (map_mul_left_cobounded ha).le

中文:
定理 tendsto_mul_left_cobounded
  条件: {a : α} (ha : a != 0)
  证明: (map_mul_left_cobounded ha).le

Depends on / 依赖: map_mul_left_cobounded
-/
theorem tendsto_mul_left_cobounded {a : α} (ha : a != 0) :
    Tendsto (a * ·) (cobounded α) (cobounded α) :=
  (map_mul_left_cobounded ha).le

/--
theorem `tendsto_mul_right_cobounded` / 定理 `tendsto_mul_right_cobounded`

English:
theorem tendsto_mul_right_cobounded
  given: {a : α} (ha : a != 0)
  proof: (map_mul_right_cobounded ha).le

@[simp]

中文:
定理 tendsto_mul_right_cobounded
  条件: {a : α} (ha : a != 0)
  证明: (map_mul_right_cobounded ha).le

@[simp]

Depends on / 依赖: map_mul_right_cobounded
-/
theorem tendsto_mul_right_cobounded {a : α} (ha : a != 0) :
    Tendsto (· * a) (cobounded α) (cobounded α) :=
  (map_mul_right_cobounded ha).le

@[simp]
/--
lemma `inv_cobounded₀` / 引理 `inv_cobounded₀`

English:
lemma inv_cobounded₀
  statement: (cobounded α)⁻¹ = 𝓝[!=] 0
  proof: by
  rw [← comap_norm_atTop]; rw [← Filter.comap_inv]; rw [← comap_norm_nhdsGT_zero]; rw [← inv_atTop₀]; rw [← Filter.comap_inv]
  simp only [comap_comap, Function.comp_def, norm_inv]

@[simp]

中文:
引理 inv_cobounded₀
  结论: (cobounded α)⁻¹ = 𝓝[!=] 0
  证明: by
  rw [← comap_norm_atTop]; rw [← Filter.comap_inv]; rw [← comap_norm_nhdsGT_zero]; rw [← inv_atTop₀]; rw [← Filter.comap_inv]
  simp only [comap_comap, Function.comp_def, norm_inv]

@[simp]

Depends on / 依赖: Filter, Filter.comap_inv, Function, Function.comp_def, comap_comap, comap_inv, comap_norm_atTop, comap_norm_nhdsGT_zero, comp_def, norm_inv
-/
lemma inv_cobounded₀ : (cobounded α)⁻¹ = 𝓝[!=] 0 := by
  rw [← comap_norm_atTop]; rw [← Filter.comap_inv]; rw [← comap_norm_nhdsGT_zero]; rw [← inv_atTop₀]; rw [← Filter.comap_inv]
  simp only [comap_comap, Function.comp_def, norm_inv]

@[simp]
/--
lemma `inv_nhdsNE_zero` / 引理 `inv_nhdsNE_zero`

English:
lemma inv_nhdsNE_zero
  statement: (𝓝[!=] (0 : α))⁻¹ = cobounded α
  proof: by
  rw [← inv_cobounded₀]; rw [inv_inv]

中文:
引理 inv_nhdsNE_zero
  结论: (𝓝[!=] (0 : α))⁻¹ = cobounded α
  证明: by
  rw [← inv_cobounded₀]; rw [inv_inv]

Depends on / 依赖: inv_inv
-/
lemma inv_nhdsNE_zero : (𝓝[!=] (0 : α))⁻¹ = cobounded α := by
  rw [← inv_cobounded₀]; rw [inv_inv]

/--
lemma `tendsto_inv₀_cobounded'` / 引理 `tendsto_inv₀_cobounded'`

English:
lemma tendsto_inv₀_cobounded'
  statement: Tendsto Inv.inv (cobounded α) (𝓝[!=] 0)
  proof: inv_cobounded₀.le

中文:
引理 tendsto_inv₀_cobounded'
  结论: Tendsto Inv.inv (cobounded α) (𝓝[!=] 0)
  证明: inv_cobounded₀.le
-/
lemma tendsto_inv₀_cobounded' : Tendsto Inv.inv (cobounded α) (𝓝[!=] 0) :=
  inv_cobounded₀.le

/--
theorem `tendsto_inv₀_cobounded` / 定理 `tendsto_inv₀_cobounded`

English:
theorem tendsto_inv₀_cobounded
  statement: Tendsto Inv.inv (cobounded α) (𝓝 0)
  proof: tendsto_inv₀_cobounded'.mono_right inf_le_left

中文:
定理 tendsto_inv₀_cobounded
  结论: Tendsto Inv.inv (cobounded α) (𝓝 0)
  证明: tendsto_inv₀_cobounded'.mono_right inf_le_left

Depends on / 依赖: inf_le_left, mono_right
-/
theorem tendsto_inv₀_cobounded : Tendsto Inv.inv (cobounded α) (𝓝 0) :=
  tendsto_inv₀_cobounded'.mono_right inf_le_left

/--
lemma `tendsto_inv₀_nhdsNE_zero` / 引理 `tendsto_inv₀_nhdsNE_zero`

English:
lemma tendsto_inv₀_nhdsNE_zero
  statement: Tendsto Inv.inv (𝓝[!=] 0) (cobounded α)
  proof: inv_nhdsNE_zero.le

中文:
引理 tendsto_inv₀_nhdsNE_zero
  结论: Tendsto Inv.inv (𝓝[!=] 0) (cobounded α)
  证明: inv_nhdsNE_zero.le

Depends on / 依赖: inv_nhdsNE_zero, inv_nhdsNE_zero.le
-/
lemma tendsto_inv₀_nhdsNE_zero : Tendsto Inv.inv (𝓝[!=] 0) (cobounded α) :=
  inv_nhdsNE_zero.le

end Filter

/--
theorem `uniformContinuousOn_inv₀` / 定理 `uniformContinuousOn_inv₀`

English:
theorem uniformContinuousOn_inv₀
  given: {s : Set α} (hs : sᶜ in 𝓝 0)
  proof: by
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  rcases NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp hs with ⟨r, hr₀, hr⟩
  simp only [Set.subset_compl_comm (t := s), Set.compl_ofPred, not_lt] at hr
have hs₀ : forall x in s, x != 0 := fun x hx => norm_pos_iff.mp hr₀.trans_le (hr hx)
 

中文:
定理 uniformContinuousOn_inv₀
  条件: {s : Set α} (hs : sᶜ in 𝓝 0)
  证明: by
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  rcases NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp hs with ⟨r, hr₀, hr⟩
  simp only [Set.subset_compl_comm (t := s), Set.compl_ofPred, not_lt] at hr
have hs₀ : forall x in s, x != 0 := fun x hx => norm_pos_iff.mp hr₀.trans_le (hr hx)
 

Depends on / 依赖: Metric, Metric.uniformContinuousOn_iff_le, NormedAddGroup, NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp, Set.compl_ofPred, Set.subset_compl_comm, compl_ofPred, dist_eq_norm, inv_sub_inv, mem_iff, nhds_zero_basis_norm_lt, norm_pos_iff, norm_pos_iff.mp, not_lt, subset_compl_comm, trans_le, uniformContinuousOn_iff_le
-/
theorem uniformContinuousOn_inv₀ {s : Set α} (hs : sᶜ in 𝓝 0) :
    UniformContinuousOn Inv.inv s := by
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  rcases NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp hs with ⟨r, hr₀, hr⟩
  simp only [Set.subset_compl_comm (t := s), Set.compl_ofPred, not_lt] at hr
have hs₀ : forall x in s, x != 0 := fun x hx => norm_pos_iff.mp hr₀.trans_le (hr hx)
  refine ⟨ε * r ^ 2, by positivity, fun x hx y hy hxy => ?_⟩
  calc
    dist x⁻¹ y⁻¹ = ‖x‖⁻¹ * dist y x * ‖y‖⁻¹ := by
      simp [dist_eq_norm, inv_sub_inv' (hs₀ x hx) (hs₀ y hy)]
    _ <= r⁻¹ * (ε * r ^ 2) * r⁻¹ := by
      rw [dist_comm]
      gcongr <;> exact hr ‹_›
    _ = ε := by field_simp

@[to_fun]
/--
theorem `UniformContinuousOn.inv₀` / 定理 `UniformContinuousOn.inv₀`

English:
theorem UniformContinuousOn.inv₀
  statement: {X : Type*} [UniformSpace X] {f : X -> α} {s : Set X}
  proof: .comp hf (Set.mapsTo_image f s) uniformContinuousOn_inv₀ hf₀

@[to_fun]

中文:
定理 UniformContinuousOn.inv₀
  结论: {X : 类型} [UniformSpace X] {f : X -> α} {s : Set X}
  证明: .comp hf (Set.mapsTo_image f s) uniformContinuousOn_inv₀ hf₀

@[to_fun]

Depends on / 依赖: Set.mapsTo_image, mapsTo_image
-/
theorem UniformContinuousOn.inv₀ {X : Type*} [UniformSpace X] {f : X -> α} {s : Set X}
    (hf : UniformContinuousOn f s) (hf₀ : (f '' s)ᶜ in 𝓝 0) :
    UniformContinuousOn f⁻¹ s :=
.comp hf (Set.mapsTo_image f s) uniformContinuousOn_inv₀ hf₀

@[to_fun]
/--
theorem `UniformContinuous.inv₀` / 定理 `UniformContinuous.inv₀`

English:
theorem UniformContinuous.inv₀
  statement: {X : Type*} [UniformSpace X] {f : X -> α}
  proof: by
  simp only [← uniformContinuousOn_univ, ← Set.image_univ] at *
  exact hf.inv₀ hf₀

@[to_fun]

中文:
定理 UniformContinuous.inv₀
  结论: {X : 类型} [UniformSpace X] {f : X -> α}
  证明: by
  simp only [← uniformContinuousOn_univ, ← Set.image_univ] at *
  exact hf.inv₀ hf₀

@[to_fun]

Depends on / 依赖: Set.image_univ, hf.inv, image_univ, uniformContinuousOn_univ
-/
theorem UniformContinuous.inv₀ {X : Type*} [UniformSpace X] {f : X -> α}
    (hf : UniformContinuous f) (hf₀ : (Set.range f)ᶜ in 𝓝 0) :
    UniformContinuous f⁻¹ := by
  simp only [← uniformContinuousOn_univ, ← Set.image_univ] at *
  exact hf.inv₀ hf₀

@[to_fun]
/--
theorem `TendstoLocallyUniformlyOn.inv₀_of_disjoint` / 定理 `TendstoLocallyUniformlyOn.inv₀_of_disjoint`

English:
theorem TendstoLocallyUniformlyOn.inv₀_of_disjoint
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
.disjoint_iff nhds_basis_ball .map _ rcases basis_sets _
.mp (hf x hx) with ⟨U, hUx, r, hr₀, hr⟩
  refine Tendsto.comp (uniformContinuousOn_inv₀ (s := (closedBall (0 : α) (r / 2))ᶜ)
    (by simp [closedBall_mem_nhds, hr₀])) <| 

中文:
定理 TendstoLocallyUniformlyOn.inv₀_of_disjoint
  结论: {X ι : 类型} [TopologicalSpace X]
  证明: by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
.disjoint_iff nhds_basis_ball .map _ rcases basis_sets _
.mp (hf x hx) with ⟨U, hUx, r, hr₀, hr⟩
  refine Tendsto.comp (uniformContinuousOn_inv₀ (s := (closedBall (0 : α) (r / 2))ᶜ)
    (by simp [closedBall_mem_nhds, hr₀])) <| 

Depends on / 依赖: Set.disjoint_left, Tendsto, Tendsto.comp, basis_sets, closedBall, closedBall_mem_nhds, disjoint_iff, disjoint_left, dist_mem_uniformity, filter_upwards, half_pos, nhds_basis_ball, tendstoLocallyUniformlyOn_iff_forall_tendsto, tendsto_inf, tendsto_inf.mpr, tendsto_principal, tendsto_principal.mpr, tendsto_snd
-/
theorem TendstoLocallyUniformlyOn.inv₀_of_disjoint {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι -> X -> α} {f : X -> α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hf : forall x in s, Disjoint (map f (𝓝[s] x)) (𝓝 0)) :
    TendstoLocallyUniformlyOn F⁻¹ f⁻¹ l s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
.disjoint_iff nhds_basis_ball .map _ rcases basis_sets _
.mp (hf x hx) with ⟨U, hUx, r, hr₀, hr⟩
  refine Tendsto.comp (uniformContinuousOn_inv₀ (s := (closedBall (0 : α) (r / 2))ᶜ)
    (by simp [closedBall_mem_nhds, hr₀])) <| tendsto_inf.mpr ⟨hF x hx, tendsto_principal.mpr ?_⟩
  filter_upwards [hF x hx (dist_mem_uniformity (half_pos hr₀)), tendsto_snd hUx] with y hy₁ hy₂
  have : r <= ‖f y.2‖ := by simp_all [Set.disjoint_left]
  have : r / 2 < ‖F y.1 y.2‖ := by
    simp [dist_eq_norm_sub] at hy₁
    linarith [hy₁, norm_sub_norm_le (f y.2) (F y.1 y.2)]
  simp_all [(half_lt_self hr₀).trans_le]

@[to_fun]
/--
theorem `TendstoLocallyUniformly.inv₀_of_disjoint` / 定理 `TendstoLocallyUniformly.inv₀_of_disjoint`

English:
theorem TendstoLocallyUniformly.inv₀_of_disjoint
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hF.inv₀_of_disjoint
  simpa

@[to_fun]

中文:
定理 TendstoLocallyUniformly.inv₀_of_disjoint
  结论: {X ι : 类型} [TopologicalSpace X]
  证明: by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hF.inv₀_of_disjoint
  simpa

@[to_fun]

Depends on / 依赖: hF.inv, tendstoLocallyUniformlyOn_univ
-/
theorem TendstoLocallyUniformly.inv₀_of_disjoint {X ι : Type*} [TopologicalSpace X]
    {F : ι -> X -> α} {f : X -> α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hf : forall x, Disjoint (map f (𝓝 x)) (𝓝 0)) :
    TendstoLocallyUniformly F⁻¹ f⁻¹ l := by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hF.inv₀_of_disjoint
  simpa

@[to_fun]
/--
theorem `TendstoLocallyUniformlyOn.inv₀` / 定理 `TendstoLocallyUniformlyOn.inv₀`

English:
theorem TendstoLocallyUniformlyOn.inv₀
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: .mono_left (hf x hx) hF.inv₀_of_disjoint fun x hx => disjoint_nhds_nhds.2 (hf₀ x hx)

@[to_fun]

中文:
定理 TendstoLocallyUniformlyOn.inv₀
  结论: {X ι : 类型} [TopologicalSpace X]
  证明: .mono_left (hf x hx) hF.inv₀_of_disjoint fun x hx => disjoint_nhds_nhds.2 (hf₀ x hx)

@[to_fun]

Depends on / 依赖: disjoint_nhds_nhds, hF.inv, mono_left
-/
theorem TendstoLocallyUniformlyOn.inv₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι -> X -> α} {f : X -> α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hf : ContinuousOn f s) (hf₀ : forall x in s, f x != 0) :
    TendstoLocallyUniformlyOn F⁻¹ f⁻¹ l s :=
.mono_left (hf x hx) hF.inv₀_of_disjoint fun x hx => disjoint_nhds_nhds.2 (hf₀ x hx)

@[to_fun]
/--
theorem `TendstoLocallyUniformly.inv₀` / 定理 `TendstoLocallyUniformly.inv₀`

English:
theorem TendstoLocallyUniformly.inv₀
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: .mono_left (hf.tendsto x) hF.inv₀_of_disjoint fun x => disjoint_nhds_nhds.2 (hf₀ x)

中文:
定理 TendstoLocallyUniformly.inv₀
  结论: {X ι : 类型} [TopologicalSpace X]
  证明: .mono_left (hf.tendsto x) hF.inv₀_of_disjoint fun x => disjoint_nhds_nhds.2 (hf₀ x)

Depends on / 依赖: disjoint_nhds_nhds, hF.inv, hf.tendsto, mono_left, tendsto
-/
theorem TendstoLocallyUniformly.inv₀ {X ι : Type*} [TopologicalSpace X]
    {F : ι -> X -> α} {f : X -> α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hf : Continuous f) (hf₀ : forall x, f x != 0) :
    TendstoLocallyUniformly F⁻¹ f⁻¹ l :=
.mono_left (hf.tendsto x) hF.inv₀_of_disjoint fun x => disjoint_nhds_nhds.2 (hf₀ x)

-- see Note [lower instance priority]
instance (priority := 100) NormedDivisionRing.to_continuousInv₀ : ContinuousInv₀ α where
  continuousAt_inv₀ x hx := by
    refine uniformContinuousOn_inv₀ (s := (Metric.closedBall x (‖x‖ / 2))) ?_
.continuousAt ?_ .continuousOn
    · refine Metric.isClosed_closedBall.isOpen_compl.mem_nhds ?_
      simpa
    · apply Metric.closedBall_mem_nhds
      simpa

@[to_fun]
/--
theorem `TendstoLocallyUniformlyOn.div₀` / 定理 `TendstoLocallyUniformlyOn.div₀`

English:
theorem TendstoLocallyUniformlyOn.div₀
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: by
  simp only [div_eq_mul_inv]
exact hF.mul₀ (hG.inv₀ hg hg₀) hf hg.inv₀ hg₀

@[to_fun]

中文:
定理 TendstoLocallyUniformlyOn.div₀
  结论: {X ι : 类型} [TopologicalSpace X]
  证明: by
  simp only [div_eq_mul_inv]
exact hF.mul₀ (hG.inv₀ hg hg₀) hf hg.inv₀ hg₀

@[to_fun]

Depends on / 依赖: div_eq_mul_inv, hF.mul, hG.inv, hg.inv
-/
theorem TendstoLocallyUniformlyOn.div₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F G : ι -> X -> α} {f g : X -> α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hg₀ : forall x in s, g x != 0) :
    TendstoLocallyUniformlyOn (F / G) (f / g) l s := by
  simp only [div_eq_mul_inv]
exact hF.mul₀ (hG.inv₀ hg hg₀) hf hg.inv₀ hg₀

@[to_fun]
/--
theorem `TendstoLocallyUniformly.div₀` / 定理 `TendstoLocallyUniformly.div₀`

English:
theorem TendstoLocallyUniformly.div₀
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: by
  simp only [div_eq_mul_inv]
exact hF.mul₀ (hG.inv₀ hg hg₀) hf hg.inv₀ hg₀

中文:
定理 TendstoLocallyUniformly.div₀
  结论: {X ι : 类型} [TopologicalSpace X]
  证明: by
  simp only [div_eq_mul_inv]
exact hF.mul₀ (hG.inv₀ hg hg₀) hf hg.inv₀ hg₀

Depends on / 依赖: div_eq_mul_inv, hF.mul, hG.inv, hg.inv
-/
theorem TendstoLocallyUniformly.div₀ {X ι : Type*} [TopologicalSpace X]
    {F G : ι -> X -> α} {f g : X -> α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : Continuous f) (hg : Continuous g) (hg₀ : forall x, g x != 0) :
    TendstoLocallyUniformly (F / G) (f / g) l := by
  simp only [div_eq_mul_inv]
exact hF.mul₀ (hG.inv₀ hg hg₀) hf hg.inv₀ hg₀

-- see Note [lower instance priority]
/-- A normed division ring is a topological division ring. -/
instance (priority := 100) NormedDivisionRing.to_isTopologicalDivisionRing :
    IsTopologicalDivisionRing α where

/--
lemma `tendsto_norm_inv_nhdsNE_zero_atTop` / 引理 `tendsto_norm_inv_nhdsNE_zero_atTop`

English:
lemma tendsto_norm_inv_nhdsNE_zero_atTop
  statement: Tendsto (fun x : α => ‖x⁻¹‖) (𝓝[!=] 0) atTop
  proof: tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero

中文:
引理 tendsto_norm_inv_nhdsNE_zero_atTop
  结论: Tendsto (fun x : α => ‖x⁻¹‖) (𝓝[!=] 0) atTop
  证明: tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero

Depends on / 依赖: tendsto_norm_cobounded_atTop, tendsto_norm_cobounded_atTop.comp
-/
lemma tendsto_norm_inv_nhdsNE_zero_atTop : Tendsto (fun x : α => ‖x⁻¹‖) (𝓝[!=] 0) atTop :=
  tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero

/--
lemma `tendsto_zpow_nhdsNE_zero_cobounded` / 引理 `tendsto_zpow_nhdsNE_zero_cobounded`

English:
lemma tendsto_zpow_nhdsNE_zero_cobounded
  given: {m : Int} (hm : m < 0)
  proof: by
  obtain ⟨m, rfl⟩ := neg_surjective m
  lift m to Nat using by lia
  simpa [Function.comp_def] using
    (tendsto_pow_cobounded_cobounded (by lia)).comp tendsto_inv₀_nhdsNE_zero

中文:
引理 tendsto_zpow_nhdsNE_zero_cobounded
  条件: {m : 整数} (hm : m < 0)
  证明: by
  obtain ⟨m, rfl⟩ := neg_surjective m
  lift m to Nat using by lia
  simpa [Function.comp_def] using
    (tendsto_pow_cobounded_cobounded (by lia)).comp tendsto_inv₀_nhdsNE_zero

Depends on / 依赖: Function, Function.comp_def, comp_def, neg_surjective, tendsto_pow_cobounded_cobounded
-/
lemma tendsto_zpow_nhdsNE_zero_cobounded {m : Int} (hm : m < 0) :
    Tendsto (· ^ m) (𝓝[!=] 0) (cobounded α) := by
  obtain ⟨m, rfl⟩ := neg_surjective m
  lift m to Nat using by lia
  simpa [Function.comp_def] using
    (tendsto_pow_cobounded_cobounded (by lia)).comp tendsto_inv₀_nhdsNE_zero

end NormedDivisionRing

namespace NormedField

/--
lemma `discreteTopology_or_nontriviallyNormedField` / 引理 `discreteTopology_or_nontriviallyNormedField`

English:
lemma discreteTopology_or_nontriviallyNormedField
  given: (𝕜 : Type*) [h : NormedField 𝕜]
  proof: by
  by_cases H : exists x : 𝕜, x != 0 ∧ ‖x‖ != 1
  · exact Or.inr ⟨(⟨NontriviallyNormedField.ofNormNeOne H, rfl⟩)⟩
  · simp_rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff, dist_eq_norm,
             sub_zero]
    refine Or.inl ⟨1, zero_lt_one, ?_⟩
    contrapose! H
    

中文:
引理 discreteTopology_or_nontriviallyNormedField
  条件: (𝕜 : 类型) [h : NormedField 𝕜]
  证明: by
  by_cases H : exists x : 𝕜, x != 0 ∧ ‖x‖ != 1
  · exact Or.inr ⟨(⟨NontriviallyNormedField.ofNormNeOne H, rfl⟩)⟩
  · simp_rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff, dist_eq_norm,
             sub_zero]
    refine Or.inl ⟨1, zero_lt_one, ?_⟩
    contrapose! H
    

Depends on / 依赖: H.imp, Metric, Metric.isOpen_singleton_iff, NontriviallyNormedField, NontriviallyNormedField.ofNormNeOne, Or.inl, Or.inr, contrapose, discreteTopology_iff_isOpen_singleton_zero, dist_eq_norm, isOpen_singleton_iff, ofNormNeOne, simp_rw, sub_zero, zero_lt_one
-/
lemma discreteTopology_or_nontriviallyNormedField (𝕜 : Type*) [h : NormedField 𝕜] :
    DiscreteTopology 𝕜 ∨ Nonempty ({h' : NontriviallyNormedField 𝕜 // h'.toNormedField = h}) := by
  by_cases H : exists x : 𝕜, x != 0 ∧ ‖x‖ != 1
  · exact Or.inr ⟨(⟨NontriviallyNormedField.ofNormNeOne H, rfl⟩)⟩
  · simp_rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff, dist_eq_norm,
             sub_zero]
    refine Or.inl ⟨1, zero_lt_one, ?_⟩
    contrapose! H
    refine H.imp ?_
    -- contextual to reuse the `a ≠ 0` hypothesis in the proof of `a ≠ 0 ∧ ‖a‖ ≠ 1`
    simp +contextual [ne_of_lt]

/--
lemma `discreteTopology_of_bddAbove_range_norm` / 引理 `discreteTopology_of_bddAbove_range_norm`

English:
lemma discreteTopology_of_bddAbove_range_norm
  statement: {𝕜 : Type*} [NormedField 𝕜]
  proof: by
  refine (NormedField.discreteTopology_or_nontriviallyNormedField _).resolve_right ?_
  rintro ⟨_, rfl⟩
  obtain ⟨x, h⟩ := h
  obtain ⟨k, hk⟩ := NormedField.exists_lt_norm 𝕜 x
  exact hk.not_ge (h (Set.mem_range_self k))

中文:
引理 discreteTopology_of_bddAbove_range_norm
  结论: {𝕜 : 类型} [NormedField 𝕜]
  证明: by
  refine (NormedField.discreteTopology_or_nontriviallyNormedField _).resolve_right ?_
  rintro ⟨_, rfl⟩
  obtain ⟨x, h⟩ := h
  obtain ⟨k, hk⟩ := NormedField.exists_lt_norm 𝕜 x
  exact hk.not_ge (h (Set.mem_range_self k))

Depends on / 依赖: NormedField, NormedField.discreteTopology_or_nontriviallyNormedField, NormedField.exists_lt_norm, Set.mem_range_self, discreteTopology_or_nontriviallyNormedField, exists_lt_norm, hk.not_ge, mem_range_self, not_ge, resolve_right
-/
lemma discreteTopology_of_bddAbove_range_norm {𝕜 : Type*} [NormedField 𝕜]
    (h : BddAbove (Set.range fun k : 𝕜 => ‖k‖)) :
    DiscreteTopology 𝕜 := by
  refine (NormedField.discreteTopology_or_nontriviallyNormedField _).resolve_right ?_
  rintro ⟨_, rfl⟩
  obtain ⟨x, h⟩ := h
  obtain ⟨k, hk⟩ := NormedField.exists_lt_norm 𝕜 x
  exact hk.not_ge (h (Set.mem_range_self k))

section Densely

variable (α) [DenselyNormedField α]

/--
theorem `denseRange_nnnorm` / 定理 `denseRange_nnnorm`

English:
theorem denseRange_nnnorm
  statement: DenseRange (nnnorm : α -> Real>=0)
  proof: dense_of_exists_between fun _ _ hr =>
    let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr
    ⟨‖x‖₊, ⟨x, rfl⟩, h⟩

中文:
定理 denseRange_nnnorm
  结论: DenseRange (nnnorm : α -> 实数>=0)
  证明: dense_of_exists_between fun _ _ hr =>
    let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr
    ⟨‖x‖₊, ⟨x, rfl⟩, h⟩

Depends on / 依赖: dense_of_exists_between, exists_lt_nnnorm_lt
-/
theorem denseRange_nnnorm : DenseRange (nnnorm : α -> Real>=0) :=
  dense_of_exists_between fun _ _ hr =>
    let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr
    ⟨‖x‖₊, ⟨x, rfl⟩, h⟩

end Densely

section NontriviallyNormedField
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Int} {x : 𝕜}

@[simp]
/--
lemma `continuousAt_zpow` / 引理 `continuousAt_zpow`

English:
lemma continuousAt_zpow
  statement: ContinuousAt (fun x => x ^ n) x ↔ x != 0 ∨ 0 <= n
  proof: by
  refine ⟨?_, continuousAt_zpow₀ _ _⟩
  contrapose!
  rintro ⟨rfl, hm⟩ hc
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).not_tendsto (Metric.disjoint_nhds_cobounded _)
    (tendsto_zpow_nhdsNE_zero_cobounded hm)

@[simp]

中文:
引理 continuousAt_zpow
  结论: ContinuousAt (fun x => x ^ n) x ↔ x != 0 ∨ 0 <= n
  证明: by
  refine ⟨?_, continuousAt_zpow₀ _ _⟩
  contrapose!
  rintro ⟨rfl, hm⟩ hc
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).not_tendsto (Metric.disjoint_nhds_cobounded _)
    (tendsto_zpow_nhdsNE_zero_cobounded hm)

@[simp]
-/
protected lemma continuousAt_zpow : ContinuousAt (fun x => x ^ n) x ↔ x != 0 ∨ 0 <= n := by
  refine ⟨?_, continuousAt_zpow₀ _ _⟩
  contrapose!
  rintro ⟨rfl, hm⟩ hc
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).not_tendsto (Metric.disjoint_nhds_cobounded _)
    (tendsto_zpow_nhdsNE_zero_cobounded hm)

@[simp]
/--
lemma `continuousAt_inv` / 引理 `continuousAt_inv`

English:
lemma continuousAt_inv
  statement: ContinuousAt Inv.inv x ↔ x != 0
  proof: by
  simpa using NormedField.continuousAt_zpow (n := -1) (x := x)

中文:
引理 continuousAt_inv
  结论: ContinuousAt Inv.inv x ↔ x != 0
  证明: by
  simpa using NormedField.continuousAt_zpow (n := -1) (x := x)
-/
protected lemma continuousAt_inv : ContinuousAt Inv.inv x ↔ x != 0 := by
  simpa using NormedField.continuousAt_zpow (n := -1) (x := x)

end NontriviallyNormedField
end NormedField

/--
Instance `Rat.instNormedField` / 实例 `Rat.instNormedField`

English:
instance Rat.instNormedField
  signature: : NormedField Rat where
  body: instField
  __ := instNormedAddCommGroup
  norm_mul a b := by simp only [norm, Rat.cast_mul, abs_mul]

中文:
实例 Rat.instNormedField
  签名: : NormedField Rat where
  定义体: instField
  __ := instNormedAddCommGroup
  norm_mul a b := by simp only [norm, Rat.cast_mul, abs_mul]

Depends on / 依赖: instField
-/
instance Rat.instNormedField : NormedField Rat where
  __ := instField
  __ := instNormedAddCommGroup
  norm_mul a b := by simp only [norm, Rat.cast_mul, abs_mul]

/--
Instance `Rat.instDenselyNormedField` / 实例 `Rat.instDenselyNormedField`

English:
instance Rat.instDenselyNormedField
  signature: : DenselyNormedField Rat where
  body: let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by rwa [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos (h₀.trans_lt h.1)]⟩

中文:
实例 Rat.instDenselyNormedField
  签名: : DenselyNormedField Rat where
  定义体: let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by rwa [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos (h₀.trans_lt h.1)]⟩

Depends on / 依赖: Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos, exists_rat_btwn, norm_cast_real, norm_eq_abs, trans_lt
-/
instance Rat.instDenselyNormedField : DenselyNormedField Rat where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by rwa [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos (h₀.trans_lt h.1)]⟩

section Complete

/--
lemma `NormedField.completeSpace_iff_isComplete_closedBall` / 引理 `NormedField.completeSpace_iff_isComplete_closedBall`

English:
lemma NormedField.completeSpace_iff_isComplete_closedBall
  given: {K : Type*} [NormedField K]
  proof: by
  constructor <;> intro h
  · exact Metric.isClosed_closedBall.isComplete
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with _ | ⟨_, rfl⟩
  · rwa [completeSpace_iff_isComplete_univ,
         ← NormedDivisionRing.unitClosedBall_eq_univ_of_discrete]
  refine Metric.complete_of_

中文:
引理 NormedField.completeSpace_iff_isComplete_closedBall
  条件: {K : 类型} [NormedField K]
  证明: by
  constructor <;> intro h
  · exact Metric.isClosed_closedBall.isComplete
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with _ | ⟨_, rfl⟩
  · rwa [completeSpace_iff_isComplete_univ,
         ← NormedDivisionRing.unitClosedBall_eq_univ_of_discrete]
  refine Metric.complete_of_

Depends on / 依赖: CauchySeq, Metric, Metric.complete_of_cauchySeq_tendsto, Metric.isClosed_closedBall.isComplete, NormedDivisionRing, NormedDivisionRing.unitClosedBall_eq_univ_of_discrete, NormedField, NormedField.discreteTopology_or_nontriviallyNormedField, NormedField.exists_lt_norm, _root_, _root_.norm_nonneg, completeSpace_iff_isComplete_univ, complete_of_cauchySeq_tendsto, discreteTopology_or_nontriviallyNormedField, exists_lt_norm, hu.norm_bddAbove, isClosed_closedBall, isComplete, norm_bddAbove, norm_nonneg
-/
lemma NormedField.completeSpace_iff_isComplete_closedBall {K : Type*} [NormedField K] :
    CompleteSpace K ↔ IsComplete (Metric.closedBall 0 1 : Set K) := by
  constructor <;> intro h
  · exact Metric.isClosed_closedBall.isComplete
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with _ | ⟨_, rfl⟩
  · rwa [completeSpace_iff_isComplete_univ,
         ← NormedDivisionRing.unitClosedBall_eq_univ_of_discrete]
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨k, hk⟩ := hu.norm_bddAbove
  have kpos : 0 <= k := (_root_.norm_nonneg (u 0)).trans (hk (by simp))
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm K k
  have hu' : CauchySeq ((· / x) ∘ u) := (uniformContinuous_div_const' x).comp_cauchySeq hu
  have hb : forall n, ((· / x) ∘ u) n in Metric.closedBall 0 1 := by
    intro
    simp only [Function.comp_apply, Metric.mem_closedBall, dist_zero_right, norm_div]
    rw [div_le_one (kpos.trans_lt hx)]
    exact hx.le.trans' (hk (by simp))
  obtain ⟨a, -, ha'⟩ := cauchySeq_tendsto_of_isComplete h hb hu'
  refine ⟨a * x, (((continuous_mul_const x).tendsto a).comp ha').congr ?_⟩
  have hx' : x != 0 := by
    contrapose! hx
    simp [hx, kpos]
  simp [div_mul_cancel₀ _ hx']

end Complete
