/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Topology on `ℝ≥0`

The basic lemmas for the natural topology on `ℝ≥0` .

## Main statements

Various mathematically trivial lemmas are proved about the compatibility
of limits and sums in `ℝ≥0` and `ℝ`. For example

* `tendsto_coe {f : Filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
  Filter.Tendsto (fun a, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ Filter.Tendsto m f (𝓝 x)`

says that the limit of a filter along a map to `ℝ≥0` is the same in `ℝ` and `ℝ≥0`, and

* `coe_tsum {f : α → ℝ≥0} : ((∑'a, f a) : ℝ) = (∑'a, (f a : ℝ))`

says that says that a sum of elements in `ℝ≥0` is the same in `ℝ` and `ℝ≥0`.

Similarly, some mathematically trivial lemmas about infinite sums are proved,
a few of which rely on the fact that subtraction is continuous.

-/

@[expose] public section

noncomputable section

open Filter Metric Set TopologicalSpace Topology

variable {ι : Sort*} {n : Nat}

namespace NNReal

variable {α : Type*} {L : SummationFilter α}

section coe

/--
lemma `isOpen_Ico_zero` / 引理 `isOpen_Ico_zero`

English:
lemma isOpen_Ico_zero
  given: {x : NNReal}
  statement: IsOpen (Set.Ico 0 x)
  proof: Ico_bot (a := x) ▸ isOpen_Iio

中文:
引理 isOpen_Ico_zero
  条件: {x : 非负实数}
  结论: 是开集 (集合.左闭右开区间 0 x)
  证明: Ico_bot (a := x) ▸ isOpen_Iio

Depends on / 依赖: Ico_bot, isOpen_Iio
-/
lemma isOpen_Ico_zero {x : NNReal} : IsOpen (Set.Ico 0 x) :=
  Ico_bot (a := x) ▸ isOpen_Iio

open Filter Finset

@[fun_prop]
/--
theorem `_root_.continuous_real_toNNReal` / 定理 `_root_.continuous_real_toNNReal`

English:
theorem _root_.continuous_real_toNNReal
  statement: Continuous Real.toNNReal
  proof: (continuous_id.max continuous_const).subtype_mk _

中文:
定理 _root_.continuous_real_toNN实数
  结论: 连续 实数.toNN实数
  证明: (continuous_id.max continuous_const).subtype_mk _

Depends on / 依赖: continuous_const, continuous_id, continuous_id.max, subtype_mk
-/
theorem _root_.continuous_real_toNNReal : Continuous Real.toNNReal :=
  (continuous_id.max continuous_const).subtype_mk _

/-- `Real.toNNReal` bundled as a continuous map for convenience. -/
@[simps -fullyApplied]
/--
Definition of `_root_.ContinuousMap.realToNNReal` / `_root_.ContinuousMap.realToNNReal` 的定义

English:
definition _root_.ContinuousMap.realToNNReal
  signature: : C(Real, Real>=0)
  body: .mk Real.toNNReal continuous_real_toNNReal

@[simp]

中文:
定义 _root_.连续映射.realToNN实数
  签名: : C(实数, 实数>=0)
  定义体: .mk Real.toNNReal continuous_real_toNNReal

@[simp]

Depends on / 依赖: Real.toNNReal, continuous_real_toNNReal, toNNReal
-/
noncomputable def _root_.ContinuousMap.realToNNReal : C(Real, Real>=0) :=
  .mk Real.toNNReal continuous_real_toNNReal

@[simp]
/--
theorem `map_coe_nhdsGT` / 定理 `map_coe_nhdsGT`

English:
theorem map_coe_nhdsGT
  given: (x : Real>=0)
  statement: (𝓝[>] x).map toReal = 𝓝[>] ↑x
  proof: by
  rw [isEmbedding_coe.map_nhdsWithin_eq]; rw [image_coe_Ioi]

@[simp]

中文:
定理 map_coe_nhdsGT
  条件: (x : 实数>=0)
  结论: (𝓝[>] x).map to实数 = 𝓝[>] ↑x
  证明: by
  rw [isEmbedding_coe.map_nhdsWithin_eq]; rw [image_coe_Ioi]

@[simp]

Depends on / 依赖: image_coe_Ioi, isEmbedding_coe, isEmbedding_coe.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem map_coe_nhdsGT (x : Real>=0) : (𝓝[>] x).map toReal = 𝓝[>] ↑x := by
  rw [isEmbedding_coe.map_nhdsWithin_eq]; rw [image_coe_Ioi]

@[simp]
/--
theorem `map_coe_nhdsGE` / 定理 `map_coe_nhdsGE`

English:
theorem map_coe_nhdsGE
  given: (x : Real>=0)
  statement: (𝓝[>=] x).map toReal = 𝓝[>=] ↑x
  proof: by
  rw [isEmbedding_coe.map_nhdsWithin_eq]; rw [image_coe_Ici]

中文:
定理 map_coe_nhdsGE
  条件: (x : 实数>=0)
  结论: (𝓝[>=] x).map to实数 = 𝓝[>=] ↑x
  证明: by
  rw [isEmbedding_coe.map_nhdsWithin_eq]; rw [image_coe_Ici]

Depends on / 依赖: image_coe_Ici, isEmbedding_coe, isEmbedding_coe.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem map_coe_nhdsGE (x : Real>=0) : (𝓝[>=] x).map toReal = 𝓝[>=] ↑x := by
  rw [isEmbedding_coe.map_nhdsWithin_eq]; rw [image_coe_Ici]

/--
lemma `_root_.ContinuousOn.ofReal_map_toNNReal` / 引理 `_root_.ContinuousOn.ofReal_map_toNNReal`

English:
lemma _root_.ContinuousOn.ofReal_map_toNNReal
  statement: {f : Real>=0 -> Real>=0} {s : Set Real} {t : Set Real>=0}
  proof: continuous_subtype_val.comp_continuousOn hf.comp continuous_real_toNNReal.continuousOn h

@[simp, norm_cast]

中文:
引理 _root_.ContinuousOn.of实数_map_toNN实数
  结论: {f : 实数>=0 -> 实数>=0} {s : 集合 实数} {t : 集合 实数>=0}
  证明: continuous_subtype_val.comp_continuousOn hf.comp continuous_real_toNNReal.continuousOn h

@[simp, norm_cast]

Depends on / 依赖: comp_continuousOn, continuousOn, continuous_real_toNNReal, continuous_real_toNNReal.continuousOn, continuous_subtype_val, continuous_subtype_val.comp_continuousOn, hf.comp
-/
lemma _root_.ContinuousOn.ofReal_map_toNNReal {f : Real>=0 -> Real>=0} {s : Set Real} {t : Set Real>=0}
    (hf : ContinuousOn f t) (h : Set.MapsTo Real.toNNReal s t) :
    ContinuousOn (fun x => f x.toNNReal : Real -> Real) s :=
continuous_subtype_val.comp_continuousOn hf.comp continuous_real_toNNReal.continuousOn h

@[simp, norm_cast]
/--
theorem `tendsto_coe` / 定理 `tendsto_coe`

English:
theorem tendsto_coe
  given: {f : Filter α} {m : α -> Real>=0} {x : Real>=0}
  proof: tendsto_subtype_rng.symm

中文:
定理 tendsto_coe
  条件: {f : 滤子 α} {m : α -> 实数>=0} {x : 实数>=0}
  证明: tendsto_subtype_rng.symm

Depends on / 依赖: tendsto_subtype_rng, tendsto_subtype_rng.symm
-/
theorem tendsto_coe {f : Filter α} {m : α -> Real>=0} {x : Real>=0} :
    Tendsto (fun a => (m a : Real)) f (𝓝 (x : Real)) ↔ Tendsto m f (𝓝 x) :=
  tendsto_subtype_rng.symm

/--
theorem `tendsto_coe'` / 定理 `tendsto_coe'`

English:
theorem tendsto_coe'
  given: {f : Filter α} [NeBot f] {m : α -> Real>=0} {x : Real}
  proof: ⟨fun h => ⟨ge_of_tendsto' h fun c => (m c).2, tendsto_coe.1 h⟩, fun ⟨_, hm⟩ => tendsto_coe.2 hm⟩

中文:
定理 tendsto_coe'
  条件: {f : 滤子 α} [NeBot f] {m : α -> 实数>=0} {x : 实数}
  证明: ⟨fun h => ⟨ge_of_tendsto' h fun c => (m c).2, tendsto_coe.1 h⟩, fun ⟨_, hm⟩ => tendsto_coe.2 hm⟩

Depends on / 依赖: ge_of_tendsto, tendsto_coe
-/
theorem tendsto_coe' {f : Filter α} [NeBot f] {m : α -> Real>=0} {x : Real} :
    Tendsto (fun a => m a : α -> Real) f (𝓝 x) ↔ exists hx : 0 <= x, Tendsto m f (𝓝 ⟨x, hx⟩) :=
  ⟨fun h => ⟨ge_of_tendsto' h fun c => (m c).2, tendsto_coe.1 h⟩, fun ⟨_, hm⟩ => tendsto_coe.2 hm⟩

/--
theorem `map_coe_atTop` / 定理 `map_coe_atTop`

English:
theorem map_coe_atTop
  statement: map toReal atTop = atTop
  proof: map_val_Ici_atTop 0

@[simp]

中文:
定理 map_coe_atTop
  结论: map to实数 atTop = atTop
  证明: map_val_Ici_atTop 0

@[simp]
-/
@[simp] theorem map_coe_atTop : map toReal atTop = atTop := map_val_Ici_atTop 0

@[simp]
/--
theorem `comap_coe_atTop` / 定理 `comap_coe_atTop`

English:
theorem comap_coe_atTop
  statement: comap toReal atTop = atTop
  proof: (atTop_Ici_eq 0).symm

@[simp, norm_cast]

中文:
定理 comap_coe_atTop
  结论: comap to实数 atTop = atTop
  证明: (atTop_Ici_eq 0).symm

@[simp, norm_cast]

Depends on / 依赖: atTop_Ici_eq
-/
theorem comap_coe_atTop : comap toReal atTop = atTop := (atTop_Ici_eq 0).symm

@[simp, norm_cast]
/--
theorem `tendsto_coe_atTop` / 定理 `tendsto_coe_atTop`

English:
theorem tendsto_coe_atTop
  given: {f : Filter α} {m : α -> Real>=0}
  proof: tendsto_Ici_atTop.symm

中文:
定理 tendsto_coe_atTop
  条件: {f : 滤子 α} {m : α -> 实数>=0}
  证明: tendsto_Ici_atTop.symm

Depends on / 依赖: tendsto_Ici_atTop, tendsto_Ici_atTop.symm
-/
theorem tendsto_coe_atTop {f : Filter α} {m : α -> Real>=0} :
    Tendsto (fun a => (m a : Real)) f atTop ↔ Tendsto m f atTop :=
  tendsto_Ici_atTop.symm

/--
theorem `_root_.tendsto_real_toNNReal` / 定理 `_root_.tendsto_real_toNNReal`

English:
theorem _root_.tendsto_real_toNNReal
  given: {f : Filter α} {m : α -> Real} {x : Real} (h : Tendsto m f (𝓝 x))
  proof: (continuous_real_toNNReal.tendsto _).comp h

@[simp]

中文:
定理 _root_.tendsto_real_toNN实数
  条件: {f : 滤子 α} {m : α -> 实数} {x : 实数} (h : 收敛 m f (𝓝 x))
  证明: (continuous_real_toNNReal.tendsto _).comp h

@[simp]

Depends on / 依赖: continuous_real_toNNReal, continuous_real_toNNReal.tendsto, tendsto
-/
theorem _root_.tendsto_real_toNNReal {f : Filter α} {m : α -> Real} {x : Real} (h : Tendsto m f (𝓝 x)) :
    Tendsto (fun a => Real.toNNReal (m a)) f (𝓝 (Real.toNNReal x)) :=
  (continuous_real_toNNReal.tendsto _).comp h

@[simp]
/--
theorem `_root_.Real.map_toNNReal_atTop` / 定理 `_root_.Real.map_toNNReal_atTop`

English:
theorem _root_.Real.map_toNNReal_atTop
  statement: map Real.toNNReal atTop = atTop
  proof: by
  rw [← map_coe_atTop]; rw [Function.LeftInverse.filter_map @Real.toNNReal_coe]

中文:
定理 _root_.实数.map_toNN实数_atTop
  结论: map 实数.toNN实数 atTop = atTop
  证明: by
  rw [← map_coe_atTop]; rw [Function.LeftInverse.filter_map @Real.toNNReal_coe]

Depends on / 依赖: Function, Function.LeftInverse.filter_map, LeftInverse, Real.toNNReal_coe, filter_map, map_coe_atTop, toNNReal_coe
-/
theorem _root_.Real.map_toNNReal_atTop : map Real.toNNReal atTop = atTop := by
  rw [← map_coe_atTop]; rw [Function.LeftInverse.filter_map @Real.toNNReal_coe]

/--
theorem `_root_.tendsto_real_toNNReal_atTop` / 定理 `_root_.tendsto_real_toNNReal_atTop`

English:
theorem _root_.tendsto_real_toNNReal_atTop
  statement: Tendsto Real.toNNReal atTop atTop
  proof: Real.map_toNNReal_atTop.le

@[simp]

中文:
定理 _root_.tendsto_real_toNN实数_atTop
  结论: 收敛 实数.toNN实数 atTop atTop
  证明: Real.map_toNNReal_atTop.le

@[simp]

Depends on / 依赖: Real.map_toNNReal_atTop.le, map_toNNReal_atTop
-/
theorem _root_.tendsto_real_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop :=
  Real.map_toNNReal_atTop.le

@[simp]
/--
theorem `_root_.Real.comap_toNNReal_atTop` / 定理 `_root_.Real.comap_toNNReal_atTop`

English:
theorem _root_.Real.comap_toNNReal_atTop
  statement: comap Real.toNNReal atTop = atTop
  proof: by
  refine le_antisymm ?_ tendsto_real_toNNReal_atTop.le_comap
  refine (atTop_basis_Ioi' 0).ge_iff.2 fun a ha => ?_
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop a.toNNReal)] with x hx
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg ha.le).1 hx

@[simp]

中文:
定理 _root_.实数.comap_toNN实数_atTop
  结论: comap 实数.toNN实数 atTop = atTop
  证明: by
  refine le_antisymm ?_ tendsto_real_toNNReal_atTop.le_comap
  refine (atTop_basis_Ioi' 0).ge_iff.2 fun a ha => ?_
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop a.toNNReal)] with x hx
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg ha.le).1 hx

@[simp]

Depends on / 依赖: Ioi_mem_atTop, Real.toNNReal_lt_toNNReal_iff_of_nonneg, a.toNNReal, atTop_basis_Ioi, filter_upwards, ge_iff, ha.le, le_antisymm, le_comap, preimage_mem_comap, tendsto_real_toNNReal_atTop, tendsto_real_toNNReal_atTop.le_comap, toNNReal, toNNReal_lt_toNNReal_iff_of_nonneg
-/
theorem _root_.Real.comap_toNNReal_atTop : comap Real.toNNReal atTop = atTop := by
  refine le_antisymm ?_ tendsto_real_toNNReal_atTop.le_comap
  refine (atTop_basis_Ioi' 0).ge_iff.2 fun a ha => ?_
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop a.toNNReal)] with x hx
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg ha.le).1 hx

@[simp]
/--
theorem `_root_.Real.tendsto_toNNReal_atTop_iff` / 定理 `_root_.Real.tendsto_toNNReal_atTop_iff`

English:
theorem _root_.Real.tendsto_toNNReal_atTop_iff
  given: {l : Filter α} {f : α -> Real}
  proof: by
  rw [← Real.comap_toNNReal_atTop]; rw [tendsto_comap_iff]; rw [Function.comp_def]

中文:
定理 _root_.实数.tendsto_toNN实数_atTop_iff
  条件: {l : 滤子 α} {f : α -> 实数}
  证明: by
  rw [← Real.comap_toNNReal_atTop]; rw [tendsto_comap_iff]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Real.comap_toNNReal_atTop, comap_toNNReal_atTop, comp_def, tendsto_comap_iff
-/
theorem _root_.Real.tendsto_toNNReal_atTop_iff {l : Filter α} {f : α -> Real} :
    Tendsto (fun x => (f x).toNNReal) l atTop ↔ Tendsto f l atTop := by
  rw [← Real.comap_toNNReal_atTop]; rw [tendsto_comap_iff]; rw [Function.comp_def]

/--
theorem `_root_.Real.tendsto_toNNReal_atTop` / 定理 `_root_.Real.tendsto_toNNReal_atTop`

English:
theorem _root_.Real.tendsto_toNNReal_atTop
  statement: Tendsto Real.toNNReal atTop atTop
  proof: Real.tendsto_toNNReal_atTop_iff.2 tendsto_id

中文:
定理 _root_.实数.tendsto_toNN实数_atTop
  结论: 收敛 实数.toNN实数 atTop atTop
  证明: Real.tendsto_toNNReal_atTop_iff.2 tendsto_id

Depends on / 依赖: Real.tendsto_toNNReal_atTop_iff, tendsto_id, tendsto_toNNReal_atTop_iff
-/
theorem _root_.Real.tendsto_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop :=
  Real.tendsto_toNNReal_atTop_iff.2 tendsto_id

/--
theorem `nhds_zero` / 定理 `nhds_zero`

English:
theorem nhds_zero
  statement: 𝓝 (0 : Real>=0) = ⨅ (a : Real>=0) (_ : a != 0), 𝓟 (Iio a)
  proof: nhds_bot_order.trans by simp only [bot_lt_iff_ne_bot]; rfl

中文:
定理 nhds_zero
  结论: 𝓝 (0 : 实数>=0) = ⨅ (a : 实数>=0) (_ : a != 0), 𝓟 (左无界右开区间 a)
  证明: nhds_bot_order.trans by simp only [bot_lt_iff_ne_bot]; rfl

Depends on / 依赖: bot_lt_iff_ne_bot, nhds_bot_order, nhds_bot_order.trans
-/
theorem nhds_zero : 𝓝 (0 : Real>=0) = ⨅ (a : Real>=0) (_ : a != 0), 𝓟 (Iio a) :=
nhds_bot_order.trans by simp only [bot_lt_iff_ne_bot]; rfl

/--
theorem `nhds_zero_basis` / 定理 `nhds_zero_basis`

English:
theorem nhds_zero_basis
  statement: (𝓝 (0 : Real>=0)).HasBasis (fun a : Real>=0 => 0 < a) fun a => Iio a
  proof: nhds_bot_basis


@[norm_cast]

中文:
定理 nhds_zero_basis
  结论: (𝓝 (0 : 实数>=0)).有基 (fun a : 实数>=0 => 0 < a) fun a => 左无界右开区间 a
  证明: nhds_bot_basis


@[norm_cast]

Depends on / 依赖: nhds_bot_basis
-/
theorem nhds_zero_basis : (𝓝 (0 : Real>=0)).HasBasis (fun a : Real>=0 => 0 < a) fun a => Iio a :=
  nhds_bot_basis


@[norm_cast]
/--
theorem `hasSum_coe` / 定理 `hasSum_coe`

English:
theorem hasSum_coe
  given: {f : α -> Real>=0} {r : Real>=0}
  proof: by
  simp only [HasSum, ← coe_sum, tendsto_coe]

中文:
定理 hasSum_coe
  条件: {f : α -> 实数>=0} {r : 实数>=0}
  证明: by
  simp only [HasSum, ← coe_sum, tendsto_coe]

Depends on / 依赖: HasSum, coe_sum, tendsto_coe
-/
theorem hasSum_coe {f : α -> Real>=0} {r : Real>=0} :
    HasSum (fun a => (f a : Real)) (r : Real) L ↔ HasSum f r L := by
  simp only [HasSum, ← coe_sum, tendsto_coe]

/--
theorem `_root_.HasSum.toNNReal` / 定理 `_root_.HasSum.toNNReal`

English:
theorem _root_.HasSum.toNNReal
  statement: {f : α -> Real} {y : Real} (hf₀ : forall n, 0 <= f n)
  proof: by
  rcases L.neBot_or_eq_bot with _ | hL
  · lift y to Real>=0 using hy.nonneg hf₀
    lift f to α -> Real>=0 using hf₀
    simpa [hasSum_coe] using hy
  · simp [HasSum, hL]

中文:
定理 _root_.HasSum.toNN实数
  结论: {f : α -> 实数} {y : 实数} (hf₀ : 对任意 n, 0 <= f n)
  证明: by
  rcases L.neBot_or_eq_bot with _ | hL
  · lift y to Real>=0 using hy.nonneg hf₀
    lift f to α -> Real>=0 using hf₀
    simpa [hasSum_coe] using hy
  · simp [HasSum, hL]
-/
protected theorem _root_.HasSum.toNNReal {f : α -> Real} {y : Real} (hf₀ : forall n, 0 <= f n)
    (hy : HasSum f y L) : HasSum (fun x => Real.toNNReal (f x)) y.toNNReal L := by
  rcases L.neBot_or_eq_bot with _ | hL
  · lift y to Real>=0 using hy.nonneg hf₀
    lift f to α -> Real>=0 using hf₀
    simpa [hasSum_coe] using hy
  · simp [HasSum, hL]

/--
theorem `hasSum_real_toNNReal_of_nonneg` / 定理 `hasSum_real_toNNReal_of_nonneg`

English:
theorem hasSum_real_toNNReal_of_nonneg
  statement: {f : α -> Real} (hf_nonneg : forall n, 0 <= f n)
  proof: hf.hasSum.toNNReal hf_nonneg

@[norm_cast]

中文:
定理 hasSum_real_toNN实数_of_nonneg
  结论: {f : α -> 实数} (hf_nonneg : 对任意 n, 0 <= f n)
  证明: hf.hasSum.toNNReal hf_nonneg

@[norm_cast]

Depends on / 依赖: hasSum, hf.hasSum.toNNReal, hf_nonneg, toNNReal
-/
theorem hasSum_real_toNNReal_of_nonneg {f : α -> Real} (hf_nonneg : forall n, 0 <= f n)
    (hf : Summable f L) :
    HasSum (fun n => Real.toNNReal (f n)) (Real.toNNReal (∑'[L] n, f n)) L :=
  hf.hasSum.toNNReal hf_nonneg

@[norm_cast]
/--
theorem `summable_coe` / 定理 `summable_coe`

English:
theorem summable_coe
  given: {f : α -> Real>=0}
  proof: by
  rcases L.neBot_or_eq_bot with _ | hL
  · constructor
    · exact fun ⟨a, ha⟩ => ⟨⟨a, ha.nonneg fun x => (f x).2⟩, hasSum_coe.1 ha⟩
    · exact fun ⟨a, ha⟩ => ⟨a.1, hasSum_coe.2 ha⟩
  · simp [Summable, HasSum, hL]

中文:
定理 summable_coe
  条件: {f : α -> 实数>=0}
  证明: by
  rcases L.neBot_or_eq_bot with _ | hL
  · constructor
    · exact fun ⟨a, ha⟩ => ⟨⟨a, ha.nonneg fun x => (f x).2⟩, hasSum_coe.1 ha⟩
    · exact fun ⟨a, ha⟩ => ⟨a.1, hasSum_coe.2 ha⟩
  · simp [Summable, HasSum, hL]

Depends on / 依赖: HasSum, L.neBot_or_eq_bot, Summable, ha.nonneg, hasSum_coe, neBot_or_eq_bot, nonneg
-/
theorem summable_coe {f : α -> Real>=0} :
    (Summable (fun a => (f a : Real)) L) ↔ Summable f L := by
  rcases L.neBot_or_eq_bot with _ | hL
  · constructor
    · exact fun ⟨a, ha⟩ => ⟨⟨a, ha.nonneg fun x => (f x).2⟩, hasSum_coe.1 ha⟩
    · exact fun ⟨a, ha⟩ => ⟨a.1, hasSum_coe.2 ha⟩
  · simp [Summable, HasSum, hL]

/--
theorem `summable_mk` / 定理 `summable_mk`

English:
theorem summable_mk
  given: {f : α -> Real} (hf : forall n, 0 <= f n)
  proof: Iff.symm summable_coe (f := fun x => ⟨f x, hf x⟩)

@[norm_cast]

中文:
定理 summable_mk
  条件: {f : α -> 实数} (hf : 对任意 n, 0 <= f n)
  证明: Iff.symm summable_coe (f := fun x => ⟨f x, hf x⟩)

@[norm_cast]

Depends on / 依赖: Iff.symm, summable_coe
-/
theorem summable_mk {f : α -> Real} (hf : forall n, 0 <= f n) :
    Summable (fun n => ⟨f n, hf n⟩ : α -> Real>=0) L ↔ Summable f L :=
Iff.symm summable_coe (f := fun x => ⟨f x, hf x⟩)

@[norm_cast]
/--
theorem `coe_tsum` / 定理 `coe_tsum`

English:
theorem coe_tsum
  given: {f : α -> Real>=0}
  statement: ↑(∑'[L] a, f a) = ∑'[L] a, (f a : Real)
  proof: Function.LeftInverse.map_tsum (g := NNReal.toRealHom)
    f NNReal.continuous_coe continuous_real_toNNReal (fun x => by simp)

中文:
定理 coe_tsum
  条件: {f : α -> 实数>=0}
  结论: ↑(∑'[L] a, f a) = ∑'[L] a, (f a : 实数)
  证明: Function.LeftInverse.map_tsum (g := NNReal.toRealHom)
    f NNReal.continuous_coe continuous_real_toNNReal (fun x => by simp)

Depends on / 依赖: Function, Function.LeftInverse.map_tsum, LeftInverse, NNReal, NNReal.continuous_coe, NNReal.toRealHom, continuous_coe, continuous_real_toNNReal, map_tsum, toRealHom
-/
theorem coe_tsum {f : α -> Real>=0} : ↑(∑'[L] a, f a) = ∑'[L] a, (f a : Real) :=
  Function.LeftInverse.map_tsum (g := NNReal.toRealHom)
    f NNReal.continuous_coe continuous_real_toNNReal (fun x => by simp)

/--
theorem `coe_tsum_of_nonneg` / 定理 `coe_tsum_of_nonneg`

English:
theorem coe_tsum_of_nonneg
  given: {f : α -> Real} (hf₁ : forall n, 0 <= f n)
  proof: NNReal.eq Eq.symm coe_tsum (f := fun x => ⟨f x, hf₁ x⟩)

nonrec theorem tsum_mul_left (a : Real>=0) (f : α -> Real>=0) :
    ∑'[L] x, a * f x = a * ∑'[L] x, f x :=
NNReal.eq by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_left]

nonrec theorem tsum_mul_right (f : α -> Real>=0) (a : Real>=0) :
    ∑'[L] x, f x * a = (∑'[L] x, f x) * a :=
NNReal.eq by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_right]

中文:
定理 coe_tsum_of_nonneg
  条件: {f : α -> 实数} (hf₁ : 对任意 n, 0 <= f n)
  证明: NNReal.eq Eq.symm coe_tsum (f := fun x => ⟨f x, hf₁ x⟩)

nonrec theorem tsum_mul_left (a : Real>=0) (f : α -> Real>=0) :
    ∑'[L] x, a * f x = a * ∑'[L] x, f x :=
NNReal.eq by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_left]

nonrec theorem tsum_mul_right (f : α -> Real>=0) (a : Real>=0) :
    ∑'[L] x, f x * a = (∑'[L] x, f x) * a :=
NNReal.eq by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_right]

Depends on / 依赖: Eq.symm, NNReal, NNReal.eq, coe_tsum
-/
theorem coe_tsum_of_nonneg {f : α -> Real} (hf₁ : forall n, 0 <= f n) :
    NNReal.mk (∑'[L] n, f n) (tsum_nonneg hf₁) = ∑'[L] n, NNReal.mk (f n) (hf₁ n) :=
NNReal.eq Eq.symm coe_tsum (f := fun x => ⟨f x, hf₁ x⟩)

nonrec theorem tsum_mul_left (a : Real>=0) (f : α -> Real>=0) :
    ∑'[L] x, a * f x = a * ∑'[L] x, f x :=
NNReal.eq by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_left]

nonrec theorem tsum_mul_right (f : α -> Real>=0) (a : Real>=0) :
    ∑'[L] x, f x * a = (∑'[L] x, f x) * a :=
NNReal.eq by simp only [coe_tsum, NNReal.coe_mul, tsum_mul_right]

/--
theorem `summable_comp_injective` / 定理 `summable_comp_injective`

English:
theorem summable_comp_injective
  statement: {β : Type*} {f : α -> Real>=0} (hf : Summable f) {i : β -> α}
  proof: by
  rw [← summable_coe] at hf ⊢
  exact hf.comp_injective hi

中文:
定理 summable_comp_injective
  结论: {β : 类型} {f : α -> 实数>=0} (hf : Summable f) {i : β -> α}
  证明: by
  rw [← summable_coe] at hf ⊢
  exact hf.comp_injective hi

Depends on / 依赖: comp_injective, hf.comp_injective, summable_coe
-/
theorem summable_comp_injective {β : Type*} {f : α -> Real>=0} (hf : Summable f) {i : β -> α}
    (hi : Function.Injective i) : Summable (f ∘ i) := by
  rw [← summable_coe] at hf ⊢
  exact hf.comp_injective hi

/--
theorem `summable_nat_add` / 定理 `summable_nat_add`

English:
theorem summable_nat_add
  given: (f : Nat -> Real>=0) (hf : Summable f) (k : Nat)
  statement: Summable fun i => f (i + k)
  proof: summable_comp_injective hf add_left_injective k

nonrec theorem summable_nat_add_iff {f : Nat -> Real>=0} (k : Nat) :
    (Summable fun i => f (i + k)) ↔ Summable f := by
  rw [← summable_coe]; rw [← summable_coe]
  exact @summable_nat_add_iff Real _ _ _ (fun i => (f i : Real)) k

nonrec theorem hasSum_nat_add_iff {f : Nat -> Real>=0} (k : Nat) {a : Real>=0} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) := by
  rw [← hasSum_coe]; rw [hasSum_nat_add_iff (f := fun n => toReal (f n)) k]; norm_cast

中文:
定理 summable_nat_add
  条件: (f : 自然数 -> 实数>=0) (hf : Summable f) (k : 自然数)
  结论: Summable fun i => f (i + k)
  证明: summable_comp_injective hf add_left_injective k

nonrec theorem summable_nat_add_iff {f : Nat -> Real>=0} (k : Nat) :
    (Summable fun i => f (i + k)) ↔ Summable f := by
  rw [← summable_coe]; rw [← summable_coe]
  exact @summable_nat_add_iff Real _ _ _ (fun i => (f i : Real)) k

nonrec theorem hasSum_nat_add_iff {f : Nat -> Real>=0} (k : Nat) {a : Real>=0} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) := by
  rw [← hasSum_coe]; rw [hasSum_nat_add_iff (f := fun n => toReal (f n)) k]; norm_cast

Depends on / 依赖: add_left_injective, summable_comp_injective
-/
theorem summable_nat_add (f : Nat -> Real>=0) (hf : Summable f) (k : Nat) : Summable fun i => f (i + k) :=
summable_comp_injective hf add_left_injective k

nonrec theorem summable_nat_add_iff {f : Nat -> Real>=0} (k : Nat) :
    (Summable fun i => f (i + k)) ↔ Summable f := by
  rw [← summable_coe]; rw [← summable_coe]
  exact @summable_nat_add_iff Real _ _ _ (fun i => (f i : Real)) k

nonrec theorem hasSum_nat_add_iff {f : Nat -> Real>=0} (k : Nat) {a : Real>=0} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) := by
  rw [← hasSum_coe]; rw [hasSum_nat_add_iff (f := fun n => toReal (f n)) k]; norm_cast

/--
theorem `sum_add_tsum_nat_add` / 定理 `sum_add_tsum_nat_add`

English:
theorem sum_add_tsum_nat_add
  given: {f : Nat -> Real>=0} (k : Nat) (hf : Summable f)
  proof: (((summable_nat_add_iff k).2 hf).sum_add_tsum_nat_add').symm

中文:
定理 sum_add_tsum_nat_add
  条件: {f : 自然数 -> 实数>=0} (k : 自然数) (hf : Summable f)
  证明: (((summable_nat_add_iff k).2 hf).sum_add_tsum_nat_add').symm

Depends on / 依赖: sum_add_tsum_nat_add, summable_nat_add_iff
-/
theorem sum_add_tsum_nat_add {f : Nat -> Real>=0} (k : Nat) (hf : Summable f) :
    ∑' i, f i = (∑ i in range k, f i) + ∑' i, f (i + k) :=
  (((summable_nat_add_iff k).2 hf).sum_add_tsum_nat_add').symm

/--
theorem `iInf_real_pos_eq_iInf_nnreal_pos` / 定理 `iInf_real_pos_eq_iInf_nnreal_pos`

English:
theorem iInf_real_pos_eq_iInf_nnreal_pos
  given: [CompleteLattice α] {f : Real -> α}
  proof: le_antisymm (iInf_mono' fun r => ⟨r, le_rfl⟩) (iInf₂_mono' fun r hr => ⟨⟨r, hr.le⟩, hr, le_rfl⟩)

中文:
定理 iInf_real_pos_eq_iInf_nnreal_pos
  条件: [完备格 α] {f : 实数 -> α}
  证明: le_antisymm (iInf_mono' fun r => ⟨r, le_rfl⟩) (iInf₂_mono' fun r hr => ⟨⟨r, hr.le⟩, hr, le_rfl⟩)

Depends on / 依赖: hr.le, iInf_mono, le_antisymm, le_rfl
-/
theorem iInf_real_pos_eq_iInf_nnreal_pos [CompleteLattice α] {f : Real -> α} :
    ⨅ (n : Real) (_ : 0 < n), f n = ⨅ (n : Real>=0) (_ : 0 < n), f n :=
  le_antisymm (iInf_mono' fun r => ⟨r, le_rfl⟩) (iInf₂_mono' fun r hr => ⟨⟨r, hr.le⟩, hr, le_rfl⟩)

end coe

/--
theorem `tendsto_cofinite_zero_of_summable` / 定理 `tendsto_cofinite_zero_of_summable`

English:
theorem tendsto_cofinite_zero_of_summable
  given: {α} {f : α -> Real>=0} (hf : Summable f)
  proof: by
  simp only [← summable_coe, ← tendsto_coe] at hf ⊢
  exact hf.tendsto_cofinite_zero

中文:
定理 tendsto_cofinite_zero_of_summable
  条件: {α} {f : α -> 实数>=0} (hf : Summable f)
  证明: by
  simp only [← summable_coe, ← tendsto_coe] at hf ⊢
  exact hf.tendsto_cofinite_zero

Depends on / 依赖: hf.tendsto_cofinite_zero, summable_coe, tendsto_coe, tendsto_cofinite_zero
-/
theorem tendsto_cofinite_zero_of_summable {α} {f : α -> Real>=0} (hf : Summable f) :
    Tendsto f cofinite (𝓝 0) := by
  simp only [← summable_coe, ← tendsto_coe] at hf ⊢
  exact hf.tendsto_cofinite_zero

/--
theorem `tendsto_atTop_zero_of_summable` / 定理 `tendsto_atTop_zero_of_summable`

English:
theorem tendsto_atTop_zero_of_summable
  given: {f : Nat -> Real>=0} (hf : Summable f)
  statement: Tendsto f atTop (𝓝 0)
  proof: by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_summable hf

中文:
定理 tendsto_atTop_zero_of_summable
  条件: {f : 自然数 -> 实数>=0} (hf : Summable f)
  结论: 收敛 f atTop (𝓝 0)
  证明: by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_summable hf

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, tendsto_cofinite_zero_of_summable
-/
theorem tendsto_atTop_zero_of_summable {f : Nat -> Real>=0} (hf : Summable f) : Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_summable hf

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
nonrec theorem tendsto_tsum_compl_atTop_zero {α : Type*} (f : α -> Real>=0) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
  simp_rw [← tendsto_coe, coe_tsum, NNReal.coe_zero]
  exact tendsto_tsum_compl_atTop_zero fun a : α => (f a : Real)

/--
Definition of `powOrderIso` / `powOrderIso` 的定义

English:
definition powOrderIso
  signature: (n : Nat) (hn : n != 0)
  body: StrictMono.orderIsoOfSurjective (fun x => x ^ n) (fun x y h =>
      pow_left_strictMonoOn₀ hn (zero_le (a := x)) (zero_le (a := y)) h) <|
(continuous_id.pow _).surjective (tendsto_pow_atTop hn) by
      simpa [OrderBot.atBot_eq, pos_iff_ne_zero]

中文:
定义 powOrderIso
  签名: (n : 自然数) (hn : n != 0)
  定义体: StrictMono.orderIsoOfSurjective (fun x => x ^ n) (fun x y h =>
      pow_left_strictMonoOn₀ hn (zero_le (a := x)) (zero_le (a := y)) h) <|
(continuous_id.pow _).surjective (tendsto_pow_atTop hn) by
      simpa [OrderBot.atBot_eq, pos_iff_ne_zero]

Depends on / 依赖: OrderBot, OrderBot.atBot_eq, StrictMono, StrictMono.orderIsoOfSurjective, atBot_eq, continuous_id, continuous_id.pow, orderIsoOfSurjective, pos_iff_ne_zero, surjective, tendsto_pow_atTop, zero_le
-/
def powOrderIso (n : Nat) (hn : n != 0) : Real>=0 ≃o Real>=0 :=
  StrictMono.orderIsoOfSurjective (fun x => x ^ n) (fun x y h =>
      pow_left_strictMonoOn₀ hn (zero_le (a := x)) (zero_le (a := y)) h) <|
(continuous_id.pow _).surjective (tendsto_pow_atTop hn) by
      simpa [OrderBot.atBot_eq, pos_iff_ne_zero]

section Monotone

/-- A monotone, bounded above sequence `f : ℕ → ℝ` has a finite limit. -/
@[deprecated tendsto_atTop_ciSup (since := "2026-01-14")]
/--
theorem `_root_.Real.tendsto_of_bddAbove_monotone` / 定理 `_root_.Real.tendsto_of_bddAbove_monotone`

English:
theorem _root_.Real.tendsto_of_bddAbove_monotone
  statement: {f : Nat -> Real} (h_bdd : BddAbove (Set.range f))
  proof: ⟨iSup f, tendsto_atTop_ciSup h_mon h_bdd⟩

中文:
定理 _root_.实数.tendsto_of_bddAbove_monotone
  结论: {f : 自然数 -> 实数} (h_bdd : BddAbove (集合.range f))
  证明: ⟨iSup f, tendsto_atTop_ciSup h_mon h_bdd⟩

Depends on / 依赖: h_bdd, h_mon, tendsto_atTop_ciSup
-/
theorem _root_.Real.tendsto_of_bddAbove_monotone {f : Nat -> Real} (h_bdd : BddAbove (Set.range f))
    (h_mon : Monotone f) : exists r : Real, Tendsto f atTop (𝓝 r) :=
  ⟨iSup f, tendsto_atTop_ciSup h_mon h_bdd⟩

/-- An antitone, bounded below sequence `f : ℕ → ℝ` has a finite limit. -/
@[deprecated tendsto_atTop_ciInf (since := "2026-01-14")]
/--
theorem `_root_.Real.tendsto_of_bddBelow_antitone` / 定理 `_root_.Real.tendsto_of_bddBelow_antitone`

English:
theorem _root_.Real.tendsto_of_bddBelow_antitone
  statement: {f : Nat -> Real} (h_bdd : BddBelow (Set.range f))
  proof: ⟨iInf f, tendsto_atTop_ciInf h_ant h_bdd⟩

中文:
定理 _root_.实数.tendsto_of_bddBelow_antitone
  结论: {f : 自然数 -> 实数} (h_bdd : BddBelow (集合.range f))
  证明: ⟨iInf f, tendsto_atTop_ciInf h_ant h_bdd⟩

Depends on / 依赖: h_ant, h_bdd, tendsto_atTop_ciInf
-/
theorem _root_.Real.tendsto_of_bddBelow_antitone {f : Nat -> Real} (h_bdd : BddBelow (Set.range f))
    (h_ant : Antitone f) : exists r : Real, Tendsto f atTop (𝓝 r) :=
  ⟨iInf f, tendsto_atTop_ciInf h_ant h_bdd⟩

variable {ι : Type*} [Preorder ι]

/-- An antitone sequence `f : ℕ → ℝ≥0` has a finite limit. -/
@[deprecated tendsto_atTop_ciInf (since := "2026-01-14")]
/--
theorem `tendsto_of_antitone` / 定理 `tendsto_of_antitone`

English:
theorem tendsto_of_antitone
  given: {f : Nat -> Real>=0} (h_ant : Antitone f)
  proof: ⟨iInf f, tendsto_atTop_ciInf h_ant (by simp)⟩

中文:
定理 tendsto_of_antitone
  条件: {f : 自然数 -> 实数>=0} (h_ant : 递减 f)
  证明: ⟨iInf f, tendsto_atTop_ciInf h_ant (by simp)⟩

Depends on / 依赖: h_ant, tendsto_atTop_ciInf
-/
theorem tendsto_of_antitone {f : Nat -> Real>=0} (h_ant : Antitone f) :
    exists r : Real>=0, Tendsto f atTop (𝓝 r) := ⟨iInf f, tendsto_atTop_ciInf h_ant (by simp)⟩

end Monotone

/--
lemma `iSup_pow_of_ne_zero` / 引理 `iSup_pow_of_ne_zero`

English:
lemma iSup_pow_of_ne_zero
  given: (hn : n != 0) (f : ι -> Real>=0)
  statement: (⨆ i, f i) ^ n = ⨆ i, f i ^ n
  proof: (NNReal.powOrderIso n hn).map_ciSup' _

中文:
引理 iSup_pow_of_ne_zero
  条件: (hn : n != 0) (f : ι -> 实数>=0)
  结论: (⨆ i, f i) ^ n = ⨆ i, f i ^ n
  证明: (NNReal.powOrderIso n hn).map_ciSup' _

Depends on / 依赖: NNReal, NNReal.powOrderIso, map_ciSup, powOrderIso
-/
lemma iSup_pow_of_ne_zero (hn : n != 0) (f : ι -> Real>=0) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n :=
  (NNReal.powOrderIso n hn).map_ciSup' _

/--
lemma `iSup_pow` / 引理 `iSup_pow`

English:
lemma iSup_pow
  given: [Nonempty ι] (f : ι -> Real>=0) (n : Nat)
  statement: (⨆ i, f i) ^ n = ⨆ i, f i ^ n
  proof: by
  by_cases hn : n = 0
  · simp [hn]
  · exact iSup_pow_of_ne_zero hn _

中文:
引理 iSup_pow
  条件: [非空 ι] (f : ι -> 实数>=0) (n : 自然数)
  结论: (⨆ i, f i) ^ n = ⨆ i, f i ^ n
  证明: by
  by_cases hn : n = 0
  · simp [hn]
  · exact iSup_pow_of_ne_zero hn _

Depends on / 依赖: iSup_pow_of_ne_zero
-/
lemma iSup_pow [Nonempty ι] (f : ι -> Real>=0) (n : Nat) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact iSup_pow_of_ne_zero hn _

end NNReal

namespace ENNReal

attribute [simp] ENNReal.top_pow

/--
Definition of `powOrderIso` / `powOrderIso` 的定义

English:
definition powOrderIso
  signature: (n : Nat) (hn : n != 0)
  body: (NNReal.powOrderIso n hn).withTopCongr.copy (· ^ n) _
    (by cases n; (· cases hn rfl); · ext (_ | _) <;> rfl) rfl

中文:
定义 powOrderIso
  签名: (n : 自然数) (hn : n != 0)
  定义体: (NNReal.powOrderIso n hn).withTopCongr.copy (· ^ n) _
    (by cases n; (· cases hn rfl); · ext (_ | _) <;> rfl) rfl

Depends on / 依赖: NNReal, NNReal.powOrderIso, powOrderIso, withTopCongr, withTopCongr.copy
-/
def powOrderIso (n : Nat) (hn : n != 0) : Real>=0∞ ≃o Real>=0∞ :=
  (NNReal.powOrderIso n hn).withTopCongr.copy (· ^ n) _
    (by cases n; (· cases hn rfl); · ext (_ | _) <;> rfl) rfl

/--
lemma `iSup_pow_of_ne_zero` / 引理 `iSup_pow_of_ne_zero`

English:
lemma iSup_pow_of_ne_zero
  given: (hn : n != 0) (f : ι -> Real>=0∞)
  statement: (⨆ i, f i) ^ n = ⨆ i, f i ^ n
  proof: (powOrderIso n hn).map_iSup _

中文:
引理 iSup_pow_of_ne_zero
  条件: (hn : n != 0) (f : ι -> 实数>=0∞)
  结论: (⨆ i, f i) ^ n = ⨆ i, f i ^ n
  证明: (powOrderIso n hn).map_iSup _

Depends on / 依赖: map_iSup, powOrderIso
-/
lemma iSup_pow_of_ne_zero (hn : n != 0) (f : ι -> Real>=0∞) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n :=
  (powOrderIso n hn).map_iSup _

/--
lemma `iSup_pow` / 引理 `iSup_pow`

English:
lemma iSup_pow
  given: [Nonempty ι] (f : ι -> Real>=0∞) (n : Nat)
  statement: (⨆ i, f i) ^ n = ⨆ i, f i ^ n
  proof: by
  by_cases hn : n = 0
  · simp [hn]
  · exact iSup_pow_of_ne_zero hn _

中文:
引理 iSup_pow
  条件: [非空 ι] (f : ι -> 实数>=0∞) (n : 自然数)
  结论: (⨆ i, f i) ^ n = ⨆ i, f i ^ n
  证明: by
  by_cases hn : n = 0
  · simp [hn]
  · exact iSup_pow_of_ne_zero hn _

Depends on / 依赖: iSup_pow_of_ne_zero
-/
lemma iSup_pow [Nonempty ι] (f : ι -> Real>=0∞) (n : Nat) : (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact iSup_pow_of_ne_zero hn _

/--
lemma `iSup₂_pow_of_ne_zero` / 引理 `iSup₂_pow_of_ne_zero`

English:
lemma iSup₂_pow_of_ne_zero
  given: {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Real>=0∞) {n : Nat} (hn : n != 0)
  proof: (powOrderIso n hn).map_iSup₂ f

中文:
引理 iSup₂_pow_of_ne_zero
  条件: {κ : ι -> 类型层*} (f : (i : ι) -> κ i -> 实数>=0∞) {n : 自然数} (hn : n != 0)
  证明: (powOrderIso n hn).map_iSup₂ f

Depends on / 依赖: powOrderIso
-/
lemma iSup₂_pow_of_ne_zero {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Real>=0∞) {n : Nat} (hn : n != 0) :
    (⨆ i, ⨆ j, f i j) ^ n = ⨆ i, ⨆ j, f i j ^ n :=
  (powOrderIso n hn).map_iSup₂ f

end ENNReal

open NNReal in
/--
lemma `Real.iSup_pow` / 引理 `Real.iSup_pow`

English:
lemma Real.iSup_pow
  given: [Nonempty ι] {f : ι -> Real} (hf : forall i, 0 <= f i) (n : Nat)
  proof: by
  lift f to ι -> Real>=0 using hf; dsimp; exact mod_cast NNReal.iSup_pow f n

中文:
引理 实数.iSup_pow
  条件: [非空 ι] {f : ι -> 实数} (hf : 对任意 i, 0 <= f i) (n : 自然数)
  证明: by
  lift f to ι -> Real>=0 using hf; dsimp; exact mod_cast NNReal.iSup_pow f n

Depends on / 依赖: NNReal, NNReal.iSup_pow, iSup_pow, mod_cast
-/
lemma Real.iSup_pow [Nonempty ι] {f : ι -> Real} (hf : forall i, 0 <= f i) (n : Nat) :
    (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  lift f to ι -> Real>=0 using hf; dsimp; exact mod_cast NNReal.iSup_pow f n

/--
lemma `Real.iSup_pow_of_ne_zero` / 引理 `Real.iSup_pow_of_ne_zero`

English:
lemma Real.iSup_pow_of_ne_zero
  given: {f : ι -> Real} (hf : forall i, 0 <= f i) (hn : n != 0)
  proof: by
  cases isEmpty_or_nonempty ι
  · simp [hn]
  · exact iSup_pow hf _

中文:
引理 实数.iSup_pow_of_ne_zero
  条件: {f : ι -> 实数} (hf : 对任意 i, 0 <= f i) (hn : n != 0)
  证明: by
  cases isEmpty_or_nonempty ι
  · simp [hn]
  · exact iSup_pow hf _

Depends on / 依赖: iSup_pow, isEmpty_or_nonempty
-/
lemma Real.iSup_pow_of_ne_zero {f : ι -> Real} (hf : forall i, 0 <= f i) (hn : n != 0) :
    (⨆ i, f i) ^ n = ⨆ i, f i ^ n := by
  cases isEmpty_or_nonempty ι
  · simp [hn]
  · exact iSup_pow hf _
