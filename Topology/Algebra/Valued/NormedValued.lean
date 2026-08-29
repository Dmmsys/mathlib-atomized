/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Correspondence between nontrivial nonarchimedean norms and rank one valuations

Nontrivial nonarchimedean norms correspond to rank one valuations.

## Main Definitions
* `NormedField.toValued` : the valued field structure on a nonarchimedean normed field `K`,
  determined by the norm.
* `Valued.toNormedField` : the normed field structure determined by a rank one valuation.

## Main Results
* The valuation of a normed field has rank at most one.

## Tags

norm, nonarchimedean, nontrivial, valuation, rank one
-/

@[expose] public section


noncomputable section

open Filter Set Valuation MonoidWithZeroHom

open scoped NNReal

section

variable {K : Type*} [hK : NormedField K] [IsUltrametricDist K]

namespace NormedField

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `valuation` / `valuation` 的定义

English:
definition valuation
  signature: : Valuation K Real>=0 where
  body: nnnorm
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul
  map_add_le_max' := IsUltrametricDist.norm_add_le_max

@[simp]

中文:
定义 valuation
  签名: : Valuation K 实数>=0 where
  定义体: nnnorm
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul
  map_add_le_max' := IsUltrametricDist.norm_add_le_max

@[simp]

Depends on / 依赖: nnnorm
-/
def valuation : Valuation K Real>=0 where
  toFun := nnnorm
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul
  map_add_le_max' := IsUltrametricDist.norm_add_le_max

@[simp]
/--
theorem `valuation_apply` / 定理 `valuation_apply`

English:
theorem valuation_apply
  given: (x : K)
  statement: valuation x = ‖x‖₊
  proof: rfl

中文:
定理 valuation_apply
  条件: (x : K)
  结论: valuation x = ‖x‖₊
  证明: rfl
-/
theorem valuation_apply (x : K) : valuation x = ‖x‖₊ := rfl

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RankLeOne (valuation (K := K))
  body: embedding
  strictMono' := embedding_strictMono

中文:
实例 :
  签名: RankLeOne (valuation (K := K))
  定义体: embedding
  strictMono' := embedding_strictMono
-/
instance : RankLeOne (valuation (K := K)) where
  hom' := embedding
  strictMono' := embedding_strictMono

set_option backward.isDefEq.respectTransparency.types false in
/-- The valued field structure on a nonarchimedean normed field `K`, determined by the norm. -/
@[instance_reducible]
/--
Definition of `toValued` / `toValued` 的定义

English:
definition toValued
  signature: : Valued K Real>=0
  body: { hK.toUniformSpace,
    (inferInstance : IsUniformAddGroup K) with
    v := valuation
    is_topological_valuation := fun U => by
      rw [Metric.mem_nhds_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨ε, hε, h⟩
        rcases RankLeOne.exists_val_lt (valuation (K := K)) with H | H
        · use Units

中文:
定义 toValued
  签名: : Valued K 实数>=0
  定义体: { hK.toUniformSpace,
    (inferInstance : IsUniformAddGroup K) with
    v := valuation
    is_topological_valuation := fun U => by
      rw [Metric.mem_nhds_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨ε, hε, h⟩
        rcases RankLeOne.exists_val_lt (valuation (K := K)) with H | H
        · use Units

Depends on / 依赖: IsUniformAddGroup, Metric, Metric.mem_ball_self, Metric.mem_nhds_iff, RankLeOne, RankLeOne.exists_val_lt, Units.mk0, Units.val_mk0, exists_val_lt, hK.toUniformSpace, is_topological_valuation, map_one, mem_ball_self, mem_nhds_iff, mem_ofPred_eq, ne_eq, restrict, restrict.zero_iff, toUniformSpace, val_mk0
-/
def toValued : Valued K Real>=0 :=
  { hK.toUniformSpace,
    (inferInstance : IsUniformAddGroup K) with
    v := valuation
    is_topological_valuation := fun U => by
      rw [Metric.mem_nhds_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨ε, hε, h⟩
        rcases RankLeOne.exists_val_lt (valuation (K := K)) with H | H
        · use Units.mk0 (valuation.restrict 1) (by simp)
          intro x hx
          simp only [Units.val_mk0, mem_ofPred_eq, map_one] at hx
          by_cases hx0 : x = 0
          · exact h (hx0 ▸ Metric.mem_ball_self hε)
          · exfalso
            rw [← (valuation (K := K)).restrict.zero_iff]; rw [← ne_eq]; rw [← isUnit_iff_ne_zero] at hx0
            apply not_le.mpr hx
            apply le_of_eq
            rw [eq_comm]
            simpa only [Units.ext_iff, hx0.unit_spec, Units.val_one,
              Submonoid.mk_eq_one] using! H.elim hx0.unit 1
        · obtain ⟨x, hx, hxy⟩ := H (γ := ⟨ε, le_of_lt hε⟩) (pos_iff_ne_zero.mp hε)
          use Units.mk0 (valuation.restrict x) (by simp [Valuation.restrict_def, hx])
          intro y hy
          apply h
          simp only [Metric.mem_ball, dist_zero_right]
          simp only [Units.val_mk0, mem_ofPred_eq, restrict_lt_iff, ← NNReal.coe_lt_coe] at hy
          apply lt_trans hy
          simpa [RankLeOne.hom', valuation.restrict_def] using! hxy
      · rintro ⟨ε, hε⟩
        refine ⟨(embedding ε.1 : Real>=0), ?_, fun x hx => hε ?_⟩
· exact NNReal.coe_pos.mpr embedding_strictMono.lt_iff_lt.mpr ε.zero_lt
        · simpa [restrict_lt_iff_lt_embedding] using! (mem_ball_zero_iff.mp hx) }

instance {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] :
    Valuation.RankOne (valuation (K := K)) where
  hom' := ValueGroup₀.embedding
  strictMono' := ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := (exists_one_lt_norm K).imp fun x h => by
    have h' : x != 0 := norm_eq_zero.not.mp (h.gt.trans' (by simp)).ne'
    simp [valuation_apply, ← NNReal.coe_inj, h.ne', h']

end NormedField

end


namespace Valuation

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀) [hv : RankOne v]

/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: : L -> Real
  body: fun x : L => hv.hom _ (v.restrict x)

中文:
定义 norm
  签名: : L -> 实数
  定义体: fun x : L => hv.hom _ (v.restrict x)

Depends on / 依赖: hv.hom, restrict, v.restrict
-/
def norm : L -> Real := fun x : L => hv.hom _ (v.restrict x)

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: {x : L}
  statement: v.norm x = hv.hom _ (v.restrict x)
  proof: rfl

中文:
定理 norm_def
  条件: {x : L}
  结论: v.norm x = hv.hom _ (v.restrict x)
  证明: rfl
-/
theorem norm_def {x : L} : v.norm x = hv.hom _ (v.restrict x) := rfl

/--
theorem `norm_nonneg` / 定理 `norm_nonneg`

English:
theorem norm_nonneg
  given: (x : L)
  statement: 0 <= v.norm x
  proof: by simp only [norm, NNReal.zero_le_coe]

中文:
定理 norm_nonneg
  条件: (x : L)
  结论: 0 <= v.norm x
  证明: by simp only [norm, NNReal.zero_le_coe]

Depends on / 依赖: NNReal, NNReal.zero_le_coe, zero_le_coe
-/
theorem norm_nonneg (x : L) : 0 <= v.norm x := by simp only [norm, NNReal.zero_le_coe]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `norm_add_le` / 定理 `norm_add_le`

English:
theorem norm_add_le
  given: (x y : L)
  statement: v.norm (x + y) <= max (v.norm x) (v.norm y)
  proof: by
  simp only [norm, NNReal.coe_le_coe, le_max_iff, StrictMono.le_iff_le hv.strictMono]
  exact le_max_iff.mp (Valuation.map_add_le_max' v.restrict _ _)

中文:
定理 norm_add_le
  条件: (x y : L)
  结论: v.norm (x + y) <= max (v.norm x) (v.norm y)
  证明: by
  simp only [norm, NNReal.coe_le_coe, le_max_iff, StrictMono.le_iff_le hv.strictMono]
  exact le_max_iff.mp (Valuation.map_add_le_max' v.restrict _ _)

Depends on / 依赖: NNReal, NNReal.coe_le_coe, StrictMono, StrictMono.le_iff_le, Valuation, Valuation.map_add_le_max, coe_le_coe, hv.strictMono, le_iff_le, le_max_iff, le_max_iff.mp, map_add_le_max, restrict, strictMono, v.restrict
-/
theorem norm_add_le (x y : L) : v.norm (x + y) <= max (v.norm x) (v.norm y) := by
  simp only [norm, NNReal.coe_le_coe, le_max_iff, StrictMono.le_iff_le hv.strictMono]
  exact le_max_iff.mp (Valuation.map_add_le_max' v.restrict _ _)

/--
theorem `norm_eq_zero` / 定理 `norm_eq_zero`

English:
theorem norm_eq_zero
  given: {x : L} (hx : v.norm x = 0)
  statement: x = 0
  proof: by
  simpa [v.restrict_def, norm, NNReal.coe_eq_zero, RankOne.hom_eq_zero_iff, zero_iff] using hx

中文:
定理 norm_eq_zero
  条件: {x : L} (hx : v.norm x = 0)
  结论: x = 0
  证明: by
  simpa [v.restrict_def, norm, NNReal.coe_eq_zero, RankOne.hom_eq_zero_iff, zero_iff] using hx

Depends on / 依赖: NNReal, NNReal.coe_eq_zero, RankOne, RankOne.hom_eq_zero_iff, coe_eq_zero, hom_eq_zero_iff, restrict_def, v.restrict_def, zero_iff
-/
theorem norm_eq_zero {x : L} (hx : v.norm x = 0) : x = 0 := by
  simpa [v.restrict_def, norm, NNReal.coe_eq_zero, RankOne.hom_eq_zero_iff, zero_iff] using hx

/--
theorem `norm_pos_iff_valuation_pos` / 定理 `norm_pos_iff_valuation_pos`

English:
theorem norm_pos_iff_valuation_pos
  given: {x : L}
  statement: 0 < v.norm x ↔ (0 : Γ₀) < v x
  proof: by
  rw [norm_def]; rw [← NNReal.coe_zero]; rw [NNReal.coe_lt_coe]; rw [← map_zero (RankOne.hom v)]; rw [StrictMono.lt_iff_lt (RankOne.strictMono v)]
  rw [v.restrict_pos_iff]

中文:
定理 norm_pos_iff_valuation_pos
  条件: {x : L}
  结论: 0 < v.norm x ↔ (0 : Γ₀) < v x
  证明: by
  rw [norm_def]; rw [← NNReal.coe_zero]; rw [NNReal.coe_lt_coe]; rw [← map_zero (RankOne.hom v)]; rw [StrictMono.lt_iff_lt (RankOne.strictMono v)]
  rw [v.restrict_pos_iff]

Depends on / 依赖: NNReal, NNReal.coe_lt_coe, NNReal.coe_zero, RankOne, RankOne.hom, RankOne.strictMono, StrictMono, StrictMono.lt_iff_lt, coe_lt_coe, coe_zero, lt_iff_lt, map_zero, norm_def, restrict_pos_iff, strictMono, v.restrict_pos_iff
-/
theorem norm_pos_iff_valuation_pos {x : L} : 0 < v.norm x ↔ (0 : Γ₀) < v x := by
  rw [norm_def]; rw [← NNReal.coe_zero]; rw [NNReal.coe_lt_coe]; rw [← map_zero (RankOne.hom v)]; rw [StrictMono.lt_iff_lt (RankOne.strictMono v)]
  rw [v.restrict_pos_iff]

end Valuation

namespace Valued

variable (L : Type*) [Field L] (Γ₀ : Type*) [LinearOrderedCommGroupWithZero Γ₀]
  [val : Valued L Γ₀] [hv : RankOne val.v]

open Valuation

/-- The normed field structure determined by a rank one valuation. -/
@[instance_reducible]
/--
Definition of `toNormedField` / `toNormedField` 的定义

English:
definition toNormedField
  signature: : NormedField L
  body: { (inferInstance : Field L) with
    norm := val.v.norm
    dist := fun x y => val.v.norm (x - y)
    dist_self := fun x => by
      simp only [sub_self, Valuation.norm, Valuation.map_zero, hv.hom.map_zero, NNReal.coe_zero]
    dist_comm := fun x y => by simp only [Valuation.norm]; rw [← neg_sub, Va

中文:
定义 toNormedField
  签名: : NormedField L
  定义体: { (inferInstance : Field L) with
    norm := val.v.norm
    dist := fun x y => val.v.norm (x - y)
    dist_self := fun x => by
      simp only [sub_self, Valuation.norm, Valuation.map_zero, hv.hom.map_zero, NNReal.coe_zero]
    dist_comm := fun x y => by simp only [Valuation.norm]; rw [← neg_sub, Va

Depends on / 依赖: NNReal, NNReal.coe_zero, Valuation, Valuation.map_neg, Valuation.map_zero, Valuation.norm, coe_zero, dist_comm, dist_self, dist_triangle, eq_of_dist_eq_zero, hv.hom.map_zero, le_trans, map_neg, map_zero, max_le_add_of_nonneg, neg_sub, norm_add_le, norm_nonneg, sub_add_sub_cancel
-/
def toNormedField : NormedField L :=
  { (inferInstance : Field L) with
    norm := val.v.norm
    dist := fun x y => val.v.norm (x - y)
    dist_self := fun x => by
      simp only [sub_self, Valuation.norm, Valuation.map_zero, hv.hom.map_zero, NNReal.coe_zero]
    dist_comm := fun x y => by simp only [Valuation.norm]; rw [← neg_sub, Valuation.map_neg]
    dist_triangle := fun x y z => by
      simp only [← sub_add_sub_cancel x y z]
      exact le_trans (val.v.norm_add_le _ _)
        (max_le_add_of_nonneg (val.v.norm_nonneg _) (val.v.norm_nonneg _))
    eq_of_dist_eq_zero := fun hxy => eq_of_sub_eq_zero (val.v.norm_eq_zero hxy)
    dist_eq := fun x y => by
      simp only [Valuation.norm]
      rw [← v.restrict.map_neg]; rw [neg_sub]; rw [sub_eq_add_neg]; rw [add_comm]
    norm_mul := fun x y => by simp only [Valuation.norm, ← NNReal.coe_mul, map_mul]
    toUniformSpace := Valued.toUniformSpace
    uniformity_dist := by
      have : Nonempty { ε : Real // ε > 0 } := nonempty_Ioi_subtype
      ext U
      rw [hasBasis_iff.mp (Valued.hasBasis_uniformity L Γ₀)]; rw [iInf_subtype']; rw [mem_iInf_of_directed]
      · simp only [true_and, mem_principal, Subtype.exists, gt_iff_lt, exists_prop]
        refine ⟨fun ⟨ε, hε⟩ => ?_, fun ⟨r, hr_pos, hr⟩ => ?_⟩
        · set δ : Real>=0 := hv.hom _ ε with hδ
          have hδ_pos : 0 < δ := by
            rw [hδ]; rw [← map_zero hv.hom]
            exact hv.strictMono _ (Units.zero_lt ε)
          use δ, hδ_pos
          apply subset_trans _ hε
          intro x hx
          simp only [mem_ofPred_eq, Valuation.norm, hδ, NNReal.coe_lt_coe] at hx
          rw [mem_ofPred]; rw [← neg_sub]; rw [Valuation.map_neg]
          exact (RankOne.strictMono Valued.v).lt_iff_lt.mp hx
        · have : Nontrivial Γ₀ˣ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mpr
            ⟨RankOne.unit val.v, RankOne.unit_ne_one val.v⟩
          obtain ⟨u, hu⟩ := Real.exists_lt_of_strictMono hv.strictMono hr_pos
          use u
          apply subset_trans _ hr
          intro x hx
          simp only [Valuation.norm, mem_ofPred_eq]
          apply lt_trans _ hu
          rw [NNReal.coe_lt_coe]; rw [← neg_sub]; rw [Valuation.map_neg]
          exact (RankOne.strictMono Valued.v).lt_iff_lt.mpr hx
      · simp only [Directed]
        intro x y
        use min x y
        simp only [le_principal_iff, mem_principal, ofPred_subset_ofPred, Prod.forall]
        exact ⟨fun a b hab => lt_of_lt_of_le hab (min_le_left _ _), fun a b hab =>
            lt_of_lt_of_le hab (min_le_right _ _)⟩ }

-- When a field is valued, one inherits a `NormedField`.
-- Scoped instance to avoid a typeclass loop or non-defeq topology or norms.
scoped[Valued] attribute [instance] Valued.toNormedField
scoped[NormedField] attribute [instance] NormedField.toValued

section NormedField

open scoped Valued

/--
lemma `isNonarchimedean_norm` / 引理 `isNonarchimedean_norm`

English:
lemma isNonarchimedean_norm
  statement: IsNonarchimedean ((‖·‖) : L -> Real)
  proof: Valuation.norm_add_le _

中文:
引理 isNonarchimedean_norm
  结论: IsNonarchimedean ((‖·‖) : L -> 实数)
  证明: Valuation.norm_add_le _
-/
protected lemma isNonarchimedean_norm : IsNonarchimedean ((‖·‖) : L -> Real) :=
  Valuation.norm_add_le _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUltrametricDist L
  body: ⟨fun x y z => by
    refine (Valuation.norm_add_le _ (x - y) (y - z)).trans_eq' ?_
    simp only [sub_add_sub_cancel]
    rfl ⟩

中文:
实例 :
  签名: IsUltrametricDist L
  定义体: ⟨fun x y z => by
    refine (Valuation.norm_add_le _ (x - y) (y - z)).trans_eq' ?_
    simp only [sub_add_sub_cancel]
    rfl ⟩

Depends on / 依赖: Valuation, Valuation.norm_add_le, norm_add_le, sub_add_sub_cancel, trans_eq
-/
instance : IsUltrametricDist L :=
  ⟨fun x y z => by
    refine (Valuation.norm_add_le _ (x - y) (y - z)).trans_eq' ?_
    simp only [sub_add_sub_cancel]
    rfl ⟩

/--
lemma `coe_valuation_eq_rankOne_hom_comp_valuation` / 引理 `coe_valuation_eq_rankOne_hom_comp_valuation`

English:
lemma coe_valuation_eq_rankOne_hom_comp_valuation
  proof: rfl

中文:
引理 coe_valuation_eq_rankOne_hom_comp_valuation
  证明: rfl
-/
lemma coe_valuation_eq_rankOne_hom_comp_valuation :
    ⇑NormedField.valuation = hv.hom ∘ val.v.restrict := rfl

end NormedField
namespace toNormedField

variable {L Γ₀}

variable {x x' : L}

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  statement: ‖x‖ = hv.hom _ (Valued.v.restrict x)
  proof: rfl

@[simp]

中文:
定理 norm_def
  结论: ‖x‖ = hv.hom _ (Valued.v.restrict x)
  证明: rfl

@[simp]
-/
theorem norm_def : ‖x‖ = hv.hom _ (Valued.v.restrict x) := rfl

@[simp]
/--
theorem `norm_le_iff` / 定理 `norm_le_iff`

English:
theorem norm_le_iff
  statement: ‖x‖ <= ‖x'‖ ↔ val.v x <= val.v x'
  proof: by
  rw [← v.restrict_le_iff]; rw [← (Valuation.RankOne.strictMono val.v).le_iff_le]
  rfl

@[simp]

中文:
定理 norm_le_iff
  结论: ‖x‖ <= ‖x'‖ ↔ val.v x <= val.v x'
  证明: by
  rw [← v.restrict_le_iff]; rw [← (Valuation.RankOne.strictMono val.v).le_iff_le]
  rfl

@[simp]

Depends on / 依赖: RankOne, Valuation, Valuation.RankOne.strictMono, le_iff_le, restrict_le_iff, strictMono, v.restrict_le_iff, val.v
-/
theorem norm_le_iff : ‖x‖ <= ‖x'‖ ↔ val.v x <= val.v x' := by
  rw [← v.restrict_le_iff]; rw [← (Valuation.RankOne.strictMono val.v).le_iff_le]
  rfl

@[simp]
/--
theorem `norm_lt_iff` / 定理 `norm_lt_iff`

English:
theorem norm_lt_iff
  statement: ‖x‖ < ‖x'‖ ↔ val.v x < val.v x'
  proof: by
  rw [← v.restrict_lt_iff]; rw [← (Valuation.RankOne.strictMono val.v).lt_iff_lt]
  rfl

@[simp]

中文:
定理 norm_lt_iff
  结论: ‖x‖ < ‖x'‖ ↔ val.v x < val.v x'
  证明: by
  rw [← v.restrict_lt_iff]; rw [← (Valuation.RankOne.strictMono val.v).lt_iff_lt]
  rfl

@[simp]

Depends on / 依赖: RankOne, Valuation, Valuation.RankOne.strictMono, lt_iff_lt, restrict_lt_iff, strictMono, v.restrict_lt_iff, val.v
-/
theorem norm_lt_iff : ‖x‖ < ‖x'‖ ↔ val.v x < val.v x' := by
  rw [← v.restrict_lt_iff]; rw [← (Valuation.RankOne.strictMono val.v).lt_iff_lt]
  rfl

@[simp]
/--
theorem `norm_le_one_iff` / 定理 `norm_le_one_iff`

English:
theorem norm_le_one_iff
  statement: ‖x‖ <= 1 ↔ val.v x <= 1
  proof: by
  rw [← map_one val.v]; rw [← v.restrict_le_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).le_iff_le (b := 1)

@[simp]

中文:
定理 norm_le_one_iff
  结论: ‖x‖ <= 1 ↔ val.v x <= 1
  证明: by
  rw [← map_one val.v]; rw [← v.restrict_le_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).le_iff_le (b := 1)

@[simp]

Depends on / 依赖: RankOne, Valuation, Valuation.RankOne.strictMono, le_iff_le, map_one, restrict_le_iff, strictMono, v.restrict_le_iff, val.v
-/
theorem norm_le_one_iff : ‖x‖ <= 1 ↔ val.v x <= 1 := by
  rw [← map_one val.v]; rw [← v.restrict_le_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).le_iff_le (b := 1)

@[simp]
/--
theorem `norm_lt_one_iff` / 定理 `norm_lt_one_iff`

English:
theorem norm_lt_one_iff
  statement: ‖x‖ < 1 ↔ val.v x < 1
  proof: by
  rw [← map_one val.v]; rw [← v.restrict_lt_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).lt_iff_lt (b := 1)

@[simp]

中文:
定理 norm_lt_one_iff
  结论: ‖x‖ < 1 ↔ val.v x < 1
  证明: by
  rw [← map_one val.v]; rw [← v.restrict_lt_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).lt_iff_lt (b := 1)

@[simp]

Depends on / 依赖: RankOne, Valuation, Valuation.RankOne.strictMono, lt_iff_lt, map_one, restrict_lt_iff, strictMono, v.restrict_lt_iff, val.v
-/
theorem norm_lt_one_iff : ‖x‖ < 1 ↔ val.v x < 1 := by
  rw [← map_one val.v]; rw [← v.restrict_lt_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).lt_iff_lt (b := 1)

@[simp]
/--
theorem `one_le_norm_iff` / 定理 `one_le_norm_iff`

English:
theorem one_le_norm_iff
  statement: 1 <= ‖x‖ ↔ 1 <= val.v x
  proof: by
  rw [← map_one val.v]; rw [← v.restrict_le_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).le_iff_le (a := 1)

@[simp]

中文:
定理 one_le_norm_iff
  结论: 1 <= ‖x‖ ↔ 1 <= val.v x
  证明: by
  rw [← map_one val.v]; rw [← v.restrict_le_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).le_iff_le (a := 1)

@[simp]

Depends on / 依赖: RankOne, Valuation, Valuation.RankOne.strictMono, le_iff_le, map_one, restrict_le_iff, strictMono, v.restrict_le_iff, val.v
-/
theorem one_le_norm_iff : 1 <= ‖x‖ ↔ 1 <= val.v x := by
  rw [← map_one val.v]; rw [← v.restrict_le_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).le_iff_le (a := 1)

@[simp]
/--
theorem `one_lt_norm_iff` / 定理 `one_lt_norm_iff`

English:
theorem one_lt_norm_iff
  statement: 1 < ‖x‖ ↔ 1 < val.v x
  proof: by
  rw [← map_one val.v]; rw [← v.restrict_lt_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).lt_iff_lt (a := 1)

中文:
定理 one_lt_norm_iff
  结论: 1 < ‖x‖ ↔ 1 < val.v x
  证明: by
  rw [← map_one val.v]; rw [← v.restrict_lt_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).lt_iff_lt (a := 1)

Depends on / 依赖: RankOne, Valuation, Valuation.RankOne.strictMono, lt_iff_lt, map_one, restrict_lt_iff, strictMono, v.restrict_lt_iff, val.v
-/
theorem one_lt_norm_iff : 1 < ‖x‖ ↔ 1 < val.v x := by
  rw [← map_one val.v]; rw [← v.restrict_lt_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).lt_iff_lt (a := 1)

/--
lemma `setOfPred_mem_integer_eq_closedBall` / 引理 `setOfPred_mem_integer_eq_closedBall`

English:
lemma setOfPred_mem_integer_eq_closedBall
  proof: by
  ext x
  simp [mem_integer_iff]

@[deprecated (since := "2026-07-09")]
alias setOf_mem_integer_eq_closedBall := setOfPred_mem_integer_eq_closedBall

中文:
引理 setOfPred_mem_integer_eq_closedBall
  证明: by
  ext x
  simp [mem_integer_iff]

@[deprecated (since := "2026-07-09")]
alias setOf_mem_integer_eq_closedBall := setOfPred_mem_integer_eq_closedBall

Depends on / 依赖: mem_integer_iff
-/
lemma setOfPred_mem_integer_eq_closedBall :
    { x : L | x in Valued.v.integer } = Metric.closedBall 0 1 := by
  ext x
  simp [mem_integer_iff]

@[deprecated (since := "2026-07-09")]
alias setOf_mem_integer_eq_closedBall := setOfPred_mem_integer_eq_closedBall

end toNormedField

/--
The nontrivially normed field structure determined by a rank one valuation.
-/
@[instance_reducible]
/--
Definition of `toNontriviallyNormedField` / `toNontriviallyNormedField` 的定义

English:
definition toNontriviallyNormedField
  signature: : NontriviallyNormedField L
  body: {
  val.toNormedField with
  non_trivial := by
    obtain ⟨x, hx⟩ := Valuation.RankOne.nontrivial val.v
    rcases Valuation.val_le_one_or_val_inv_le_one val.v x with h | h
    · use x⁻¹
      simp only [toNormedField.one_lt_norm_iff, map_inv₀, one_lt_inv₀ (zero_lt_iff.mpr hx.1),
          lt_of_le_

中文:
定义 toNontriviallyNormedField
  签名: : NontriviallyNormedField L
  定义体: {
  val.toNormedField with
  non_trivial := by
    obtain ⟨x, hx⟩ := Valuation.RankOne.nontrivial val.v
    rcases Valuation.val_le_one_or_val_inv_le_one val.v x with h | h
    · use x⁻¹
      simp only [toNormedField.one_lt_norm_iff, map_inv₀, one_lt_inv₀ (zero_lt_iff.mpr hx.1),
          lt_of_le_
-/
def toNontriviallyNormedField : NontriviallyNormedField L := {
  val.toNormedField with
  non_trivial := by
    obtain ⟨x, hx⟩ := Valuation.RankOne.nontrivial val.v
    rcases Valuation.val_le_one_or_val_inv_le_one val.v x with h | h
    · use x⁻¹
      simp only [toNormedField.one_lt_norm_iff, map_inv₀, one_lt_inv₀ (zero_lt_iff.mpr hx.1),
          lt_of_le_of_ne h hx.2]
    · use x
      simp only [map_inv₀, inv_le_one₀ <| zero_lt_iff.mpr hx.1] at h
      simp only [toNormedField.one_lt_norm_iff, lt_of_le_of_ne h hx.2.symm]
}

scoped[Valued] attribute [instance] Valued.toNontriviallyNormedField

end Valued
