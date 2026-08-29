/-
Copyright (c) 2019 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Dynamics.FixedPoints.Topology
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Contracting maps

A Lipschitz continuous self-map with Lipschitz constant `K < 1` is called a *contracting map*.
In this file we prove the Banach fixed point theorem, some explicit estimates on the rate
of convergence, and some properties of the map sending a contracting map to its fixed point.

## Main definitions

* `ContractingWith K f` : a Lipschitz continuous self-map with `K < 1`;
* `efixedPoint` : given a contracting map `f` on a complete emetric space and a point `x`
  such that `edist x (f x) ≠ ∞`, `efixedPoint f hf x hx` is the unique fixed point of `f`
  in `Metric.eball x ∞`;
* `fixedPoint` : the unique fixed point of a contracting map on a complete nonempty metric space.

## Tags

contracting map, fixed point, Banach fixed point theorem
-/

@[expose] public section

open NNReal Topology ENNReal Filter Function

variable {α : Type*}

/--
Definition of `ContractingWith` / `ContractingWith` 的定义

English:
definition ContractingWith
  signature: [EMetricSpace α] (K : Real>=0) (f : α -> α)
  body: K < 1 ∧ LipschitzWith K f

中文:
定义 ContractingWith
  签名: [广义度量空间 α] (K : 实数>=0) (f : α -> α)
  定义体: K < 1 ∧ LipschitzWith K f

Depends on / 依赖: LipschitzWith
-/
def ContractingWith [EMetricSpace α] (K : Real>=0) (f : α -> α) :=
  K < 1 ∧ LipschitzWith K f

namespace ContractingWith

variable [EMetricSpace α] {K : Real>=0} {f : α -> α}

open EMetric Set

/--
theorem `toLipschitzWith` / 定理 `toLipschitzWith`

English:
theorem toLipschitzWith
  given: (hf : ContractingWith K f)
  statement: LipschitzWith K f
  proof: hf.2

中文:
定理 toLipschitzWith
  条件: (hf : ContractingWith K f)
  结论: LipschitzWith K f
  证明: hf.2
-/
theorem toLipschitzWith (hf : ContractingWith K f) : LipschitzWith K f := hf.2

/--
theorem `one_sub_K_pos'` / 定理 `one_sub_K_pos'`

English:
theorem one_sub_K_pos'
  given: (hf : ContractingWith K f)
  statement: (0 : Real>=0∞) < 1 - K
  proof: by simp [hf.1]

中文:
定理 one_sub_K_pos'
  条件: (hf : ContractingWith K f)
  结论: (0 : 实数>=0∞) < 1 - K
  证明: by simp [hf.1]
-/
theorem one_sub_K_pos' (hf : ContractingWith K f) : (0 : Real>=0∞) < 1 - K := by simp [hf.1]

/--
theorem `one_sub_K_ne_zero` / 定理 `one_sub_K_ne_zero`

English:
theorem one_sub_K_ne_zero
  given: (hf : ContractingWith K f)
  statement: (1 : Real>=0∞) - K != 0
  proof: ne_of_gt hf.one_sub_K_pos'

中文:
定理 one_sub_K_ne_zero
  条件: (hf : ContractingWith K f)
  结论: (1 : 实数>=0∞) - K != 0
  证明: ne_of_gt hf.one_sub_K_pos'

Depends on / 依赖: hf.one_sub_K_pos, ne_of_gt, one_sub_K_pos
-/
theorem one_sub_K_ne_zero (hf : ContractingWith K f) : (1 : Real>=0∞) - K != 0 :=
  ne_of_gt hf.one_sub_K_pos'

/--
theorem `one_sub_K_ne_top` / 定理 `one_sub_K_ne_top`

English:
theorem one_sub_K_ne_top
  statement: (1 : Real>=0∞) - K != ∞
  proof: by
  norm_cast
  exact ENNReal.coe_ne_top

中文:
定理 one_sub_K_ne_top
  结论: (1 : 实数>=0∞) - K != ∞
  证明: by
  norm_cast
  exact ENNReal.coe_ne_top

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, coe_ne_top
-/
theorem one_sub_K_ne_top : (1 : Real>=0∞) - K != ∞ := by
  norm_cast
  exact ENNReal.coe_ne_top

/--
theorem `edist_inequality` / 定理 `edist_inequality`

English:
theorem edist_inequality
  given: (hf : ContractingWith K f) {x y} (h : edist x y != ∞)
  proof: suffices edist x y <= edist x (f x) + edist y (f y) + K * edist x y by
    rwa [ENNReal.le_div_iff_mul_le (Or.inl hf.one_sub_K_ne_zero) (Or.inl one_sub_K_ne_top),
      mul_comm, ENNReal.sub_mul fun _ _ => h, one_mul, tsub_le_iff_right]
  calc
    edist x y <= edist x (f x) + edist (f x) (f y) + edi

中文:
定理 edist_inequality
  条件: (hf : ContractingWith K f) {x y} (h : edist x y != ∞)
  证明: suffices edist x y <= edist x (f x) + edist y (f y) + K * edist x y by
    rwa [ENNReal.le_div_iff_mul_le (Or.inl hf.one_sub_K_ne_zero) (Or.inl one_sub_K_ne_top),
      mul_comm, ENNReal.sub_mul fun _ _ => h, one_mul, tsub_le_iff_right]
  calc
    edist x y <= edist x (f x) + edist (f x) (f y) + edi

Depends on / 依赖: ENNReal, ENNReal.le_div_iff_mul_le, ENNReal.sub_mul, Or.inl, add_le_add, add_right_comm, edist_comm, edist_triangle4, hf.one_sub_K_ne_zero, le_div_iff_mul_le, le_rfl, mul_comm, one_mul, one_sub_K_ne_top, one_sub_K_ne_zero, sub_mul, tsub_le_iff_right
-/
theorem edist_inequality (hf : ContractingWith K f) {x y} (h : edist x y != ∞) :
    edist x y <= (edist x (f x) + edist y (f y)) / (1 - K) :=
  suffices edist x y <= edist x (f x) + edist y (f y) + K * edist x y by
    rwa [ENNReal.le_div_iff_mul_le (Or.inl hf.one_sub_K_ne_zero) (Or.inl one_sub_K_ne_top),
      mul_comm, ENNReal.sub_mul fun _ _ => h, one_mul, tsub_le_iff_right]
  calc
    edist x y <= edist x (f x) + edist (f x) (f y) + edist (f y) y := edist_triangle4 _ _ _ _
    _ = edist x (f x) + edist y (f y) + edist (f x) (f y) := by rw [edist_comm y, add_right_comm]
    _ <= edist x (f x) + edist y (f y) + K * edist x y := add_le_add le_rfl (hf.2 _ _)

/--
theorem `edist_le_of_fixedPoint` / 定理 `edist_le_of_fixedPoint`

English:
theorem edist_le_of_fixedPoint
  statement: (hf : ContractingWith K f) {x y} (h : edist x y != ∞)
  proof: by
  simpa only [hy.eq, edist_self, add_zero] using hf.edist_inequality h

中文:
定理 edist_le_of_fixedPoint
  结论: (hf : ContractingWith K f) {x y} (h : edist x y != ∞)
  证明: by
  simpa only [hy.eq, edist_self, add_zero] using hf.edist_inequality h

Depends on / 依赖: add_zero, edist_inequality, edist_self, hf.edist_inequality, hy.eq
-/
theorem edist_le_of_fixedPoint (hf : ContractingWith K f) {x y} (h : edist x y != ∞)
    (hy : IsFixedPt f y) : edist x y <= edist x (f x) / (1 - K) := by
  simpa only [hy.eq, edist_self, add_zero] using hf.edist_inequality h

/--
theorem `eq_or_edist_eq_top_of_fixedPoints` / 定理 `eq_or_edist_eq_top_of_fixedPoints`

English:
theorem eq_or_edist_eq_top_of_fixedPoints
  statement: (hf : ContractingWith K f) {x y} (hx : IsFixedPt f x)
  proof: by
  refine or_iff_not_imp_right.2 fun h => edist_le_zero.1 ?_
  simpa only [hx.eq, edist_self, add_zero, ENNReal.zero_div] using hf.edist_le_of_fixedPoint h hy

中文:
定理 eq_or_edist_eq_top_of_fixedPoints
  结论: (hf : ContractingWith K f) {x y} (hx : IsFixedPt f x)
  证明: by
  refine or_iff_not_imp_right.2 fun h => edist_le_zero.1 ?_
  simpa only [hx.eq, edist_self, add_zero, ENNReal.zero_div] using hf.edist_le_of_fixedPoint h hy

Depends on / 依赖: ENNReal, ENNReal.zero_div, add_zero, edist_le_of_fixedPoint, edist_le_zero, edist_self, hf.edist_le_of_fixedPoint, hx.eq, or_iff_not_imp_right, zero_div
-/
theorem eq_or_edist_eq_top_of_fixedPoints (hf : ContractingWith K f) {x y} (hx : IsFixedPt f x)
    (hy : IsFixedPt f y) : x = y ∨ edist x y = ∞ := by
  refine or_iff_not_imp_right.2 fun h => edist_le_zero.1 ?_
  simpa only [hx.eq, edist_self, add_zero, ENNReal.zero_div] using hf.edist_le_of_fixedPoint h hy

/--
theorem `restrict` / 定理 `restrict`

English:
theorem restrict
  given: (hf : ContractingWith K f) {s : Set α} (hs : MapsTo f s s)
  proof: ⟨hf.1, fun x y => hf.2 x y⟩

中文:
定理 restrict
  条件: (hf : ContractingWith K f) {s : 集合 α} (hs : 映射到 f s s)
  证明: ⟨hf.1, fun x y => hf.2 x y⟩
-/
theorem restrict (hf : ContractingWith K f) {s : Set α} (hs : MapsTo f s s) :
    ContractingWith K (hs.restrict f s s) :=
  ⟨hf.1, fun x y => hf.2 x y⟩

section
variable [CompleteSpace α]

/-- Banach fixed-point theorem, contraction mapping theorem, `EMetricSpace` version.
A contracting map on a complete metric space has a fixed point.
We include more conclusions in this theorem to avoid proving them again later.

The main API for this theorem are the functions `efixedPoint` and `fixedPoint`,
and lemmas about these functions. -/
@[wikidata Q220680]
/--
theorem `exists_fixedPoint` / 定理 `exists_fixedPoint`

English:
theorem exists_fixedPoint
  given: (hf : ContractingWith K f) (x : α) (hx : edist x (f x) != ∞)
  proof: have : CauchySeq fun n => f^[n] x :=
    cauchySeq_of_edist_le_geometric K (edist x (f x)) (ENNReal.coe_lt_one_iff.2 hf.1) hx
      (hf.toLipschitzWith.edist_iterate_succ_le_geometric x)
  let ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this
  ⟨y, isFixedPt_of_tendsto_iterate hy hf.2.continuous.continu

中文:
定理 存在_fixedPoint
  条件: (hf : ContractingWith K f) (x : α) (hx : edist x (f x) != ∞)
  证明: have : CauchySeq fun n => f^[n] x :=
    cauchySeq_of_edist_le_geometric K (edist x (f x)) (ENNReal.coe_lt_one_iff.2 hf.1) hx
      (hf.toLipschitzWith.edist_iterate_succ_le_geometric x)
  let ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this
  ⟨y, isFixedPt_of_tendsto_iterate hy hf.2.continuous.continu

Depends on / 依赖: CauchySeq, ENNReal, ENNReal.coe_lt_one_iff, cauchySeq_of_edist_le_geometric, cauchySeq_tendsto_of_complete, coe_lt_one_iff, continuous, continuous.continuousAt, continuousAt, edist_iterate_succ_le_geometric, edist_le_of_edist_le_geometric_of_tendsto, hf.toLipschitzWith.edist_iterate_succ_le_geometric, isFixedPt_of_tendsto_iterate, toLipschitzWith
-/
theorem exists_fixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) != ∞) :
    exists y, IsFixedPt f y ∧ Tendsto (fun n => f^[n] x) atTop (𝓝 y) ∧
      forall n : Nat, edist (f^[n] x) y <= edist x (f x) * (K : Real>=0∞) ^ n / (1 - K) :=
  have : CauchySeq fun n => f^[n] x :=
    cauchySeq_of_edist_le_geometric K (edist x (f x)) (ENNReal.coe_lt_one_iff.2 hf.1) hx
      (hf.toLipschitzWith.edist_iterate_succ_le_geometric x)
  let ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this
  ⟨y, isFixedPt_of_tendsto_iterate hy hf.2.continuous.continuousAt, hy,
    edist_le_of_edist_le_geometric_of_tendsto K (edist x (f x))
      (hf.toLipschitzWith.edist_iterate_succ_le_geometric x) hy⟩

variable (f) in
-- avoid `efixedPoint _` in pretty printer
/--
Definition of `efixedPoint` / `efixedPoint` 的定义

English:
definition efixedPoint
  signature: (hf : ContractingWith K f) (x : α) (hx : edist x (f x) != ∞)
  body: Classical.choose hf.exists_fixedPoint x hx

中文:
定义 efixedPoint
  签名: (hf : ContractingWith K f) (x : α) (hx : edist x (f x) != ∞)
  定义体: Classical.choose hf.exists_fixedPoint x hx

Depends on / 依赖: Classical, Classical.choose, exists_fixedPoint, hf.exists_fixedPoint
-/
noncomputable def efixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) != ∞) : α :=
Classical.choose hf.exists_fixedPoint x hx

/--
theorem `efixedPoint_isFixedPt` / 定理 `efixedPoint_isFixedPt`

English:
theorem efixedPoint_isFixedPt
  given: (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
  proof: (Classical.choose_spec <| hf.exists_fixedPoint x hx).1

中文:
定理 efixedPoint_isFixedPt
  条件: (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
  证明: (Classical.choose_spec <| hf.exists_fixedPoint x hx).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_fixedPoint, hf.exists_fixedPoint
-/
theorem efixedPoint_isFixedPt (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞) :
    IsFixedPt f (efixedPoint f hf x hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).1

/--
theorem `tendsto_iterate_efixedPoint` / 定理 `tendsto_iterate_efixedPoint`

English:
theorem tendsto_iterate_efixedPoint
  given: (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
  proof: (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.1

中文:
定理 tendsto_iterate_efixedPoint
  条件: (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
  证明: (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_fixedPoint, hf.exists_fixedPoint
-/
theorem tendsto_iterate_efixedPoint (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞) :
    Tendsto (fun n => f^[n] x) atTop (𝓝 <| efixedPoint f hf x hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.1

/--
theorem `apriori_edist_iterate_efixedPoint_le` / 定理 `apriori_edist_iterate_efixedPoint_le`

English:
theorem apriori_edist_iterate_efixedPoint_le
  statement: (hf : ContractingWith K f) {x : α}
  proof: (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.2 n

中文:
定理 apriori_edist_iterate_efixedPoint_le
  结论: (hf : ContractingWith K f) {x : α}
  证明: (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.2 n

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_fixedPoint, hf.exists_fixedPoint
-/
theorem apriori_edist_iterate_efixedPoint_le (hf : ContractingWith K f) {x : α}
    (hx : edist x (f x) != ∞) (n : Nat) :
    edist (f^[n] x) (efixedPoint f hf x hx) <= edist x (f x) * (K : Real>=0∞) ^ n / (1 - K) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.2 n

/--
theorem `edist_efixedPoint_le` / 定理 `edist_efixedPoint_le`

English:
theorem edist_efixedPoint_le
  given: (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
  proof: by
  convert! hf.apriori_edist_iterate_efixedPoint_le hx 0
  simp only [pow_zero, mul_one]

中文:
定理 edist_efixedPoint_le
  条件: (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
  证明: by
  convert! hf.apriori_edist_iterate_efixedPoint_le hx 0
  simp only [pow_zero, mul_one]

Depends on / 依赖: apriori_edist_iterate_efixedPoint_le, convert, hf.apriori_edist_iterate_efixedPoint_le, mul_one, pow_zero
-/
theorem edist_efixedPoint_le (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞) :
    edist x (efixedPoint f hf x hx) <= edist x (f x) / (1 - K) := by
  convert! hf.apriori_edist_iterate_efixedPoint_le hx 0
  simp only [pow_zero, mul_one]

/--
theorem `edist_efixedPoint_lt_top` / 定理 `edist_efixedPoint_lt_top`

English:
theorem edist_efixedPoint_lt_top
  given: (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
  proof: (hf.edist_efixedPoint_le hx).trans_lt
    (ENNReal.mul_ne_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero).lt_top

中文:
定理 edist_efixedPoint_lt_top
  条件: (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
  证明: (hf.edist_efixedPoint_le hx).trans_lt
    (ENNReal.mul_ne_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero).lt_top

Depends on / 依赖: ENNReal, ENNReal.inv_ne_top, ENNReal.mul_ne_top, edist_efixedPoint_le, hf.edist_efixedPoint_le, hf.one_sub_K_ne_zero, inv_ne_top, lt_top, mul_ne_top, one_sub_K_ne_zero, trans_lt
-/
theorem edist_efixedPoint_lt_top (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞) :
    edist x (efixedPoint f hf x hx) < ∞ :=
  (hf.edist_efixedPoint_le hx).trans_lt
    (ENNReal.mul_ne_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero).lt_top

/--
theorem `efixedPoint_eq_of_edist_lt_top` / 定理 `efixedPoint_eq_of_edist_lt_top`

English:
theorem efixedPoint_eq_of_edist_lt_top
  statement: (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
  proof: by
  refine (hf.eq_or_edist_eq_top_of_fixedPoints ?_ ?_).elim id fun h' => False.elim (ne_of_lt ?_ h')
    <;> try apply efixedPoint_isFixedPt
  change Metric.edistLtTopSetoid _ _
  trans x
  · apply Setoid.symm'
    exact hf.edist_efixedPoint_lt_top hx
  trans y
  exacts [lt_top_iff_ne_top.2 h, hf.

中文:
定理 efixedPoint_eq_of_edist_lt_top
  结论: (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
  证明: by
  refine (hf.eq_or_edist_eq_top_of_fixedPoints ?_ ?_).elim id fun h' => False.elim (ne_of_lt ?_ h')
    <;> try apply efixedPoint_isFixedPt
  change Metric.edistLtTopSetoid _ _
  trans x
  · apply Setoid.symm'
    exact hf.edist_efixedPoint_lt_top hx
  trans y
  exacts [lt_top_iff_ne_top.2 h, hf.

Depends on / 依赖: False.elim, Metric, Metric.edistLtTopSetoid, Setoid, Setoid.symm, edistLtTopSetoid, edist_efixedPoint_lt_top, efixedPoint_isFixedPt, eq_or_edist_eq_top_of_fixedPoints, exacts, hf.edist_efixedPoint_lt_top, hf.eq_or_edist_eq_top_of_fixedPoints, lt_top_iff_ne_top, ne_of_lt
-/
theorem efixedPoint_eq_of_edist_lt_top (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞)
    {y : α} (hy : edist y (f y) != ∞) (h : edist x y != ∞) :
    efixedPoint f hf x hx = efixedPoint f hf y hy := by
  refine (hf.eq_or_edist_eq_top_of_fixedPoints ?_ ?_).elim id fun h' => False.elim (ne_of_lt ?_ h')
    <;> try apply efixedPoint_isFixedPt
  change Metric.edistLtTopSetoid _ _
  trans x
  · apply Setoid.symm'
    exact hf.edist_efixedPoint_lt_top hx
  trans y
  exacts [lt_top_iff_ne_top.2 h, hf.edist_efixedPoint_lt_top hy]

end

/--
theorem `exists_fixedPoint'` / 定理 `exists_fixedPoint'`

English:
theorem exists_fixedPoint'
  statement: {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
  proof: by
  have := hsc.completeSpace_coe
  rcases hf.exists_fixedPoint ⟨x, hxs⟩ hx with ⟨y, hfy, h_tendsto, hle⟩
  refine ⟨y, y.2, Subtype.ext_iff.1 hfy, ?_, fun n => ?_⟩
  · convert! (continuous_subtype_val.tendsto _).comp h_tendsto
    simp only [(· ∘ ·), MapsTo.iterate_restrict, MapsTo.val_restrict_app

中文:
定理 存在_fixedPoint'
  结论: {s : 集合 α} (hsc : 是完备 s) (hsf : 映射到 f s s)
  证明: by
  have := hsc.completeSpace_coe
  rcases hf.exists_fixedPoint ⟨x, hxs⟩ hx with ⟨y, hfy, h_tendsto, hle⟩
  refine ⟨y, y.2, Subtype.ext_iff.1 hfy, ?_, fun n => ?_⟩
  · convert! (continuous_subtype_val.tendsto _).comp h_tendsto
    simp only [(· ∘ ·), MapsTo.iterate_restrict, MapsTo.val_restrict_app

Depends on / 依赖: MapsTo, MapsTo.iterate_restrict, MapsTo.val_restrict_apply, Subtype, Subtype.ext_iff, completeSpace_coe, continuous_subtype_val, continuous_subtype_val.tendsto, convert, exists_fixedPoint, ext_iff, h_tendsto, hf.exists_fixedPoint, hsc.completeSpace_coe, iterate_restrict, tendsto, val_restrict_apply
-/
theorem exists_fixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : edist x (f x) != ∞) :
    exists y in s, IsFixedPt f y ∧ Tendsto (fun n => f^[n] x) atTop (𝓝 y) ∧
      forall n : Nat, edist (f^[n] x) y <= edist x (f x) * (K : Real>=0∞) ^ n / (1 - K) := by
  have := hsc.completeSpace_coe
  rcases hf.exists_fixedPoint ⟨x, hxs⟩ hx with ⟨y, hfy, h_tendsto, hle⟩
  refine ⟨y, y.2, Subtype.ext_iff.1 hfy, ?_, fun n => ?_⟩
  · convert! (continuous_subtype_val.tendsto _).comp h_tendsto
    simp only [(· ∘ ·), MapsTo.iterate_restrict, MapsTo.val_restrict_apply]
  · convert! hle n
    rw [MapsTo.iterate_restrict]
    rfl

variable (f) in
-- avoid `efixedPoint _` in pretty printer
/--
Definition of `efixedPoint'` / `efixedPoint'` 的定义

English:
definition efixedPoint'
  signature: {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
  body: Classical.choose hf.exists_fixedPoint' hsc hsf hxs hx

中文:
定义 efixedPoint'
  签名: {s : 集合 α} (hsc : 是完备 s) (hsf : 映射到 f s s)
  定义体: Classical.choose hf.exists_fixedPoint' hsc hsf hxs hx

Depends on / 依赖: Classical, Classical.choose, exists_fixedPoint, hf.exists_fixedPoint
-/
noncomputable def efixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) (x : α) (hxs : x in s) (hx : edist x (f x) != ∞) :
    α :=
Classical.choose hf.exists_fixedPoint' hsc hsf hxs hx

/--
theorem `efixedPoint_mem'` / 定理 `efixedPoint_mem'`

English:
theorem efixedPoint_mem'
  statement: {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
  proof: (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).1

中文:
定理 efixedPoint_mem'
  结论: {s : 集合 α} (hsc : 是完备 s) (hsf : 映射到 f s s)
  证明: (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_fixedPoint, hf.exists_fixedPoint
-/
theorem efixedPoint_mem' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : edist x (f x) != ∞) :
    efixedPoint' f hsc hsf hf x hxs hx in s :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).1

/--
theorem `efixedPoint_isFixedPt'` / 定理 `efixedPoint_isFixedPt'`

English:
theorem efixedPoint_isFixedPt'
  statement: {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
  proof: (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.1

中文:
定理 efixedPoint_isFixedPt'
  结论: {s : 集合 α} (hsc : 是完备 s) (hsf : 映射到 f s s)
  证明: (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_fixedPoint, hf.exists_fixedPoint
-/
theorem efixedPoint_isFixedPt' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : edist x (f x) != ∞) :
    IsFixedPt f (efixedPoint' f hsc hsf hf x hxs hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.1

/--
theorem `tendsto_iterate_efixedPoint'` / 定理 `tendsto_iterate_efixedPoint'`

English:
theorem tendsto_iterate_efixedPoint'
  statement: {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
  proof: (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.1

中文:
定理 tendsto_iterate_efixedPoint'
  结论: {s : 集合 α} (hsc : 是完备 s) (hsf : 映射到 f s s)
  证明: (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_fixedPoint, hf.exists_fixedPoint
-/
theorem tendsto_iterate_efixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : edist x (f x) != ∞) :
    Tendsto (fun n => f^[n] x) atTop (𝓝 <| efixedPoint' f hsc hsf hf x hxs hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.1

/--
theorem `apriori_edist_iterate_efixedPoint_le'` / 定理 `apriori_edist_iterate_efixedPoint_le'`

English:
theorem apriori_edist_iterate_efixedPoint_le'
  statement: {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
  proof: (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.2 n

中文:
定理 apriori_edist_iterate_efixedPoint_le'
  结论: {s : 集合 α} (hsc : 是完备 s) (hsf : 映射到 f s s)
  证明: (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.2 n

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_fixedPoint, hf.exists_fixedPoint
-/
theorem apriori_edist_iterate_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : edist x (f x) != ∞)
    (n : Nat) :
    edist (f^[n] x) (efixedPoint' f hsc hsf hf x hxs hx) <=
      edist x (f x) * (K : Real>=0∞) ^ n / (1 - K) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.2 n

/--
theorem `edist_efixedPoint_le'` / 定理 `edist_efixedPoint_le'`

English:
theorem edist_efixedPoint_le'
  statement: {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
  proof: by
  convert! hf.apriori_edist_iterate_efixedPoint_le' hsc hsf hxs hx 0
  rw [pow_zero]; rw [mul_one]

中文:
定理 edist_efixedPoint_le'
  结论: {s : 集合 α} (hsc : 是完备 s) (hsf : 映射到 f s s)
  证明: by
  convert! hf.apriori_edist_iterate_efixedPoint_le' hsc hsf hxs hx 0
  rw [pow_zero]; rw [mul_one]

Depends on / 依赖: apriori_edist_iterate_efixedPoint_le, convert, hf.apriori_edist_iterate_efixedPoint_le, mul_one, pow_zero
-/
theorem edist_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : edist x (f x) != ∞) :
    edist x (efixedPoint' f hsc hsf hf x hxs hx) <= edist x (f x) / (1 - K) := by
  convert! hf.apriori_edist_iterate_efixedPoint_le' hsc hsf hxs hx 0
  rw [pow_zero]; rw [mul_one]

/--
theorem `edist_efixedPoint_lt_top'` / 定理 `edist_efixedPoint_lt_top'`

English:
theorem edist_efixedPoint_lt_top'
  statement: {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
  proof: (hf.edist_efixedPoint_le' hsc hsf hxs hx).trans_lt
    (ENNReal.mul_ne_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero).lt_top

中文:
定理 edist_efixedPoint_lt_top'
  结论: {s : 集合 α} (hsc : 是完备 s) (hsf : 映射到 f s s)
  证明: (hf.edist_efixedPoint_le' hsc hsf hxs hx).trans_lt
    (ENNReal.mul_ne_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero).lt_top

Depends on / 依赖: ENNReal, ENNReal.inv_ne_top, ENNReal.mul_ne_top, edist_efixedPoint_le, hf.edist_efixedPoint_le, hf.one_sub_K_ne_zero, inv_ne_top, lt_top, mul_ne_top, one_sub_K_ne_zero, trans_lt
-/
theorem edist_efixedPoint_lt_top' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : edist x (f x) != ∞) :
    edist x (efixedPoint' f hsc hsf hf x hxs hx) < ∞ :=
  (hf.edist_efixedPoint_le' hsc hsf hxs hx).trans_lt
    (ENNReal.mul_ne_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero).lt_top

/--
theorem `efixedPoint_eq_of_edist_lt_top'` / 定理 `efixedPoint_eq_of_edist_lt_top'`

English:
theorem efixedPoint_eq_of_edist_lt_top'
  statement: (hf : ContractingWith K f) {s : Set α} (hsc : IsComplete s)
  proof: by
  refine (hf.eq_or_edist_eq_top_of_fixedPoints ?_ ?_).elim id fun h' => False.elim (ne_of_lt ?_ h')
    <;> try apply efixedPoint_isFixedPt'
  change Metric.edistLtTopSetoid _ _
  trans x
  · apply Setoid.symm'
    apply edist_efixedPoint_lt_top'
  trans y
  · exact lt_top_iff_ne_top.2 hxy
  · ap

中文:
定理 efixedPoint_eq_of_edist_lt_top'
  结论: (hf : ContractingWith K f) {s : 集合 α} (hsc : 是完备 s)
  证明: by
  refine (hf.eq_or_edist_eq_top_of_fixedPoints ?_ ?_).elim id fun h' => False.elim (ne_of_lt ?_ h')
    <;> try apply efixedPoint_isFixedPt'
  change Metric.edistLtTopSetoid _ _
  trans x
  · apply Setoid.symm'
    apply edist_efixedPoint_lt_top'
  trans y
  · exact lt_top_iff_ne_top.2 hxy
  · ap

Depends on / 依赖: False.elim, Metric, Metric.edistLtTopSetoid, Setoid, Setoid.symm, edistLtTopSetoid, edist_efixedPoint_lt_top, efixedPoint_isFixedPt, eq_or_edist_eq_top_of_fixedPoints, hf.eq_or_edist_eq_top_of_fixedPoints, lt_top_iff_ne_top, ne_of_lt
-/
theorem efixedPoint_eq_of_edist_lt_top' (hf : ContractingWith K f) {s : Set α} (hsc : IsComplete s)
    (hsf : MapsTo f s s) (hfs : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s)
    (hx : edist x (f x) != ∞) {t : Set α} (htc : IsComplete t) (htf : MapsTo f t t)
    (hft : ContractingWith K <| htf.restrict f t t) {y : α} (hyt : y in t) (hy : edist y (f y) != ∞)
    (hxy : edist x y != ∞) :
    efixedPoint' f hsc hsf hfs x hxs hx = efixedPoint' f htc htf hft y hyt hy := by
  refine (hf.eq_or_edist_eq_top_of_fixedPoints ?_ ?_).elim id fun h' => False.elim (ne_of_lt ?_ h')
    <;> try apply efixedPoint_isFixedPt'
  change Metric.edistLtTopSetoid _ _
  trans x
  · apply Setoid.symm'
    apply edist_efixedPoint_lt_top'
  trans y
  · exact lt_top_iff_ne_top.2 hxy
  · apply edist_efixedPoint_lt_top'

end ContractingWith

namespace ContractingWith

variable [MetricSpace α] {K : Real>=0} {f : α -> α}

/--
theorem `one_sub_K_pos` / 定理 `one_sub_K_pos`

English:
theorem one_sub_K_pos
  given: (hf : ContractingWith K f)
  statement: (0 : Real) < 1 - K
  proof: sub_pos.2 hf.1

中文:
定理 one_sub_K_pos
  条件: (hf : ContractingWith K f)
  结论: (0 : 实数) < 1 - K
  证明: sub_pos.2 hf.1

Depends on / 依赖: sub_pos
-/
theorem one_sub_K_pos (hf : ContractingWith K f) : (0 : Real) < 1 - K :=
  sub_pos.2 hf.1

section
variable (hf : ContractingWith K f)
include hf

/--
theorem `dist_le_mul` / 定理 `dist_le_mul`

English:
theorem dist_le_mul
  given: (x y : α)
  statement: dist (f x) (f y) <= K * dist x y
  proof: hf.toLipschitzWith.dist_le_mul x y

中文:
定理 dist_le_mul
  条件: (x y : α)
  结论: dist (f x) (f y) <= K * dist x y
  证明: hf.toLipschitzWith.dist_le_mul x y

Depends on / 依赖: dist_le_mul, hf.toLipschitzWith.dist_le_mul, toLipschitzWith
-/
theorem dist_le_mul (x y : α) : dist (f x) (f y) <= K * dist x y :=
  hf.toLipschitzWith.dist_le_mul x y

/--
theorem `dist_inequality` / 定理 `dist_inequality`

English:
theorem dist_inequality
  given: (x y)
  statement: dist x y <= (dist x (f x) + dist y (f y)) / (1 - K)
  proof: suffices dist x y <= dist x (f x) + dist y (f y) + K * dist x y by
    rwa [le_div_iff₀ hf.one_sub_K_pos, mul_comm, _root_.sub_mul, one_mul, sub_le_iff_le_add]
  calc
    dist x y <= dist x (f x) + dist y (f y) + dist (f x) (f y) := dist_triangle4_right _ _ _ _
    _ <= dist x (f x) + dist y (f y) +

中文:
定理 dist_inequality
  条件: (x y)
  结论: dist x y <= (dist x (f x) + dist y (f y)) / (1 - K)
  证明: suffices dist x y <= dist x (f x) + dist y (f y) + K * dist x y by
    rwa [le_div_iff₀ hf.one_sub_K_pos, mul_comm, _root_.sub_mul, one_mul, sub_le_iff_le_add]
  calc
    dist x y <= dist x (f x) + dist y (f y) + dist (f x) (f y) := dist_triangle4_right _ _ _ _
    _ <= dist x (f x) + dist y (f y) +

Depends on / 依赖: _root_, _root_.sub_mul, dist_le_mul, dist_triangle4_right, hf.dist_le_mul, hf.one_sub_K_pos, mul_comm, one_mul, one_sub_K_pos, sub_le_iff_le_add, sub_mul
-/
theorem dist_inequality (x y) : dist x y <= (dist x (f x) + dist y (f y)) / (1 - K) :=
  suffices dist x y <= dist x (f x) + dist y (f y) + K * dist x y by
    rwa [le_div_iff₀ hf.one_sub_K_pos, mul_comm, _root_.sub_mul, one_mul, sub_le_iff_le_add]
  calc
    dist x y <= dist x (f x) + dist y (f y) + dist (f x) (f y) := dist_triangle4_right _ _ _ _
    _ <= dist x (f x) + dist y (f y) + K * dist x y := by grw [hf.dist_le_mul]

/--
theorem `dist_le_of_fixedPoint` / 定理 `dist_le_of_fixedPoint`

English:
theorem dist_le_of_fixedPoint
  given: (x) {y} (hy : IsFixedPt f y)
  statement: dist x y <= dist x (f x) / (1 - K)
  proof: by
  simpa only [hy.eq, dist_self, add_zero] using hf.dist_inequality x y

中文:
定理 dist_le_of_fixedPoint
  条件: (x) {y} (hy : IsFixedPt f y)
  结论: dist x y <= dist x (f x) / (1 - K)
  证明: by
  simpa only [hy.eq, dist_self, add_zero] using hf.dist_inequality x y

Depends on / 依赖: add_zero, dist_inequality, dist_self, hf.dist_inequality, hy.eq
-/
theorem dist_le_of_fixedPoint (x) {y} (hy : IsFixedPt f y) : dist x y <= dist x (f x) / (1 - K) := by
  simpa only [hy.eq, dist_self, add_zero] using hf.dist_inequality x y

/--
theorem `fixedPoint_unique'` / 定理 `fixedPoint_unique'`

English:
theorem fixedPoint_unique'
  given: {x y} (hx : IsFixedPt f x) (hy : IsFixedPt f y)
  statement: x = y
  proof: (hf.eq_or_edist_eq_top_of_fixedPoints hx hy).resolve_right (edist_ne_top _ _)

中文:
定理 fixedPoint_unique'
  条件: {x y} (hx : IsFixedPt f x) (hy : IsFixedPt f y)
  结论: x = y
  证明: (hf.eq_or_edist_eq_top_of_fixedPoints hx hy).resolve_right (edist_ne_top _ _)

Depends on / 依赖: edist_ne_top, eq_or_edist_eq_top_of_fixedPoints, hf.eq_or_edist_eq_top_of_fixedPoints, resolve_right
-/
theorem fixedPoint_unique' {x y} (hx : IsFixedPt f x) (hy : IsFixedPt f y) : x = y :=
  (hf.eq_or_edist_eq_top_of_fixedPoints hx hy).resolve_right (edist_ne_top _ _)

/--
theorem `dist_fixedPoint_fixedPoint_of_dist_le'` / 定理 `dist_fixedPoint_fixedPoint_of_dist_le'`

English:
theorem dist_fixedPoint_fixedPoint_of_dist_le'
  statement: (g : α -> α) {x y} (hx : IsFixedPt f x)
  proof: calc
    dist x y = dist y x := dist_comm x y
    _ <= dist y (f y) / (1 - K) := hf.dist_le_of_fixedPoint y hx
    _ = dist (f y) (g y) / (1 - K) := by rw [hy.eq, dist_comm]
    _ <= C / (1 - K) := (div_le_div_iff_of_pos_right hf.one_sub_K_pos).2 (hfg y)

中文:
定理 dist_fixedPoint_fixedPoint_of_dist_le'
  结论: (g : α -> α) {x y} (hx : IsFixedPt f x)
  证明: calc
    dist x y = dist y x := dist_comm x y
    _ <= dist y (f y) / (1 - K) := hf.dist_le_of_fixedPoint y hx
    _ = dist (f y) (g y) / (1 - K) := by rw [hy.eq, dist_comm]
    _ <= C / (1 - K) := (div_le_div_iff_of_pos_right hf.one_sub_K_pos).2 (hfg y)

Depends on / 依赖: dist_comm, dist_le_of_fixedPoint, div_le_div_iff_of_pos_right, hf.dist_le_of_fixedPoint, hf.one_sub_K_pos, hy.eq, one_sub_K_pos
-/
theorem dist_fixedPoint_fixedPoint_of_dist_le' (g : α -> α) {x y} (hx : IsFixedPt f x)
    (hy : IsFixedPt g y) {C} (hfg : forall z, dist (f z) (g z) <= C) : dist x y <= C / (1 - K) :=
  calc
    dist x y = dist y x := dist_comm x y
    _ <= dist y (f y) / (1 - K) := hf.dist_le_of_fixedPoint y hx
    _ = dist (f y) (g y) / (1 - K) := by rw [hy.eq, dist_comm]
    _ <= C / (1 - K) := (div_le_div_iff_of_pos_right hf.one_sub_K_pos).2 (hfg y)

variable [Nonempty α] [CompleteSpace α]

variable (f) in
/--
Definition of `fixedPoint` / `fixedPoint` 的定义

English:
definition fixedPoint
  signature: : α
  body: efixedPoint f hf _ (edist_ne_top (Classical.choice ‹Nonempty α›) _)

中文:
定义 fixedPoint
  签名: : α
  定义体: efixedPoint f hf _ (edist_ne_top (Classical.choice ‹Nonempty α›) _)

Depends on / 依赖: Classical, Classical.choice, Nonempty, choice, edist_ne_top, efixedPoint
-/
noncomputable def fixedPoint : α :=
  efixedPoint f hf _ (edist_ne_top (Classical.choice ‹Nonempty α›) _)

/--
theorem `fixedPoint_isFixedPt` / 定理 `fixedPoint_isFixedPt`

English:
theorem fixedPoint_isFixedPt
  statement: IsFixedPt f (fixedPoint f hf)
  proof: hf.efixedPoint_isFixedPt _

中文:
定理 fixedPoint_isFixedPt
  结论: IsFixedPt f (fixedPoint f hf)
  证明: hf.efixedPoint_isFixedPt _

Depends on / 依赖: efixedPoint_isFixedPt, hf.efixedPoint_isFixedPt
-/
theorem fixedPoint_isFixedPt : IsFixedPt f (fixedPoint f hf) :=
  hf.efixedPoint_isFixedPt _

/--
theorem `fixedPoint_unique` / 定理 `fixedPoint_unique`

English:
theorem fixedPoint_unique
  given: {x} (hx : IsFixedPt f x)
  statement: x = fixedPoint f hf
  proof: hf.fixedPoint_unique' hx hf.fixedPoint_isFixedPt

中文:
定理 fixedPoint_unique
  条件: {x} (hx : IsFixedPt f x)
  结论: x = fixedPoint f hf
  证明: hf.fixedPoint_unique' hx hf.fixedPoint_isFixedPt

Depends on / 依赖: fixedPoint_isFixedPt, fixedPoint_unique, hf.fixedPoint_isFixedPt, hf.fixedPoint_unique
-/
theorem fixedPoint_unique {x} (hx : IsFixedPt f x) : x = fixedPoint f hf :=
  hf.fixedPoint_unique' hx hf.fixedPoint_isFixedPt

/--
theorem `dist_fixedPoint_le` / 定理 `dist_fixedPoint_le`

English:
theorem dist_fixedPoint_le
  given: (x)
  statement: dist x (fixedPoint f hf) <= dist x (f x) / (1 - K)
  proof: hf.dist_le_of_fixedPoint x hf.fixedPoint_isFixedPt

中文:
定理 dist_fixedPoint_le
  条件: (x)
  结论: dist x (fixedPoint f hf) <= dist x (f x) / (1 - K)
  证明: hf.dist_le_of_fixedPoint x hf.fixedPoint_isFixedPt

Depends on / 依赖: dist_le_of_fixedPoint, fixedPoint_isFixedPt, hf.dist_le_of_fixedPoint, hf.fixedPoint_isFixedPt
-/
theorem dist_fixedPoint_le (x) : dist x (fixedPoint f hf) <= dist x (f x) / (1 - K) :=
  hf.dist_le_of_fixedPoint x hf.fixedPoint_isFixedPt

/--
theorem `aposteriori_dist_iterate_fixedPoint_le` / 定理 `aposteriori_dist_iterate_fixedPoint_le`

English:
theorem aposteriori_dist_iterate_fixedPoint_le
  given: (x n)
  proof: by
  rw [iterate_succ']
  apply hf.dist_fixedPoint_le

中文:
定理 aposteriori_dist_iterate_fixedPoint_le
  条件: (x n)
  证明: by
  rw [iterate_succ']
  apply hf.dist_fixedPoint_le

Depends on / 依赖: dist_fixedPoint_le, hf.dist_fixedPoint_le, iterate_succ
-/
theorem aposteriori_dist_iterate_fixedPoint_le (x n) :
    dist (f^[n] x) (fixedPoint f hf) <= dist (f^[n] x) (f^[n + 1] x) / (1 - K) := by
  rw [iterate_succ']
  apply hf.dist_fixedPoint_le

/--
theorem `apriori_dist_iterate_fixedPoint_le` / 定理 `apriori_dist_iterate_fixedPoint_le`

English:
theorem apriori_dist_iterate_fixedPoint_le
  given: (x n)
  proof: calc
    _ <= dist (f^[n] x) (f^[n + 1] x) / (1 - K) := hf.aposteriori_dist_iterate_fixedPoint_le x n
    _ <= _ := by
      gcongr; exacts [hf.one_sub_K_pos.le, hf.toLipschitzWith.dist_iterate_succ_le_geometric x n]

中文:
定理 apriori_dist_iterate_fixedPoint_le
  条件: (x n)
  证明: calc
    _ <= dist (f^[n] x) (f^[n + 1] x) / (1 - K) := hf.aposteriori_dist_iterate_fixedPoint_le x n
    _ <= _ := by
      gcongr; exacts [hf.one_sub_K_pos.le, hf.toLipschitzWith.dist_iterate_succ_le_geometric x n]

Depends on / 依赖: aposteriori_dist_iterate_fixedPoint_le, dist_iterate_succ_le_geometric, exacts, hf.aposteriori_dist_iterate_fixedPoint_le, hf.one_sub_K_pos.le, hf.toLipschitzWith.dist_iterate_succ_le_geometric, one_sub_K_pos, toLipschitzWith
-/
theorem apriori_dist_iterate_fixedPoint_le (x n) :
    dist (f^[n] x) (fixedPoint f hf) <= dist x (f x) * (K : Real) ^ n / (1 - K) :=
  calc
    _ <= dist (f^[n] x) (f^[n + 1] x) / (1 - K) := hf.aposteriori_dist_iterate_fixedPoint_le x n
    _ <= _ := by
      gcongr; exacts [hf.one_sub_K_pos.le, hf.toLipschitzWith.dist_iterate_succ_le_geometric x n]

/--
theorem `tendsto_iterate_fixedPoint` / 定理 `tendsto_iterate_fixedPoint`

English:
theorem tendsto_iterate_fixedPoint
  given: (x)
  proof: by
  convert! tendsto_iterate_efixedPoint hf (edist_ne_top x _)
  refine (fixedPoint_unique _ ?_).symm
  apply efixedPoint_isFixedPt

中文:
定理 tendsto_iterate_fixedPoint
  条件: (x)
  证明: by
  convert! tendsto_iterate_efixedPoint hf (edist_ne_top x _)
  refine (fixedPoint_unique _ ?_).symm
  apply efixedPoint_isFixedPt

Depends on / 依赖: convert, edist_ne_top, efixedPoint_isFixedPt, fixedPoint_unique, tendsto_iterate_efixedPoint
-/
theorem tendsto_iterate_fixedPoint (x) :
    Tendsto (fun n => f^[n] x) atTop (𝓝 <| fixedPoint f hf) := by
  convert! tendsto_iterate_efixedPoint hf (edist_ne_top x _)
  refine (fixedPoint_unique _ ?_).symm
  apply efixedPoint_isFixedPt

/--
theorem `fixedPoint_lipschitz_in_map` / 定理 `fixedPoint_lipschitz_in_map`

English:
theorem fixedPoint_lipschitz_in_map
  statement: {g : α -> α} (hg : ContractingWith K g) {C}
  proof: hf.dist_fixedPoint_fixedPoint_of_dist_le' g hf.fixedPoint_isFixedPt hg.fixedPoint_isFixedPt hfg

中文:
定理 fixedPoint_lipschitz_in_map
  结论: {g : α -> α} (hg : ContractingWith K g) {C}
  证明: hf.dist_fixedPoint_fixedPoint_of_dist_le' g hf.fixedPoint_isFixedPt hg.fixedPoint_isFixedPt hfg

Depends on / 依赖: dist_fixedPoint_fixedPoint_of_dist_le, fixedPoint_isFixedPt, hf.dist_fixedPoint_fixedPoint_of_dist_le, hf.fixedPoint_isFixedPt, hg.fixedPoint_isFixedPt
-/
theorem fixedPoint_lipschitz_in_map {g : α -> α} (hg : ContractingWith K g) {C}
    (hfg : forall z, dist (f z) (g z) <= C) : dist (fixedPoint f hf) (fixedPoint g hg) <= C / (1 - K) :=
  hf.dist_fixedPoint_fixedPoint_of_dist_le' g hf.fixedPoint_isFixedPt hg.fixedPoint_isFixedPt hfg

end

variable [Nonempty α] [CompleteSpace α]

/--
theorem `isFixedPt_fixedPoint_iterate` / 定理 `isFixedPt_fixedPoint_iterate`

English:
theorem isFixedPt_fixedPoint_iterate
  given: {n : Nat} (hf : ContractingWith K f^[n])
  proof: by
  set x := hf.fixedPoint f^[n]
  have hx : f^[n] x = x := hf.fixedPoint_isFixedPt
  have := hf.toLipschitzWith.dist_le_mul x (f x)
  rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [hx] at this
  contrapose! this
simpa using mul_lt_mul_of_pos_right (NNReal.coe_lt_one.2 hf.left) dist_pos.2

中文:
定理 isFixedPt_fixedPoint_iterate
  条件: {n : 自然数} (hf : ContractingWith K f^[n])
  证明: by
  set x := hf.fixedPoint f^[n]
  have hx : f^[n] x = x := hf.fixedPoint_isFixedPt
  have := hf.toLipschitzWith.dist_le_mul x (f x)
  rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [hx] at this
  contrapose! this
simpa using mul_lt_mul_of_pos_right (NNReal.coe_lt_one.2 hf.left) dist_pos.2

Depends on / 依赖: NNReal, NNReal.coe_lt_one, Ne.symm, coe_lt_one, contrapose, dist_le_mul, dist_pos, fixedPoint, fixedPoint_isFixedPt, hf.fixedPoint, hf.fixedPoint_isFixedPt, hf.left, hf.toLipschitzWith.dist_le_mul, iterate_succ_apply, mul_lt_mul_of_pos_right, toLipschitzWith
-/
theorem isFixedPt_fixedPoint_iterate {n : Nat} (hf : ContractingWith K f^[n]) :
    IsFixedPt f (hf.fixedPoint f^[n]) := by
  set x := hf.fixedPoint f^[n]
  have hx : f^[n] x = x := hf.fixedPoint_isFixedPt
  have := hf.toLipschitzWith.dist_le_mul x (f x)
  rw [← iterate_succ_apply]; rw [iterate_succ_apply']; rw [hx] at this
  contrapose! this
simpa using mul_lt_mul_of_pos_right (NNReal.coe_lt_one.2 hf.left) dist_pos.2 (Ne.symm this)

end ContractingWith
