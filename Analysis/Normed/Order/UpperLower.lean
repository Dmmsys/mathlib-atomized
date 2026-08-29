/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Field.Pi
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Topology.Algebra.Order.UpperLower
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Upper/lower/order-connected sets in normed groups

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

We also prove lemmas specific to `ℝⁿ`. Those are helpful to prove that order-connected sets in `ℝⁿ`
are measurable.

## TODO

Is there a way to generalise `IsClosed.upperClosure_pi`/`IsClosed.lowerClosure_pi` so that they also
apply to `ℝ`, `ℝ × ℝ`, `EuclideanSpace ι ℝ`? `_pi` has been appended to their names to disambiguate
from the other possible lemmas, but we will want there to be a single set of lemmas for all
situations.
-/

public section

open Bornology Function Metric Set
open scoped Pointwise

variable {α ι : Type*}

section NormedOrderedGroup
variable [NormedCommGroup α] [Preorder α] [IsOrderedMonoid α] {s : Set α}

@[to_additive IsUpperSet.thickening]
/--
theorem `IsUpperSet.thickening'` / 定理 `IsUpperSet.thickening'`

English:
theorem IsUpperSet.thickening'
  given: (hs : IsUpperSet s) (ε : Real)
  proof: by
  rw [← ball_mul_one]
  exact hs.mul_left

@[to_additive IsLowerSet.thickening]

中文:
定理 是上集.thickening'
  条件: (hs : 是上集 s) (ε : 实数)
  证明: by
  rw [← ball_mul_one]
  exact hs.mul_left

@[to_additive IsLowerSet.thickening]
-/
protected theorem IsUpperSet.thickening' (hs : IsUpperSet s) (ε : Real) :
    IsUpperSet (thickening ε s) := by
  rw [← ball_mul_one]
  exact hs.mul_left

@[to_additive IsLowerSet.thickening]
/--
theorem `IsLowerSet.thickening'` / 定理 `IsLowerSet.thickening'`

English:
theorem IsLowerSet.thickening'
  given: (hs : IsLowerSet s) (ε : Real)
  proof: by
  rw [← ball_mul_one]
  exact hs.mul_left

@[to_additive IsUpperSet.cthickening]

中文:
定理 是下集.thickening'
  条件: (hs : 是下集 s) (ε : 实数)
  证明: by
  rw [← ball_mul_one]
  exact hs.mul_left

@[to_additive IsUpperSet.cthickening]
-/
protected theorem IsLowerSet.thickening' (hs : IsLowerSet s) (ε : Real) :
    IsLowerSet (thickening ε s) := by
  rw [← ball_mul_one]
  exact hs.mul_left

@[to_additive IsUpperSet.cthickening]
/--
theorem `IsUpperSet.cthickening'` / 定理 `IsUpperSet.cthickening'`

English:
theorem IsUpperSet.cthickening'
  given: (hs : IsUpperSet s) (ε : Real)
  proof: by
  rw [cthickening_eq_iInter_thickening'']
  exact isUpperSet_iInter₂ fun δ _ => hs.thickening' _

@[to_additive IsLowerSet.cthickening]

中文:
定理 是上集.cthickening'
  条件: (hs : 是上集 s) (ε : 实数)
  证明: by
  rw [cthickening_eq_iInter_thickening'']
  exact isUpperSet_iInter₂ fun δ _ => hs.thickening' _

@[to_additive IsLowerSet.cthickening]
-/
protected theorem IsUpperSet.cthickening' (hs : IsUpperSet s) (ε : Real) :
    IsUpperSet (cthickening ε s) := by
  rw [cthickening_eq_iInter_thickening'']
  exact isUpperSet_iInter₂ fun δ _ => hs.thickening' _

@[to_additive IsLowerSet.cthickening]
/--
theorem `IsLowerSet.cthickening'` / 定理 `IsLowerSet.cthickening'`

English:
theorem IsLowerSet.cthickening'
  given: (hs : IsLowerSet s) (ε : Real)
  proof: by
  rw [cthickening_eq_iInter_thickening'']
  exact isLowerSet_iInter₂ fun δ _ => hs.thickening' _

中文:
定理 是下集.cthickening'
  条件: (hs : 是下集 s) (ε : 实数)
  证明: by
  rw [cthickening_eq_iInter_thickening'']
  exact isLowerSet_iInter₂ fun δ _ => hs.thickening' _
-/
protected theorem IsLowerSet.cthickening' (hs : IsLowerSet s) (ε : Real) :
    IsLowerSet (cthickening ε s) := by
  rw [cthickening_eq_iInter_thickening'']
  exact isLowerSet_iInter₂ fun δ _ => hs.thickening' _

/--
lemma `upperClosure_interior_subset'` / 引理 `upperClosure_interior_subset'`

English:
lemma upperClosure_interior_subset'
  given: (s : Set α)
  proof: upperClosure_min (interior_mono subset_upperClosure) (upperClosure s).upper.interior

中文:
引理 upperClosure_interior_subset'
  条件: (s : 集合 α)
  证明: upperClosure_min (interior_mono subset_upperClosure) (upperClosure s).upper.interior
-/
@[to_additive upperClosure_interior_subset] lemma upperClosure_interior_subset' (s : Set α) :
    (upperClosure (interior s) : Set α) subseteq interior (upperClosure s) :=
  upperClosure_min (interior_mono subset_upperClosure) (upperClosure s).upper.interior

/--
lemma `lowerClosure_interior_subset'` / 引理 `lowerClosure_interior_subset'`

English:
lemma lowerClosure_interior_subset'
  given: (s : Set α)
  proof: lowerClosure_min (interior_mono subset_lowerClosure) (lowerClosure s).lower.interior

中文:
引理 lowerClosure_interior_subset'
  条件: (s : 集合 α)
  证明: lowerClosure_min (interior_mono subset_lowerClosure) (lowerClosure s).lower.interior
-/
@[to_additive lowerClosure_interior_subset] lemma lowerClosure_interior_subset' (s : Set α) :
    (lowerClosure (interior s) : Set α) subseteq interior (lowerClosure s) :=
  lowerClosure_min (interior_mono subset_lowerClosure) (lowerClosure s).lower.interior

end NormedOrderedGroup

/-! ### `ℝⁿ` -/


section Finite
variable [Finite ι] {s : Set (ι -> Real)} {x y : ι -> Real}

/--
theorem `IsUpperSet.mem_interior_of_forall_lt` / 定理 `IsUpperSet.mem_interior_of_forall_lt`

English:
theorem IsUpperSet.mem_interior_of_forall_lt
  statement: (hs : IsUpperSet s) (hx : x in closure s)
  proof: by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : forall i, z i < y i := by
    refine fun i => (hxy _).trans_le' (sub_le_iff_le_add'.1 <| (le_abs_self _).trans ?

中文:
定理 是上集.mem_interior_of_对任意_lt
  结论: (hs : 是上集 s) (hx : x in closure s)
  证明: by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : forall i, z i < y i := by
    refine fun i => (hxy _).trans_le' (sub_le_iff_le_add'.1 <| (le_abs_self _).trans ?

Depends on / 依赖: Metric, Metric.mem_closure_iff, Pi.exists_forall_pos_add_lt, Real.norm_eq_abs, dist_eq_norm, dist_pi_lt_iff, exists_forall_pos_add_lt, isOpen_ball, le_abs_self, mem_ball_self, mem_closure_iff, mem_interior, nonempty_fintype, norm_eq_abs, sub_le_iff_le_add, trans_le
-/
theorem IsUpperSet.mem_interior_of_forall_lt (hs : IsUpperSet s) (hx : x in closure s)
    (h : forall i, x i < y i) : y in interior s := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : forall i, z i < y i := by
    refine fun i => (hxy _).trans_le' (sub_le_iff_le_add'.1 <| (le_abs_self _).trans ?_)
    rw [← Real.norm_eq_abs]; rw [← dist_eq_norm']
    exact (hxz _).le
  obtain ⟨δ, hδ, hyz⟩ := Pi.exists_forall_pos_add_lt hyz
  refine mem_interior.2 ⟨ball y δ, ?_, isOpen_ball, mem_ball_self hδ⟩
  rintro w hw
  refine hs (fun i => ?_) hz
  simp_rw [ball_pi _ hδ, Real.ball_eq_Ioo] at hw
  exact ((lt_sub_iff_add_lt.2 <| hyz _).trans (hw _ <| mem_univ _).1).le

/--
theorem `IsLowerSet.mem_interior_of_forall_lt` / 定理 `IsLowerSet.mem_interior_of_forall_lt`

English:
theorem IsLowerSet.mem_interior_of_forall_lt
  statement: (hs : IsLowerSet s) (hx : x in closure s)
  proof: by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : forall i, y i < z i := by
    refine fun i =>
      (lt_sub_iff_add_lt.2 <| hxy _).trans_le (sub_le_comm.1 <| (l

中文:
定理 是下集.mem_interior_of_对任意_lt
  结论: (hs : 是下集 s) (hx : x in closure s)
  证明: by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : forall i, y i < z i := by
    refine fun i =>
      (lt_sub_iff_add_lt.2 <| hxy _).trans_le (sub_le_comm.1 <| (l

Depends on / 依赖: Metric, Metric.mem_closure_iff, Pi.exists_forall_pos_add_lt, Real.norm_eq_abs, dist_eq_norm, dist_pi_lt_iff, exists_forall_pos_add_lt, isOpen_ball, le_abs_self, lt_sub_iff_add_lt, mem_ball_self, mem_closure_iff, mem_interior, nonempty_fintype, norm_eq_abs, sub_le_comm, trans_le
-/
theorem IsLowerSet.mem_interior_of_forall_lt (hs : IsLowerSet s) (hx : x in closure s)
    (h : forall i, y i < x i) : y in interior s := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : forall i, y i < z i := by
    refine fun i =>
      (lt_sub_iff_add_lt.2 <| hxy _).trans_le (sub_le_comm.1 <| (le_abs_self _).trans ?_)
    rw [← Real.norm_eq_abs]; rw [← dist_eq_norm]
    exact (hxz _).le
  obtain ⟨δ, hδ, hyz⟩ := Pi.exists_forall_pos_add_lt hyz
  refine mem_interior.2 ⟨ball y δ, ?_, isOpen_ball, mem_ball_self hδ⟩
  rintro w hw
  refine hs (fun i => ?_) hz
  simp_rw [ball_pi _ hδ, Real.ball_eq_Ioo] at hw
  exact ((hw _ <| mem_univ _).2.trans <| hyz _).le

end Finite

section Fintype
variable [Fintype ι] {s : Set (ι -> Real)} {a₁ a₂ b₁ b₂ x y : ι -> Real} {δ : Real}

-- TODO: Generalise those lemmas so that they also apply to `ℝ` and `EuclideanSpace ι ℝ`
/--
lemma `dist_inf_sup_pi` / 引理 `dist_inf_sup_pi`

English:
lemma dist_inf_sup_pi
  given: (x y : ι -> Real)
  statement: dist (x ⊓ y) (x ⊔ y) = dist x y
  proof: by
  refine congr_arg NNReal.toReal (Finset.sup_congr rfl fun i _ => ?_)
  simp only [Real.nndist_eq', max_sub_min_eq_abs, Pi.inf_apply,
    Pi.sup_apply, Real.nnabs_of_nonneg, abs_nonneg, Real.toNNReal_abs]

中文:
引理 dist_inf_sup_pi
  条件: (x y : ι -> 实数)
  结论: dist (x ⊓ y) (x ⊔ y) = dist x y
  证明: by
  refine congr_arg NNReal.toReal (Finset.sup_congr rfl fun i _ => ?_)
  simp only [Real.nndist_eq', max_sub_min_eq_abs, Pi.inf_apply,
    Pi.sup_apply, Real.nnabs_of_nonneg, abs_nonneg, Real.toNNReal_abs]

Depends on / 依赖: Finset, Finset.sup_congr, NNReal, NNReal.toReal, Pi.inf_apply, Pi.sup_apply, Real.nnabs_of_nonneg, Real.nndist_eq, Real.toNNReal_abs, abs_nonneg, congr_arg, inf_apply, max_sub_min_eq_abs, nnabs_of_nonneg, nndist_eq, sup_apply, sup_congr, toNNReal_abs, toReal
-/
lemma dist_inf_sup_pi (x y : ι -> Real) : dist (x ⊓ y) (x ⊔ y) = dist x y := by
  refine congr_arg NNReal.toReal (Finset.sup_congr rfl fun i _ => ?_)
  simp only [Real.nndist_eq', max_sub_min_eq_abs, Pi.inf_apply,
    Pi.sup_apply, Real.nnabs_of_nonneg, abs_nonneg, Real.toNNReal_abs]

/--
lemma `dist_mono_left_pi` / 引理 `dist_mono_left_pi`

English:
lemma dist_mono_left_pi
  statement: MonotoneOn (dist · y) (Ici y)
  proof: by
  refine fun y₁ hy₁ y₂ hy₂ hy => NNReal.coe_le_coe.2 (Finset.sup_mono_fun fun i _ => ?_)
  rw [Real.nndist_eq]; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹y <= _› i : y i <= y₁ i))]; rw [Real.nndist_eq]; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹y <= _› i : y i <= y₂ i))]
  grw [hy i] -- TOD

中文:
引理 dist_mono_left_pi
  结论: MonotoneOn (dist · y) (左闭右无界区间 y)
  证明: by
  refine fun y₁ hy₁ y₂ hy₂ hy => NNReal.coe_le_coe.2 (Finset.sup_mono_fun fun i _ => ?_)
  rw [Real.nndist_eq]; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹y <= _› i : y i <= y₁ i))]; rw [Real.nndist_eq]; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹y <= _› i : y i <= y₂ i))]
  grw [hy i] -- TOD

Depends on / 依赖: Finset, Finset.sup_mono_fun, NNReal, NNReal.coe_le_coe, Real.nnabs_of_nonneg, Real.nndist_eq, coe_le_coe, nnabs_of_nonneg, nndist_eq, sub_nonneg_of_le, sup_mono_fun
-/
lemma dist_mono_left_pi : MonotoneOn (dist · y) (Ici y) := by
  refine fun y₁ hy₁ y₂ hy₂ hy => NNReal.coe_le_coe.2 (Finset.sup_mono_fun fun i _ => ?_)
  rw [Real.nndist_eq]; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹y <= _› i : y i <= y₁ i))]; rw [Real.nndist_eq]; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹y <= _› i : y i <= y₂ i))]
  grw [hy i] -- TODO(gcongr): we would like `grw [hy]` to work here

/--
lemma `dist_mono_right_pi` / 引理 `dist_mono_right_pi`

English:
lemma dist_mono_right_pi
  statement: MonotoneOn (dist x) (Ici x)
  proof: by
  simpa only [dist_comm] using dist_mono_left_pi (y := x)

中文:
引理 dist_mono_right_pi
  结论: MonotoneOn (dist x) (左闭右无界区间 x)
  证明: by
  simpa only [dist_comm] using dist_mono_left_pi (y := x)

Depends on / 依赖: dist_comm, dist_mono_left_pi
-/
lemma dist_mono_right_pi : MonotoneOn (dist x) (Ici x) := by
  simpa only [dist_comm] using dist_mono_left_pi (y := x)

/--
lemma `dist_anti_left_pi` / 引理 `dist_anti_left_pi`

English:
lemma dist_anti_left_pi
  statement: AntitoneOn (dist · y) (Iic y)
  proof: by
  refine fun y₁ hy₁ y₂ hy₂ hy => NNReal.coe_le_coe.2 (Finset.sup_mono_fun fun i _ => ?_)
  rw [Real.nndist_eq']; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ <= y› i : y₂ i <= y i))]; rw [Real.nndist_eq']; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ <= y› i : y₁ i <= y i))]
  exact Real.toNN

中文:
引理 dist_anti_left_pi
  结论: AntitoneOn (dist · y) (左无界右闭区间 y)
  证明: by
  refine fun y₁ hy₁ y₂ hy₂ hy => NNReal.coe_le_coe.2 (Finset.sup_mono_fun fun i _ => ?_)
  rw [Real.nndist_eq']; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ <= y› i : y₂ i <= y i))]; rw [Real.nndist_eq']; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ <= y› i : y₁ i <= y i))]
  exact Real.toNN

Depends on / 依赖: Finset, Finset.sup_mono_fun, NNReal, NNReal.coe_le_coe, Real.nnabs_of_nonneg, Real.nndist_eq, Real.toNNReal_mono, coe_le_coe, nnabs_of_nonneg, nndist_eq, sub_le_sub_left, sub_nonneg_of_le, sup_mono_fun, toNNReal_mono
-/
lemma dist_anti_left_pi : AntitoneOn (dist · y) (Iic y) := by
  refine fun y₁ hy₁ y₂ hy₂ hy => NNReal.coe_le_coe.2 (Finset.sup_mono_fun fun i _ => ?_)
  rw [Real.nndist_eq']; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ <= y› i : y₂ i <= y i))]; rw [Real.nndist_eq']; rw [Real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ <= y› i : y₁ i <= y i))]
  exact Real.toNNReal_mono (sub_le_sub_left (hy _) _)

/--
lemma `dist_anti_right_pi` / 引理 `dist_anti_right_pi`

English:
lemma dist_anti_right_pi
  statement: AntitoneOn (dist x) (Iic x)
  proof: by
  simpa only [dist_comm] using dist_anti_left_pi (y := x)

中文:
引理 dist_anti_right_pi
  结论: AntitoneOn (dist x) (左无界右闭区间 x)
  证明: by
  simpa only [dist_comm] using dist_anti_left_pi (y := x)

Depends on / 依赖: dist_anti_left_pi, dist_comm
-/
lemma dist_anti_right_pi : AntitoneOn (dist x) (Iic x) := by
  simpa only [dist_comm] using dist_anti_left_pi (y := x)

/--
lemma `dist_le_dist_of_le_pi` / 引理 `dist_le_dist_of_le_pi`

English:
lemma dist_le_dist_of_le_pi
  given: (ha : a₂ <= a₁) (h₁ : a₁ <= b₁) (hb : b₁ <= b₂)
  proof: (dist_mono_right_pi h₁ (h₁.trans hb) hb).trans
    dist_anti_left_pi (ha.trans <| h₁.trans hb) (h₁.trans hb) ha

中文:
引理 dist_le_dist_of_le_pi
  条件: (ha : a₂ <= a₁) (h₁ : a₁ <= b₁) (hb : b₁ <= b₂)
  证明: (dist_mono_right_pi h₁ (h₁.trans hb) hb).trans
    dist_anti_left_pi (ha.trans <| h₁.trans hb) (h₁.trans hb) ha

Depends on / 依赖: dist_anti_left_pi, dist_mono_right_pi, ha.trans
-/
lemma dist_le_dist_of_le_pi (ha : a₂ <= a₁) (h₁ : a₁ <= b₁) (hb : b₁ <= b₂) :
    dist a₁ b₁ <= dist a₂ b₂ :=
(dist_mono_right_pi h₁ (h₁.trans hb) hb).trans
    dist_anti_left_pi (ha.trans <| h₁.trans hb) (h₁.trans hb) ha

/--
theorem `IsUpperSet.exists_subset_ball` / 定理 `IsUpperSet.exists_subset_ball`

English:
theorem IsUpperSet.exists_subset_ball
  given: (hs : IsUpperSet s) (hx : x in closure s) (hδ : 0 < δ)
  proof: by
  refine ⟨x + const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · grw [dist_self_add_left, ← const_def, pi_norm_const_le]
    apply le_of_eq
    simp [abs_of_nonneg, hδ.le]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs

中文:
定理 是上集.存在_subset_ball
  条件: (hs : 是上集 s) (hx : x in closure s) (hδ : 0 < δ)
  证明: by
  refine ⟨x + const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · grw [dist_self_add_left, ← const_def, pi_norm_const_le]
    apply le_of_eq
    simp [abs_of_nonneg, hδ.le]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs

Depends on / 依赖: Metric, Metric.mem_closure_iff, abs_of_nonneg, closedBall_subset_closedBall, const_def, dist_eq_norm, dist_self_add_left, div_pos, hs.mem_interior_of_forall_lt, hxy.le, le_of_eq, mem_closedBall, mem_closure_iff, mem_interior_of_forall_lt, norm_le_pi_norm, pi_norm_const_le, replace, subset_closure, zero_lt_four
-/
theorem IsUpperSet.exists_subset_ball (hs : IsUpperSet s) (hx : x in closure s) (hδ : 0 < δ) :
    exists y, closedBall y (δ / 4) subseteq closedBall x δ ∧ closedBall y (δ / 4) subseteq interior s := by
  refine ⟨x + const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · grw [dist_self_add_left, ← const_def, pi_norm_const_le]
    apply le_of_eq
    simp [abs_of_nonneg, hδ.le]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs.mem_interior_of_forall_lt (subset_closure hy) fun i => ?_
  rw [mem_closedBall]; rw [dist_eq_norm'] at hz
  rw [dist_eq_norm] at hxy
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le
  replace hz := (norm_le_pi_norm _ i).trans hz
  dsimp at hxy hz
  rw [abs_sub_le_iff] at hxy hz
  linarith

/--
theorem `IsLowerSet.exists_subset_ball` / 定理 `IsLowerSet.exists_subset_ball`

English:
theorem IsLowerSet.exists_subset_ball
  given: (hs : IsLowerSet s) (hx : x in closure s) (hδ : 0 < δ)
  proof: by
  refine ⟨x - const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · grw [dist_self_sub_left, ← const_def, pi_norm_const_le]
    apply le_of_eq
    simp [abs_of_nonneg, hδ.le]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs

中文:
定理 是下集.存在_subset_ball
  条件: (hs : 是下集 s) (hx : x in closure s) (hδ : 0 < δ)
  证明: by
  refine ⟨x - const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · grw [dist_self_sub_left, ← const_def, pi_norm_const_le]
    apply le_of_eq
    simp [abs_of_nonneg, hδ.le]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs

Depends on / 依赖: Metric, Metric.mem_closure_iff, abs_of_nonneg, closedBall_subset_closedBall, const_def, dist_eq_norm, dist_self_sub_left, div_pos, hs.mem_interior_of_forall_lt, hxy.le, le_of_eq, mem_closedBall, mem_closure_iff, mem_interior_of_forall_lt, norm_le_pi_norm, pi_norm_const_le, replace, subset_closure, zero_lt_four
-/
theorem IsLowerSet.exists_subset_ball (hs : IsLowerSet s) (hx : x in closure s) (hδ : 0 < δ) :
    exists y, closedBall y (δ / 4) subseteq closedBall x δ ∧ closedBall y (δ / 4) subseteq interior s := by
  refine ⟨x - const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · grw [dist_self_sub_left, ← const_def, pi_norm_const_le]
    apply le_of_eq
    simp [abs_of_nonneg, hδ.le]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs.mem_interior_of_forall_lt (subset_closure hy) fun i => ?_
  rw [mem_closedBall]; rw [dist_eq_norm'] at hz
  rw [dist_eq_norm] at hxy
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le
  replace hz := (norm_le_pi_norm _ i).trans hz
  dsimp at hxy hz
  rw [abs_sub_le_iff] at hxy hz
  linarith

end Fintype

section Finite
variable [Finite ι] {s : Set (ι -> Real)}


/--
lemma `IsClosed.upperClosure_pi` / 引理 `IsClosed.upperClosure_pi`

English:
lemma IsClosed.upperClosure_pi
  given: (hs : IsClosed s) (hs' : BddBelow s)
  proof: by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx => ?_
  choose g hg hgf using hf
  obtain ⟨a, ha⟩ := hx.bddAbove_range
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.isBounded_inter bddAbove_Iic) fun n =>
⟨hg n, (hgf _).trans ha mem_range_self _⟩
  exact ⟨b,

中文:
引理 是闭集.upperClosure_pi
  条件: (hs : 是闭集 s) (hs' : BddBelow s)
  证明: by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx => ?_
  choose g hg hgf using hf
  obtain ⟨a, ha⟩ := hx.bddAbove_range
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.isBounded_inter bddAbove_Iic) fun n =>
⟨hg n, (hgf _).trans ha mem_range_self _⟩
  exact ⟨b,
-/
protected lemma IsClosed.upperClosure_pi (hs : IsClosed s) (hs' : BddBelow s) :
    IsClosed (upperClosure s : Set (ι -> Real)) := by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx => ?_
  choose g hg hgf using hf
  obtain ⟨a, ha⟩ := hx.bddAbove_range
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.isBounded_inter bddAbove_Iic) fun n =>
⟨hg n, (hgf _).trans ha mem_range_self _⟩
  exact ⟨b, closure_minimal inter_subset_left hs hb,
    le_of_tendsto_of_tendsto' hbf (hx.comp hφ.tendsto_atTop) fun _ => hgf _⟩

/--
lemma `IsClosed.lowerClosure_pi` / 引理 `IsClosed.lowerClosure_pi`

English:
lemma IsClosed.lowerClosure_pi
  given: (hs : IsClosed s) (hs' : BddAbove s)
  proof: by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx => ?_
  choose g hg hfg using hf
  have : BoundedGENhdsClass Real := by infer_instance
  obtain ⟨a, ha⟩ := hx.bddBelow_range
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.isBounded_inter bddBelow_Ici) fun n =>

中文:
引理 是闭集.lowerClosure_pi
  条件: (hs : 是闭集 s) (hs' : BddAbove s)
  证明: by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx => ?_
  choose g hg hfg using hf
  have : BoundedGENhdsClass Real := by infer_instance
  obtain ⟨a, ha⟩ := hx.bddBelow_range
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.isBounded_inter bddBelow_Ici) fun n =>
-/
protected lemma IsClosed.lowerClosure_pi (hs : IsClosed s) (hs' : BddAbove s) :
    IsClosed (lowerClosure s : Set (ι -> Real)) := by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx => ?_
  choose g hg hfg using hf
  have : BoundedGENhdsClass Real := by infer_instance
  obtain ⟨a, ha⟩ := hx.bddBelow_range
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.isBounded_inter bddBelow_Ici) fun n =>
⟨hg n, (ha <| mem_range_self _).trans hfg _⟩
  exact ⟨b, closure_minimal inter_subset_left hs hb,
    le_of_tendsto_of_tendsto' (hx.comp hφ.tendsto_atTop) hbf fun _ => hfg _⟩

/--
lemma `IsClopen.upperClosure_pi` / 引理 `IsClopen.upperClosure_pi`

English:
lemma IsClopen.upperClosure_pi
  given: (hs : IsClopen s) (hs' : BddBelow s)
  proof: ⟨hs.1.upperClosure_pi hs', hs.2.upperClosure⟩

中文:
引理 IsClopen.upperClosure_pi
  条件: (hs : IsClopen s) (hs' : BddBelow s)
  证明: ⟨hs.1.upperClosure_pi hs', hs.2.upperClosure⟩
-/
protected lemma IsClopen.upperClosure_pi (hs : IsClopen s) (hs' : BddBelow s) :
    IsClopen (upperClosure s : Set (ι -> Real)) := ⟨hs.1.upperClosure_pi hs', hs.2.upperClosure⟩

/--
lemma `IsClopen.lowerClosure_pi` / 引理 `IsClopen.lowerClosure_pi`

English:
lemma IsClopen.lowerClosure_pi
  given: (hs : IsClopen s) (hs' : BddAbove s)
  proof: ⟨hs.1.lowerClosure_pi hs', hs.2.lowerClosure⟩

中文:
引理 IsClopen.lowerClosure_pi
  条件: (hs : IsClopen s) (hs' : BddAbove s)
  证明: ⟨hs.1.lowerClosure_pi hs', hs.2.lowerClosure⟩
-/
protected lemma IsClopen.lowerClosure_pi (hs : IsClopen s) (hs' : BddAbove s) :
    IsClopen (lowerClosure s : Set (ι -> Real)) := ⟨hs.1.lowerClosure_pi hs', hs.2.lowerClosure⟩

/--
lemma `closure_upperClosure_comm_pi` / 引理 `closure_upperClosure_comm_pi`

English:
lemma closure_upperClosure_comm_pi
  given: (hs : BddBelow s)
  proof: (closure_minimal (upperClosure_anti subset_closure) <|
      isClosed_closure.upperClosure_pi hs.closure).antisymm <|
    upperClosure_min (closure_mono subset_upperClosure) (upperClosure s).upper.closure

中文:
引理 closure_upperClosure_comm_pi
  条件: (hs : BddBelow s)
  证明: (closure_minimal (upperClosure_anti subset_closure) <|
      isClosed_closure.upperClosure_pi hs.closure).antisymm <|
    upperClosure_min (closure_mono subset_upperClosure) (upperClosure s).upper.closure

Depends on / 依赖: antisymm, closure, closure_minimal, closure_mono, hs.closure, isClosed_closure, isClosed_closure.upperClosure_pi, subset_closure, subset_upperClosure, upper.closure, upperClosure, upperClosure_anti, upperClosure_min, upperClosure_pi
-/
lemma closure_upperClosure_comm_pi (hs : BddBelow s) :
    closure (upperClosure s : Set (ι -> Real)) = upperClosure (closure s) :=
  (closure_minimal (upperClosure_anti subset_closure) <|
      isClosed_closure.upperClosure_pi hs.closure).antisymm <|
    upperClosure_min (closure_mono subset_upperClosure) (upperClosure s).upper.closure

/--
lemma `closure_lowerClosure_comm_pi` / 引理 `closure_lowerClosure_comm_pi`

English:
lemma closure_lowerClosure_comm_pi
  given: (hs : BddAbove s)
  proof: (closure_minimal (lowerClosure_mono subset_closure) <|
        isClosed_closure.lowerClosure_pi hs.closure).antisymm <|
    lowerClosure_min (closure_mono subset_lowerClosure) (lowerClosure s).lower.closure

中文:
引理 closure_lowerClosure_comm_pi
  条件: (hs : BddAbove s)
  证明: (closure_minimal (lowerClosure_mono subset_closure) <|
        isClosed_closure.lowerClosure_pi hs.closure).antisymm <|
    lowerClosure_min (closure_mono subset_lowerClosure) (lowerClosure s).lower.closure

Depends on / 依赖: antisymm, closure, closure_minimal, closure_mono, hs.closure, isClosed_closure, isClosed_closure.lowerClosure_pi, lower.closure, lowerClosure, lowerClosure_min, lowerClosure_mono, lowerClosure_pi, subset_closure, subset_lowerClosure
-/
lemma closure_lowerClosure_comm_pi (hs : BddAbove s) :
    closure (lowerClosure s : Set (ι -> Real)) = lowerClosure (closure s) :=
  (closure_minimal (lowerClosure_mono subset_closure) <|
        isClosed_closure.lowerClosure_pi hs.closure).antisymm <|
    lowerClosure_min (closure_mono subset_lowerClosure) (lowerClosure s).lower.closure

end Finite
