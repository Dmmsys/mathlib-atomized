/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.BoxIntegral.Integrability
public import Mathlib.Analysis.BoxIntegral.Partition.Measure
public import Mathlib.Analysis.BoxIntegral.Partition.Tagged

/-!
# Unit Partition

Fix `n` a positive integer. `BoxIntegral.unitPartition.box` are boxes in `ι → ℝ` obtained by
dividing the unit box uniformly into boxes of side length `1 / n` and translating the boxes by
vectors `ν : ι → ℤ`.

Let `B` be a `BoxIntegral`. A `unitPartition.box` is admissible for `B` (more precisely its index is
admissible) if it is contained in `B`. There are finitely many admissible `unitPartition.box` for
`B` and thus we can form the corresponding tagged prepartition, see
`BoxIntegral.unitPartition.prepartition` (note that each `unitPartition.box` comes with its
tag situated at its "upper most" vertex). If `B` satisfies `hasIntegralVertices`, that
is its vertices are in `ι → ℤ`, then the corresponding prepartition is actually a partition.

## Main definitions and results

* `BoxIntegral.hasIntegralVertices`: a `Prop` that states that the vertices of the box have
  coordinates in `ℤ`

* `BoxIntegral.unitPartition.box`: a `BoxIntegral`, indexed by `ν : ι → ℤ`, with vertices
  `ν i / n` and of side length `1 / n`.

* `BoxIntegral.unitPartition.admissibleIndex`: For `B : BoxIntegral.Box`, the set of indices of
  `unitPartition.box` that are subsets of `B`. This is a finite set.

* `BoxIntegral.unitPartition.prepartition_isPartition`: For `B : BoxIntegral.Box`, if `B`
  has integral vertices, then the prepartition of `unitPartition.box` admissible for `B` is a
  partition of `B`.

* `tendsto_tsum_div_pow_atTop_integral`: let `s` be a bounded, measurable set of `ι → ℝ`
  whose frontier has zero volume and let `F` be a continuous function. Then the limit as `n → ∞`
  of `∑ F x / n ^ card ι`, where the sum is over the points in `s ∩ n⁻¹ • (ι → ℤ)`, tends to the
  integral of `F` over `s`.

* `tendsto_card_div_pow_atTop_volume`: let `s` be a bounded, measurable set of `ι → ℝ` whose
  frontier has zero volume. Then the limit as `n → ∞` of `card (s ∩ n⁻¹ • (ι → ℤ)) / n ^ card ι`
  tends to the volume of `s`.

* `tendsto_card_div_pow_atTop_volume'`: a version of `tendsto_card_div_pow_atTop_volume` where we
  assume in addition that `x • s ⊆ y • s` whenever `0 < x ≤ y`. Then we get the same limit
  `card (s ∩ x⁻¹ • (ι → ℤ)) / x ^ card ι → volume s` but the limit is over a real variable `x`.

-/

@[expose] public section

noncomputable section

variable {ι : Type*}

open scoped Topology

section hasIntegralVertices

open Bornology

/--
Definition of `BoxIntegral.hasIntegralVertices` / `BoxIntegral.hasIntegralVertices` 的定义

English:
definition BoxIntegral.hasIntegralVertices
  signature: (B : Box ι)
  body: exists l u : ι -> Int, (forall i, B.lower i = l i) ∧ (forall i, B.upper i = u i)

中文:
定义 Box整数egral.has整数egralVertices
  签名: (B : Box ι)
  定义体: exists l u : ι -> Int, (forall i, B.lower i = l i) ∧ (forall i, B.upper i = u i)

Depends on / 依赖: B.lower, B.upper
-/
def BoxIntegral.hasIntegralVertices (B : Box ι) : Prop :=
  exists l u : ι -> Int, (forall i, B.lower i = l i) ∧ (forall i, B.upper i = u i)

/--
theorem `BoxIntegral.le_hasIntegralVertices_of_isBounded` / 定理 `BoxIntegral.le_hasIntegralVertices_of_isBounded`

English:
theorem BoxIntegral.le_hasIntegralVertices_of_isBounded
  statement: [Finite ι] {s : Set (ι -> Real)}
  proof: by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR₁, hR₂⟩ := IsBounded.subset_ball_lt h 0 0
  let C : Nat := ⌈R⌉₊
  have hC := Nat.ceil_pos.mpr hR₁
  let I : Box ι := Box.mk (fun _ => -C) (fun _ => C)
    (fun _ => by simp [C, neg_lt_self_iff, Nat.cast_pos, hC])
  refine ⟨I, ⟨fun _ => - C, fun _ => C, 

中文:
定理 Box整数egral.le_has整数egralVertices_of_isBounded
  结论: [有限 ι] {s : 集合 (ι -> 实数)}
  证明: by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR₁, hR₂⟩ := IsBounded.subset_ball_lt h 0 0
  let C : Nat := ⌈R⌉₊
  have hC := Nat.ceil_pos.mpr hR₁
  let I : Box ι := Box.mk (fun _ => -C) (fun _ => C)
    (fun _ => by simp [C, neg_lt_self_iff, Nat.cast_pos, hC])
  refine ⟨I, ⟨fun _ => - C, fun _ => C, 

Depends on / 依赖: Box.mk, Fintype, Fintype.ofFinite, Int.cast_neg_natCast, IsBounded, IsBounded.subset_ball_lt, Metric, Metric.ball, Metric.ball_subset_ball, Nat.cast_pos, Nat.ceil_pos.mpr, Nat.le_ceil, ball_subset_ball, cast_neg_natCast, cast_pos, ceil_pos, le_ceil, le_trans, mem_ball_zero_if, neg_lt_self_iff
-/
theorem BoxIntegral.le_hasIntegralVertices_of_isBounded [Finite ι] {s : Set (ι -> Real)}
    (h : IsBounded s) :
    exists B : BoxIntegral.Box ι, hasIntegralVertices B ∧ s <= B := by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR₁, hR₂⟩ := IsBounded.subset_ball_lt h 0 0
  let C : Nat := ⌈R⌉₊
  have hC := Nat.ceil_pos.mpr hR₁
  let I : Box ι := Box.mk (fun _ => -C) (fun _ => C)
    (fun _ => by simp [C, neg_lt_self_iff, Nat.cast_pos, hC])
  refine ⟨I, ⟨fun _ => - C, fun _ => C, fun i => (Int.cast_neg_natCast C).symm, fun _ => rfl⟩,
    le_trans hR₂ ?_⟩
  suffices Metric.ball (0 : ι -> Real) C <= I from
    le_trans (Metric.ball_subset_ball (Nat.le_ceil R)) this
  intro x hx
  simp_rw [C, mem_ball_zero_iff, pi_norm_lt_iff (Nat.cast_pos.mpr hC),
    Real.norm_eq_abs, abs_lt] at hx
  exact fun i => ⟨(hx i).1, le_of_lt (hx i).2⟩

end hasIntegralVertices

namespace BoxIntegral.unitPartition

open Bornology MeasureTheory Fintype BoxIntegral

variable (n : Nat)

/--
Definition of `box` / `box` 的定义

English:
definition box
  signature: [NeZero n] (ν : ι -> Int)
  body: fun i => ν i / n
  upper := fun i => (ν i + 1) / n
  lower_lt_upper := fun _ => by simp [add_div, n.pos_of_neZero]

@[simp]

中文:
定义 box
  签名: [NeZero n] (ν : ι -> 整数)
  定义体: fun i => ν i / n
  upper := fun i => (ν i + 1) / n
  lower_lt_upper := fun _ => by simp [add_div, n.pos_of_neZero]

@[simp]
-/
def box [NeZero n] (ν : ι -> Int) : Box ι where
  lower := fun i => ν i / n
  upper := fun i => (ν i + 1) / n
  lower_lt_upper := fun _ => by simp [add_div, n.pos_of_neZero]

@[simp]
/--
theorem `box_lower` / 定理 `box_lower`

English:
theorem box_lower
  given: [NeZero n] (ν : ι -> Int)
  proof: rfl

@[simp]

中文:
定理 box_lower
  条件: [NeZero n] (ν : ι -> 整数)
  证明: rfl

@[simp]
-/
theorem box_lower [NeZero n] (ν : ι -> Int) :
    (box n ν).lower = fun i => (ν i / n : Real) := rfl

@[simp]
/--
theorem `box_upper` / 定理 `box_upper`

English:
theorem box_upper
  given: [NeZero n] (ν : ι -> Int)
  proof: rfl

中文:
定理 box_upper
  条件: [NeZero n] (ν : ι -> 整数)
  证明: rfl
-/
theorem box_upper [NeZero n] (ν : ι -> Int) :
    (box n ν).upper = fun i => ((ν i + 1) / n : Real) := rfl

variable {n} in
@[simp]
/--
theorem `mem_box_iff` / 定理 `mem_box_iff`

English:
theorem mem_box_iff
  given: [NeZero n] {ν : ι -> Int} {x : ι -> Real}
  proof: by
  simp_rw [Box.mem_def, box, Set.mem_Ioc]

中文:
定理 mem_box_iff
  条件: [NeZero n] {ν : ι -> 整数} {x : ι -> 实数}
  证明: by
  simp_rw [Box.mem_def, box, Set.mem_Ioc]

Depends on / 依赖: Box.mem_def, Set.mem_Ioc, mem_Ioc, mem_def, simp_rw
-/
theorem mem_box_iff [NeZero n] {ν : ι -> Int} {x : ι -> Real} :
    x in box n ν ↔ forall i, ν i / n < x i ∧ x i <= (ν i + 1) / n := by
  simp_rw [Box.mem_def, box, Set.mem_Ioc]

variable {n} in
/--
theorem `mem_box_iff'` / 定理 `mem_box_iff'`

English:
theorem mem_box_iff'
  given: [NeZero n] {ν : ι -> Int} {x : ι -> Real}
  proof: by
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  simp_rw [mem_box_iff, ← _root_.le_div_iff₀' h, ← div_lt_iff₀' h]

中文:
定理 mem_box_iff'
  条件: [NeZero n] {ν : ι -> 整数} {x : ι -> 实数}
  证明: by
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  simp_rw [mem_box_iff, ← _root_.le_div_iff₀' h, ← div_lt_iff₀' h]

Depends on / 依赖: Nat.cast_pos.mpr, _root_, _root_.le_div_iff, cast_pos, mem_box_iff, n.pos_of_neZero, pos_of_neZero, simp_rw
-/
theorem mem_box_iff' [NeZero n] {ν : ι -> Int} {x : ι -> Real} :
    x in box n ν ↔ forall i, ν i < n * x i ∧ n * x i <= ν i + 1 := by
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  simp_rw [mem_box_iff, ← _root_.le_div_iff₀' h, ← div_lt_iff₀' h]

/--
Definition of `tag` / `tag` 的定义

English:
abbreviation tag
  signature: (ν : ι -> Int)
  body: fun i => (ν i + 1) / n

@[simp]

中文:
缩写 tag
  签名: (ν : ι -> 整数)
  定义体: fun i => (ν i + 1) / n

@[simp]
-/
abbrev tag (ν : ι -> Int) : ι -> Real := fun i => (ν i + 1) / n

@[simp]
/--
theorem `tag_apply` / 定理 `tag_apply`

English:
theorem tag_apply
  given: (ν : ι -> Int) (i : ι)
  statement: tag n ν i = (ν i + 1) / n
  proof: rfl

中文:
定理 tag_apply
  条件: (ν : ι -> 整数) (i : ι)
  结论: tag n ν i = (ν i + 1) / n
  证明: rfl
-/
theorem tag_apply (ν : ι -> Int) (i : ι) : tag n ν i = (ν i + 1) / n := rfl

variable [NeZero n]

/--
theorem `tag_injective` / 定理 `tag_injective`

English:
theorem tag_injective
  statement: Function.Injective (fun ν : ι -> Int => tag n ν)
  proof: by
  refine fun _ _ h => funext_iff.mpr fun i => ?_
  have := congr_arg (fun x => x i) h
  simp_rw [tag_apply, div_left_inj' (c := (n : Real)) (Nat.cast_ne_zero.mpr (NeZero.ne n)),
    add_left_inj, Int.cast_inj] at this
  exact this

中文:
定理 tag_injective
  结论: 函数.单射 (fun ν : ι -> 整数 => tag n ν)
  证明: by
  refine fun _ _ h => funext_iff.mpr fun i => ?_
  have := congr_arg (fun x => x i) h
  simp_rw [tag_apply, div_left_inj' (c := (n : Real)) (Nat.cast_ne_zero.mpr (NeZero.ne n)),
    add_left_inj, Int.cast_inj] at this
  exact this

Depends on / 依赖: Int.cast_inj, Nat.cast_ne_zero.mpr, NeZero, NeZero.ne, add_left_inj, cast_inj, cast_ne_zero, congr_arg, div_left_inj, funext_iff, funext_iff.mpr, simp_rw, tag_apply
-/
theorem tag_injective : Function.Injective (fun ν : ι -> Int => tag n ν) := by
  refine fun _ _ h => funext_iff.mpr fun i => ?_
  have := congr_arg (fun x => x i) h
  simp_rw [tag_apply, div_left_inj' (c := (n : Real)) (Nat.cast_ne_zero.mpr (NeZero.ne n)),
    add_left_inj, Int.cast_inj] at this
  exact this

/--
theorem `tag_mem` / 定理 `tag_mem`

English:
theorem tag_mem
  given: (ν : ι -> Int)
  proof: by
  refine mem_box_iff.mpr fun _ => ?_
  rw [tag]; rw [add_div]
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  exact ⟨lt_add_of_pos_right _ (by positivity), le_rfl⟩

中文:
定理 tag_mem
  条件: (ν : ι -> 整数)
  证明: by
  refine mem_box_iff.mpr fun _ => ?_
  rw [tag]; rw [add_div]
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  exact ⟨lt_add_of_pos_right _ (by positivity), le_rfl⟩

Depends on / 依赖: Nat.cast_pos.mpr, add_div, cast_pos, le_rfl, lt_add_of_pos_right, mem_box_iff, mem_box_iff.mpr, n.pos_of_neZero, pos_of_neZero
-/
theorem tag_mem (ν : ι -> Int) :
    tag n ν in box n ν := by
  refine mem_box_iff.mpr fun _ => ?_
  rw [tag]; rw [add_div]
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  exact ⟨lt_add_of_pos_right _ (by positivity), le_rfl⟩

/--
Definition of `index` / `index` 的定义

English:
definition index
  signature: (x : ι -> Real) (i : ι)
  body: ⌈n * x i⌉ - 1

@[simp]

中文:
定义 index
  签名: (x : ι -> 实数) (i : ι)
  定义体: ⌈n * x i⌉ - 1

@[simp]
-/
def index (x : ι -> Real) (i : ι) : Int := ⌈n * x i⌉ - 1

@[simp]
/--
theorem `index_apply` / 定理 `index_apply`

English:
theorem index_apply
  given: (m : Nat) {x : ι -> Real} (i : ι)
  proof: rfl

中文:
定理 index_apply
  条件: (m : 自然数) {x : ι -> 实数} (i : ι)
  证明: rfl
-/
theorem index_apply (m : Nat) {x : ι -> Real} (i : ι) :
    index m x i = ⌈m * x i⌉ - 1 := rfl

variable {n} in
/--
theorem `mem_box_iff_index` / 定理 `mem_box_iff_index`

English:
theorem mem_box_iff_index
  given: {x : ι -> Real} {ν : ι -> Int}
  proof: by
  simp_rw [mem_box_iff', funext_iff, index_apply, sub_eq_iff_eq_add, Int.ceil_eq_iff,
    Int.cast_add, Int.cast_one, add_sub_cancel_right]

@[simp]

中文:
定理 mem_box_iff_index
  条件: {x : ι -> 实数} {ν : ι -> 整数}
  证明: by
  simp_rw [mem_box_iff', funext_iff, index_apply, sub_eq_iff_eq_add, Int.ceil_eq_iff,
    Int.cast_add, Int.cast_one, add_sub_cancel_right]

@[simp]

Depends on / 依赖: Int.cast_add, Int.cast_one, Int.ceil_eq_iff, add_sub_cancel_right, cast_add, cast_one, ceil_eq_iff, funext_iff, index_apply, mem_box_iff, simp_rw, sub_eq_iff_eq_add
-/
theorem mem_box_iff_index {x : ι -> Real} {ν : ι -> Int} :
    x in box n ν ↔ index n x = ν := by
  simp_rw [mem_box_iff', funext_iff, index_apply, sub_eq_iff_eq_add, Int.ceil_eq_iff,
    Int.cast_add, Int.cast_one, add_sub_cancel_right]

@[simp]
/--
theorem `index_tag` / 定理 `index_tag`

English:
theorem index_tag
  given: (ν : ι -> Int)
  proof: mem_box_iff_index.mp (tag_mem n ν)

中文:
定理 index_tag
  条件: (ν : ι -> 整数)
  证明: mem_box_iff_index.mp (tag_mem n ν)

Depends on / 依赖: mem_box_iff_index, mem_box_iff_index.mp, tag_mem
-/
theorem index_tag (ν : ι -> Int) :
    index n (tag n ν) = ν := mem_box_iff_index.mp (tag_mem n ν)

variable {n} in
/--
theorem `disjoint` / 定理 `disjoint`

English:
theorem disjoint
  given: {ν ν' : ι -> Int}
  proof: by
  rw [not_iff_comm]; rw [Set.not_disjoint_iff]
  refine ⟨fun ⟨x, hx, hx'⟩ => ?_, fun h => ⟨tag n ν, tag_mem n ν, h ▸ tag_mem n ν⟩⟩
  rw [← mem_box_iff_index.mp hx]; rw [← mem_box_iff_index.mp hx']

中文:
定理 disjoint
  条件: {ν ν' : ι -> 整数}
  证明: by
  rw [not_iff_comm]; rw [Set.not_disjoint_iff]
  refine ⟨fun ⟨x, hx, hx'⟩ => ?_, fun h => ⟨tag n ν, tag_mem n ν, h ▸ tag_mem n ν⟩⟩
  rw [← mem_box_iff_index.mp hx]; rw [← mem_box_iff_index.mp hx']

Depends on / 依赖: Set.not_disjoint_iff, mem_box_iff_index, mem_box_iff_index.mp, not_disjoint_iff, not_iff_comm, tag_mem
-/
theorem disjoint {ν ν' : ι -> Int} :
    ν != ν' ↔ Disjoint (box n ν).toSet (box n ν').toSet := by
  rw [not_iff_comm]; rw [Set.not_disjoint_iff]
  refine ⟨fun ⟨x, hx, hx'⟩ => ?_, fun h => ⟨tag n ν, tag_mem n ν, h ▸ tag_mem n ν⟩⟩
  rw [← mem_box_iff_index.mp hx]; rw [← mem_box_iff_index.mp hx']

/--
theorem `box_injective` / 定理 `box_injective`

English:
theorem box_injective
  statement: Function.Injective (fun ν : ι -> Int => box n ν)
  proof: by
  intro _ _ h
  contrapose! h
  exact Box.ne_of_disjoint_coe (disjoint.mp h)

中文:
定理 box_injective
  结论: 函数.单射 (fun ν : ι -> 整数 => box n ν)
  证明: by
  intro _ _ h
  contrapose! h
  exact Box.ne_of_disjoint_coe (disjoint.mp h)

Depends on / 依赖: Box.ne_of_disjoint_coe, algebraMap_smul, contrapose, disjoint, disjoint.mp, ne_of_disjoint_coe, norm_algebraMap, norm_mul, norm_real, real_smul
-/
theorem box_injective : Function.Injective (fun ν : ι -> Int => box n ν) := by
  intro _ _ h
  contrapose! h
  exact Box.ne_of_disjoint_coe (disjoint.mp h)

/--
lemma `box.upper_sub_lower` / 引理 `box.upper_sub_lower`

English:
lemma box.upper_sub_lower
  given: (ν : ι -> Int) (i : ι)
  proof: by
  simp_rw [box, add_div, add_sub_cancel_left]

中文:
引理 box.upper_sub_lower
  条件: (ν : ι -> 整数) (i : ι)
  证明: by
  simp_rw [box, add_div, add_sub_cancel_left]

Depends on / 依赖: NormedSpace, _root_, _root_.NormedSpace.complexToReal, add_div, add_sub_cancel_left, complexToReal, simp_rw
-/
lemma box.upper_sub_lower (ν : ι -> Int) (i : ι) :
    (box n ν).upper i - (box n ν).lower i = 1 / n := by
  simp_rw [box, add_div, add_sub_cancel_left]

section fintype

variable [Fintype ι]

/--
theorem `diam_boxIcc` / 定理 `diam_boxIcc`

English:
theorem diam_boxIcc
  given: (ν : ι -> Int)
  proof: by
  rw [BoxIntegral.Box.Icc_eq_pi]
refine ENNReal.toReal_le_of_le_ofReal (by positivity) Metric.ediam_pi_le_of_le fun i => ?_
  simp_rw [Real.ediam_Icc, box.upper_sub_lower, le_rfl]

@[simp]

中文:
定理 diam_boxIcc
  条件: (ν : ι -> 整数)
  证明: by
  rw [BoxIntegral.Box.Icc_eq_pi]
refine ENNReal.toReal_le_of_le_ofReal (by positivity) Metric.ediam_pi_le_of_le fun i => ?_
  simp_rw [Real.ediam_Icc, box.upper_sub_lower, le_rfl]

@[simp]

Depends on / 依赖: BoxIntegral, BoxIntegral.Box.Icc_eq_pi, ENNReal, ENNReal.toReal_le_of_le_ofReal, Icc_eq_pi, Metric, Metric.ediam_pi_le_of_le, NormedAlgebra, Real.ediam_Icc, SeminormedRing, _root_, _root_.NormedAlgebra.complexToReal, box.upper_sub_lower, complexToReal, ediam_Icc, ediam_pi_le_of_le, le_rfl, simp_rw, toReal_le_of_le_ofReal, upper_sub_lower
-/
theorem diam_boxIcc (ν : ι -> Int) :
    Metric.diam (Box.Icc (box n ν)) <= 1 / n := by
  rw [BoxIntegral.Box.Icc_eq_pi]
refine ENNReal.toReal_le_of_le_ofReal (by positivity) Metric.ediam_pi_le_of_le fun i => ?_
  simp_rw [Real.ediam_Icc, box.upper_sub_lower, le_rfl]

@[simp]
/--
theorem `volume_box` / 定理 `volume_box`

English:
theorem volume_box
  given: (ν : ι -> Int)
  proof: by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc,
    box.upper_sub_lower, Finset.prod_const, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr
    n.pos_of_neZero), ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div, ENNReal.inv_pow,
    Finset.card_univ]

中文:
定理 volume_box
  条件: (ν : ι -> 整数)
  证明: by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc,
    box.upper_sub_lower, Finset.prod_const, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr
    n.pos_of_neZero), ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div, ENNReal.inv_pow,
    Finset.card_univ]

Depends on / 依赖: BoxIntegral, BoxIntegral.Box.coe_eq_pi, ENNReal, ENNReal.inv_pow, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_natCast, ENNReal.ofReal_one, Finset, Finset.card_univ, Finset.prod_const, Measure, Measure.pi_pi, Nat.cast_pos.mpr, Real.volume_Ioc, box.upper_sub_lower, card_univ, cast_pos, coe_eq_pi, inv_pow, n.pos_of_neZero
-/
theorem volume_box (ν : ι -> Int) :
    volume (box n ν : Set (ι -> Real)) = 1 / n ^ card ι := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc,
    box.upper_sub_lower, Finset.prod_const, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr
    n.pos_of_neZero), ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div, ENNReal.inv_pow,
    Finset.card_univ]

/--
theorem `setFinite_index` / 定理 `setFinite_index`

English:
theorem setFinite_index
  given: {s : Set (ι -> Real)} (hs₁ : NullMeasurableSet s) (hs₂ : volume s != ⊤)
  proof: by
  refine (Measure.finite_const_le_meas_of_disjoint_iUnion₀ volume (ε := 1 / n ^ card ι)
    (by simp) (As := fun ν : ι -> Int => (box n ν) inter s) (fun ν => ?_) (fun _ _ h => ?_) ?_).subset
      (fun _ hν => ?_)
  · refine NullMeasurableSet.inter ?_ hs₁
    exact (box n ν).measurableSet_coe.nul

中文:
定理 setFinite_index
  条件: {s : 集合 (ι -> 实数)} (hs₁ : NullMeasurableSet s) (hs₂ : volume s != ⊤)
  证明: by
  refine (Measure.finite_const_le_meas_of_disjoint_iUnion₀ volume (ε := 1 / n ^ card ι)
    (by simp) (As := fun ν : ι -> Int => (box n ν) inter s) (fun ν => ?_) (fun _ _ h => ?_) ?_).subset
      (fun _ hν => ?_)
  · refine NullMeasurableSet.inter ?_ hs₁
    exact (box n ν).measurableSet_coe.nul

Depends on / 依赖: Disjoint, Disjoint.inter_right, Measure, Measure.finite_const_le_meas_of_disjoint_iUnion, NullMeasurableSet, NullMeasurableSet.inter, Set.iUnion_subset_iff, Set.inter_subset_right, aedisjoint, disjoint, disjoint.mp, iUnion_subset_iff, implies_true, inter_left, inter_right, inter_subset_right, lt_top_iff_ne_top, lt_top_iff_ne_top.mp, measurableSet_coe, measurableSet_coe.nullMeasurableSet
-/
theorem setFinite_index {s : Set (ι -> Real)} (hs₁ : NullMeasurableSet s) (hs₂ : volume s != ⊤) :
    Set.Finite {ν : ι -> Int | ↑(box n ν) subseteq s} := by
  refine (Measure.finite_const_le_meas_of_disjoint_iUnion₀ volume (ε := 1 / n ^ card ι)
    (by simp) (As := fun ν : ι -> Int => (box n ν) inter s) (fun ν => ?_) (fun _ _ h => ?_) ?_).subset
      (fun _ hν => ?_)
  · refine NullMeasurableSet.inter ?_ hs₁
    exact (box n ν).measurableSet_coe.nullMeasurableSet
  · exact ((Disjoint.inter_right _ (disjoint.mp h)).inter_left _).aedisjoint
· exact lt_top_iff_ne_top.mp measure_lt_top_of_subset
      (by simp only [Set.iUnion_subset_iff, Set.inter_subset_right, implies_true]) hs₂
  · rw [Set.mem_ofPred, Set.inter_eq_self_of_subset_left hν, volume_box]

/--
Definition of `admissibleIndex` / `admissibleIndex` 的定义

English:
definition admissibleIndex
  signature: (B : Box ι)
  body: by
  refine (setFinite_index n B.measurableSet_coe.nullMeasurableSet ?_).toFinset
  exact lt_top_iff_ne_top.mp (IsBounded.measure_lt_top B.isBounded)

中文:
定义 admissibleIndex
  签名: (B : Box ι)
  定义体: by
  refine (setFinite_index n B.measurableSet_coe.nullMeasurableSet ?_).toFinset
  exact lt_top_iff_ne_top.mp (IsBounded.measure_lt_top B.isBounded)

Depends on / 依赖: B.isBounded, B.measurableSet_coe.nullMeasurableSet, IsBounded, IsBounded.measure_lt_top, isBounded, lt_top_iff_ne_top, lt_top_iff_ne_top.mp, measurableSet_coe, measure_lt_top, nullMeasurableSet, setFinite_index, toFinset
-/
def admissibleIndex (B : Box ι) : Finset (ι -> Int) := by
  refine (setFinite_index n B.measurableSet_coe.nullMeasurableSet ?_).toFinset
  exact lt_top_iff_ne_top.mp (IsBounded.measure_lt_top B.isBounded)

variable {n} in
/--
theorem `mem_admissibleIndex_iff` / 定理 `mem_admissibleIndex_iff`

English:
theorem mem_admissibleIndex_iff
  given: {B : Box ι} {ν : ι -> Int}
  proof: by
  rw [admissibleIndex]; rw [Set.Finite.mem_toFinset]; rw [Set.mem_ofPred_eq]; rw [Box.coe_subset_coe]

中文:
定理 mem_admissibleIndex_iff
  条件: {B : Box ι} {ν : ι -> 整数}
  证明: by
  rw [admissibleIndex]; rw [Set.Finite.mem_toFinset]; rw [Set.mem_ofPred_eq]; rw [Box.coe_subset_coe]

Depends on / 依赖: Box.coe_subset_coe, Finite, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, admissibleIndex, coe_subset_coe, mem_ofPred_eq, mem_toFinset
-/
theorem mem_admissibleIndex_iff {B : Box ι} {ν : ι -> Int} :
    ν in admissibleIndex n B ↔ box n ν <= B := by
  rw [admissibleIndex]; rw [Set.Finite.mem_toFinset]; rw [Set.mem_ofPred_eq]; rw [Box.coe_subset_coe]

open scoped Classical in
/--
Definition of `prepartition` / `prepartition` 的定义

English:
definition prepartition
  signature: (B : Box ι)
  body: Finset.image (fun ν => box n ν) (admissibleIndex n B)
  le_of_mem' _ hI := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hI
    exact mem_admissibleIndex_iff.mp hν
  pairwiseDisjoint _ hI₁ _ hI₂ h := by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hI₁
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.

中文:
定义 prepartition
  签名: (B : Box ι)
  定义体: Finset.image (fun ν => box n ν) (admissibleIndex n B)
  le_of_mem' _ hI := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hI
    exact mem_admissibleIndex_iff.mp hν
  pairwiseDisjoint _ hI₁ _ hI₂ h := by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hI₁
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.

Depends on / 依赖: Finset, Finset.image, admissibleIndex
-/
def prepartition (B : Box ι) : TaggedPrepartition B where
  boxes := Finset.image (fun ν => box n ν) (admissibleIndex n B)
  le_of_mem' _ hI := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hI
    exact mem_admissibleIndex_iff.mp hν
  pairwiseDisjoint _ hI₁ _ hI₂ h := by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hI₁
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hI₂
    exact disjoint.mp fun x => h (congrArg (box n) x)
  tag I :=
    if hI : exists ν in admissibleIndex n B, I = box n ν then tag n hI.choose else B.exists_mem.choose
  tag_mem_Icc I := by
    by_cases hI : exists ν in admissibleIndex n B, I = box n ν
    · simp_rw [dif_pos hI]
exact Box.coe_subset_Icc (mem_admissibleIndex_iff.mp hI.choose_spec.1) (tag_mem n _)
    · simp_rw [dif_neg hI]
      exact Box.coe_subset_Icc B.exists_mem.choose_spec

set_option backward.isDefEq.respectTransparency.types false in
variable {n} in
@[simp]
/--
theorem `mem_prepartition_iff` / 定理 `mem_prepartition_iff`

English:
theorem mem_prepartition_iff
  given: {B I : Box ι}
  proof: by
  classical
  rw [prepartition]; rw [TaggedPrepartition.mem_mk]; rw [Prepartition.mem_mk]; rw [Finset.mem_image]

中文:
定理 mem_prepartition_iff
  条件: {B I : Box ι}
  证明: by
  classical
  rw [prepartition]; rw [TaggedPrepartition.mem_mk]; rw [Prepartition.mem_mk]; rw [Finset.mem_image]

Depends on / 依赖: Finset, Finset.mem_image, Prepartition, Prepartition.mem_mk, TaggedPrepartition, TaggedPrepartition.mem_mk, classical, mem_image, mem_mk, prepartition
-/
theorem mem_prepartition_iff {B I : Box ι} :
    I in prepartition n B ↔ exists ν in admissibleIndex n B, box n ν = I := by
  classical
  rw [prepartition]; rw [TaggedPrepartition.mem_mk]; rw [Prepartition.mem_mk]; rw [Finset.mem_image]

variable {n} in
/--
theorem `mem_prepartition_boxes_iff` / 定理 `mem_prepartition_boxes_iff`

English:
theorem mem_prepartition_boxes_iff
  given: {B I : Box ι}
  proof: mem_prepartition_iff

中文:
定理 mem_prepartition_boxes_iff
  条件: {B I : Box ι}
  证明: mem_prepartition_iff

Depends on / 依赖: mem_prepartition_iff
-/
theorem mem_prepartition_boxes_iff {B I : Box ι} :
    I in (prepartition n B).boxes ↔ exists ν in admissibleIndex n B, box n ν = I :=
  mem_prepartition_iff

/--
theorem `prepartition_tag` / 定理 `prepartition_tag`

English:
theorem prepartition_tag
  given: {ν : ι -> Int} {B : Box ι} (hν : ν in admissibleIndex n B)
  proof: by
  dsimp only [prepartition]
  have h : exists ν' in admissibleIndex n B, box n ν = box n ν' := ⟨ν, hν, rfl⟩
  rw [dif_pos h]; rw [(tag_injective n).eq_iff]; rw [← (box_injective n).eq_iff]
  exact h.choose_spec.2.symm

中文:
定理 prepartition_tag
  条件: {ν : ι -> 整数} {B : Box ι} (hν : ν in admissibleIndex n B)
  证明: by
  dsimp only [prepartition]
  have h : exists ν' in admissibleIndex n B, box n ν = box n ν' := ⟨ν, hν, rfl⟩
  rw [dif_pos h]; rw [(tag_injective n).eq_iff]; rw [← (box_injective n).eq_iff]
  exact h.choose_spec.2.symm

Depends on / 依赖: admissibleIndex, box_injective, choose_spec, dif_pos, eq_iff, h.choose_spec, prepartition, tag_injective
-/
theorem prepartition_tag {ν : ι -> Int} {B : Box ι} (hν : ν in admissibleIndex n B) :
    (prepartition n B).tag (box n ν) = tag n ν := by
  dsimp only [prepartition]
  have h : exists ν' in admissibleIndex n B, box n ν = box n ν' := ⟨ν, hν, rfl⟩
  rw [dif_pos h]; rw [(tag_injective n).eq_iff]; rw [← (box_injective n).eq_iff]
  exact h.choose_spec.2.symm

/--
theorem `box_index_tag_eq_self` / 定理 `box_index_tag_eq_self`

English:
theorem box_index_tag_eq_self
  given: {B I : Box ι} (hI : I in (prepartition n B).boxes)
  proof: by
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_boxes_iff.mp hI
  rw [prepartition_tag n hν]; rw [index_tag]

中文:
定理 box_index_tag_eq_self
  条件: {B I : Box ι} (hI : I in (prepartition n B).boxes)
  证明: by
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_boxes_iff.mp hI
  rw [prepartition_tag n hν]; rw [index_tag]

Depends on / 依赖: index_tag, mem_prepartition_boxes_iff, mem_prepartition_boxes_iff.mp, prepartition_tag
-/
theorem box_index_tag_eq_self {B I : Box ι} (hI : I in (prepartition n B).boxes) :
    box n (index n ((prepartition n B).tag I)) = I := by
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_boxes_iff.mp hI
  rw [prepartition_tag n hν]; rw [index_tag]

/--
theorem `prepartition_isHenstock` / 定理 `prepartition_isHenstock`

English:
theorem prepartition_isHenstock
  given: (B : Box ι)
  proof: by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  rw [prepartition_tag n hν]
  exact Box.coe_subset_Icc (tag_mem _ _)

中文:
定理 prepartition_isHenstock
  条件: (B : Box ι)
  证明: by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  rw [prepartition_tag n hν]
  exact Box.coe_subset_Icc (tag_mem _ _)

Depends on / 依赖: Box.coe_subset_Icc, coe_subset_Icc, mem_prepartition_iff, mem_prepartition_iff.mp, prepartition_tag, tag_mem
-/
theorem prepartition_isHenstock (B : Box ι) :
    (prepartition n B).IsHenstock := by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  rw [prepartition_tag n hν]
  exact Box.coe_subset_Icc (tag_mem _ _)

/--
theorem `prepartition_isSubordinate` / 定理 `prepartition_isSubordinate`

English:
theorem prepartition_isSubordinate
  given: (B : Box ι) {r : Real} (hr : 0 < r) (hn : 1 / n <= r)
  proof: by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  refine fun _ h => le_trans (Metric.dist_le_diam_of_mem (Box.isBounded_Icc _) h ?_) ?_
  · rw [prepartition_tag n hν]
    exact Box.coe_subset_Icc (tag_mem _ _)
  · exact le_trans (diam_boxIcc n ν) hn

中文:
定理 prepartition_isSubordinate
  条件: (B : Box ι) {r : 实数} (hr : 0 < r) (hn : 1 / n <= r)
  证明: by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  refine fun _ h => le_trans (Metric.dist_le_diam_of_mem (Box.isBounded_Icc _) h ?_) ?_
  · rw [prepartition_tag n hν]
    exact Box.coe_subset_Icc (tag_mem _ _)
  · exact le_trans (diam_boxIcc n ν) hn

Depends on / 依赖: Box.coe_subset_Icc, Box.isBounded_Icc, Metric, Metric.dist_le_diam_of_mem, coe_subset_Icc, diam_boxIcc, dist_le_diam_of_mem, isBounded_Icc, le_trans, mem_prepartition_iff, mem_prepartition_iff.mp, prepartition_tag, tag_mem
-/
theorem prepartition_isSubordinate (B : Box ι) {r : Real} (hr : 0 < r) (hn : 1 / n <= r) :
    (prepartition n B).IsSubordinate (fun _ => ⟨r, hr⟩) := by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  refine fun _ h => le_trans (Metric.dist_le_diam_of_mem (Box.isBounded_Icc _) h ?_) ?_
  · rw [prepartition_tag n hν]
    exact Box.coe_subset_Icc (tag_mem _ _)
  · exact le_trans (diam_boxIcc n ν) hn

/--
theorem `mem_admissibleIndex_of_mem_box_aux₁` / 定理 `mem_admissibleIndex_of_mem_box_aux₁`

English:
theorem mem_admissibleIndex_of_mem_box_aux₁
  given: (x : Real) (a : Int)
  proof: by
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  rw [le_div_iff₀' h]; rw [le_sub_iff_add_le]; rw [show (n : Real) * a + 1 = (n * a + 1 : Int) by norm_cast]; rw [Int.cast_le]; rw [Int.add_one_le_iff]; rw [Int.lt_ceil]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [mul_lt_mul_iff_right

中文:
定理 mem_admissibleIndex_of_mem_box_aux₁
  条件: (x : 实数) (a : 整数)
  证明: by
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  rw [le_div_iff₀' h]; rw [le_sub_iff_add_le]; rw [show (n : Real) * a + 1 = (n * a + 1 : Int) by norm_cast]; rw [Int.cast_le]; rw [Int.add_one_le_iff]; rw [Int.lt_ceil]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [mul_lt_mul_iff_right
-/
private theorem mem_admissibleIndex_of_mem_box_aux₁ (x : Real) (a : Int) :
    a < x ↔ a <= (⌈n * x⌉ - 1) / (n : Real) := by
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  rw [le_div_iff₀' h]; rw [le_sub_iff_add_le]; rw [show (n : Real) * a + 1 = (n * a + 1 : Int) by norm_cast]; rw [Int.cast_le]; rw [Int.add_one_le_iff]; rw [Int.lt_ceil]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [mul_lt_mul_iff_right₀ h]

/--
theorem `mem_admissibleIndex_of_mem_box_aux₂` / 定理 `mem_admissibleIndex_of_mem_box_aux₂`

English:
theorem mem_admissibleIndex_of_mem_box_aux₂
  given: (x : Real) (a : Int)
  proof: by
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  rw [sub_add_cancel]; rw [div_le_iff₀' h]; rw [show (n : Real) * a = (n * a : Int) by norm_cast]; rw [Int.cast_le]; rw [Int.ceil_le]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [mul_le_mul_iff_right₀ h]

中文:
定理 mem_admissibleIndex_of_mem_box_aux₂
  条件: (x : 实数) (a : 整数)
  证明: by
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  rw [sub_add_cancel]; rw [div_le_iff₀' h]; rw [show (n : Real) * a = (n * a : Int) by norm_cast]; rw [Int.cast_le]; rw [Int.ceil_le]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [mul_le_mul_iff_right₀ h]
-/
private theorem mem_admissibleIndex_of_mem_box_aux₂ (x : Real) (a : Int) :
    x <= a ↔ (⌈n * x⌉ - 1 + 1) / (n : Real) <= a := by
have h : 0 < (n : Real) := Nat.cast_pos.mpr n.pos_of_neZero
  rw [sub_add_cancel]; rw [div_le_iff₀' h]; rw [show (n : Real) * a = (n * a : Int) by norm_cast]; rw [Int.cast_le]; rw [Int.ceil_le]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [mul_le_mul_iff_right₀ h]

/--
theorem `mem_admissibleIndex_of_mem_box` / 定理 `mem_admissibleIndex_of_mem_box`

English:
theorem mem_admissibleIndex_of_mem_box
  statement: {B : Box ι} (hB : hasIntegralVertices B) {x : ι -> Real}
  proof: by
  obtain ⟨l, u, hl, hu⟩ := hB
  simp_rw [mem_admissibleIndex_iff, Box.le_iff_bounds, box_lower, box_upper, Pi.le_def,
    index_apply, hl, hu, ← forall_and]
  push_cast
  refine fun i => ⟨?_, ?_⟩
  · exact (mem_admissibleIndex_of_mem_box_aux₁ n (x i) (l i)).mp ((hl i) ▸ (hx i).1)
  · exact (mem_a

中文:
定理 mem_admissibleIndex_of_mem_box
  结论: {B : Box ι} (hB : has整数egralVertices B) {x : ι -> 实数}
  证明: by
  obtain ⟨l, u, hl, hu⟩ := hB
  simp_rw [mem_admissibleIndex_iff, Box.le_iff_bounds, box_lower, box_upper, Pi.le_def,
    index_apply, hl, hu, ← forall_and]
  push_cast
  refine fun i => ⟨?_, ?_⟩
  · exact (mem_admissibleIndex_of_mem_box_aux₁ n (x i) (l i)).mp ((hl i) ▸ (hx i).1)
  · exact (mem_a

Depends on / 依赖: Box.le_iff_bounds, Pi.le_def, box_lower, box_upper, forall_and, index_apply, le_def, le_iff_bounds, mem_admissibleIndex_iff, simp_rw
-/
theorem mem_admissibleIndex_of_mem_box {B : Box ι} (hB : hasIntegralVertices B) {x : ι -> Real}
    (hx : x in B) : index n x in admissibleIndex n B := by
  obtain ⟨l, u, hl, hu⟩ := hB
  simp_rw [mem_admissibleIndex_iff, Box.le_iff_bounds, box_lower, box_upper, Pi.le_def,
    index_apply, hl, hu, ← forall_and]
  push_cast
  refine fun i => ⟨?_, ?_⟩
  · exact (mem_admissibleIndex_of_mem_box_aux₁ n (x i) (l i)).mp ((hl i) ▸ (hx i).1)
  · exact (mem_admissibleIndex_of_mem_box_aux₂ n (x i) (u i)).mp ((hu i) ▸ (hx i).2)

/--
theorem `prepartition_isPartition` / 定理 `prepartition_isPartition`

English:
theorem prepartition_isPartition
  given: {B : Box ι} (hB : hasIntegralVertices B)
  proof: by
  refine fun x hx => ⟨box n (index n x), ?_, mem_box_iff_index.mpr rfl⟩
  rw [TaggedPrepartition.mem_toPrepartition]; rw [mem_prepartition_iff]
  exact ⟨index n x, mem_admissibleIndex_of_mem_box n hB hx, rfl⟩

中文:
定理 prepartition_isPartition
  条件: {B : Box ι} (hB : has整数egralVertices B)
  证明: by
  refine fun x hx => ⟨box n (index n x), ?_, mem_box_iff_index.mpr rfl⟩
  rw [TaggedPrepartition.mem_toPrepartition]; rw [mem_prepartition_iff]
  exact ⟨index n x, mem_admissibleIndex_of_mem_box n hB hx, rfl⟩

Depends on / 依赖: TaggedPrepartition, TaggedPrepartition.mem_toPrepartition, mem_admissibleIndex_of_mem_box, mem_box_iff_index, mem_box_iff_index.mpr, mem_prepartition_iff, mem_toPrepartition
-/
theorem prepartition_isPartition {B : Box ι} (hB : hasIntegralVertices B) :
    (prepartition n B).IsPartition := by
  refine fun x hx => ⟨box n (index n x), ?_, mem_box_iff_index.mpr rfl⟩
  rw [TaggedPrepartition.mem_toPrepartition]; rw [mem_prepartition_iff]
  exact ⟨index n x, mem_admissibleIndex_of_mem_box n hB hx, rfl⟩

end fintype

open Submodule Pointwise

open scoped Pointwise

variable (c : Real) (s : Set (ι -> Real)) (F : (ι -> Real) -> Real)

-- The image of `ι → ℤ` inside `ι → ℝ`
local notation "L" => span Int (Set.range (Pi.basisFun Real ι))

section finite

variable [Finite ι]

variable {n} in
/--
theorem `mem_smul_span_iff` / 定理 `mem_smul_span_iff`

English:
theorem mem_smul_span_iff
  given: {v : ι -> Real}
  proof: by
  have := Fintype.ofFinite ι
  rw [ZSpan.smul _ (inv_ne_zero (NeZero.ne _))]; rw [Module.Basis.mem_span_iff_repr_mem]
  simp_rw [Module.Basis.repr_isUnitSMul, Pi.basisFun_repr, Units.smul_def, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, inv_inv, smul_eq_mul]

中文:
定理 mem_smul_span_iff
  条件: {v : ι -> 实数}
  证明: by
  have := Fintype.ofFinite ι
  rw [ZSpan.smul _ (inv_ne_zero (NeZero.ne _))]; rw [Module.Basis.mem_span_iff_repr_mem]
  simp_rw [Module.Basis.repr_isUnitSMul, Pi.basisFun_repr, Units.smul_def, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, inv_inv, smul_eq_mul]

Depends on / 依赖: Fintype, Fintype.ofFinite, IsUnit, IsUnit.unit_spec, Module, Module.Basis.mem_span_iff_repr_mem, Module.Basis.repr_isUnitSMul, NeZero, NeZero.ne, Pi.basisFun_repr, Units.smul_def, Units.val_inv_eq_inv_val, ZSpan.smul, basisFun_repr, inv_inv, inv_ne_zero, mem_span_iff_repr_mem, ofFinite, repr_isUnitSMul, simp_rw
-/
theorem mem_smul_span_iff {v : ι -> Real} :
    v in (n : Real)⁻¹ • L ↔ forall i, n * v i in Set.range (algebraMap Int Real) := by
  have := Fintype.ofFinite ι
  rw [ZSpan.smul _ (inv_ne_zero (NeZero.ne _))]; rw [Module.Basis.mem_span_iff_repr_mem]
  simp_rw [Module.Basis.repr_isUnitSMul, Pi.basisFun_repr, Units.smul_def, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, inv_inv, smul_eq_mul]

/--
theorem `tag_mem_smul_span` / 定理 `tag_mem_smul_span`

English:
theorem tag_mem_smul_span
  given: (ν : ι -> Int)
  proof: by
  refine mem_smul_span_iff.mpr fun i => ⟨ν i + 1, ?_⟩
  rw [tag_apply]; rw [div_eq_inv_mul]; rw [← mul_assoc]; rw [mul_inv_cancel_of_invertible]; rw [one_mul]; rw [map_add]; rw [map_one]; rw [eq_intCast]

中文:
定理 tag_mem_smul_span
  条件: (ν : ι -> 整数)
  证明: by
  refine mem_smul_span_iff.mpr fun i => ⟨ν i + 1, ?_⟩
  rw [tag_apply]; rw [div_eq_inv_mul]; rw [← mul_assoc]; rw [mul_inv_cancel_of_invertible]; rw [one_mul]; rw [map_add]; rw [map_one]; rw [eq_intCast]

Depends on / 依赖: div_eq_inv_mul, eq_intCast, map_add, map_one, mem_smul_span_iff, mem_smul_span_iff.mpr, mul_assoc, mul_inv_cancel_of_invertible, one_mul, tag_apply
-/
theorem tag_mem_smul_span (ν : ι -> Int) :
    tag n ν in (n : Real)⁻¹ • L := by
  refine mem_smul_span_iff.mpr fun i => ⟨ν i + 1, ?_⟩
  rw [tag_apply]; rw [div_eq_inv_mul]; rw [← mul_assoc]; rw [mul_inv_cancel_of_invertible]; rw [one_mul]; rw [map_add]; rw [map_one]; rw [eq_intCast]

/--
theorem `tag_index_eq_self_of_mem_smul_span` / 定理 `tag_index_eq_self_of_mem_smul_span`

English:
theorem tag_index_eq_self_of_mem_smul_span
  given: {x : ι -> Real} (hx : x in (n : Real)⁻¹ • L)
  proof: by
  rw [mem_smul_span_iff] at hx
  ext i
  obtain ⟨a, ha⟩ : exists a : Int, a = n * x i := hx i
  rwa [tag_apply, index_apply, Int.cast_sub, Int.cast_one, sub_add_cancel, ← ha, Int.ceil_intCast,
    div_eq_iff (NeZero.ne _), mul_comm]

中文:
定理 tag_index_eq_self_of_mem_smul_span
  条件: {x : ι -> 实数} (hx : x in (n : 实数)⁻¹ • L)
  证明: by
  rw [mem_smul_span_iff] at hx
  ext i
  obtain ⟨a, ha⟩ : exists a : Int, a = n * x i := hx i
  rwa [tag_apply, index_apply, Int.cast_sub, Int.cast_one, sub_add_cancel, ← ha, Int.ceil_intCast,
    div_eq_iff (NeZero.ne _), mul_comm]

Depends on / 依赖: Int.cast_one, Int.cast_sub, Int.ceil_intCast, NeZero, NeZero.ne, cast_one, cast_sub, ceil_intCast, div_eq_iff, index_apply, mem_smul_span_iff, mul_comm, sub_add_cancel, tag_apply
-/
theorem tag_index_eq_self_of_mem_smul_span {x : ι -> Real} (hx : x in (n : Real)⁻¹ • L) :
    tag n (index n x) = x := by
  rw [mem_smul_span_iff] at hx
  ext i
  obtain ⟨a, ha⟩ : exists a : Int, a = n * x i := hx i
  rwa [tag_apply, index_apply, Int.cast_sub, Int.cast_one, sub_add_cancel, ← ha, Int.ceil_intCast,
    div_eq_iff (NeZero.ne _), mul_comm]

/--
theorem `eq_of_mem_smul_span_of_index_eq_index` / 定理 `eq_of_mem_smul_span_of_index_eq_index`

English:
theorem eq_of_mem_smul_span_of_index_eq_index
  statement: {x y : ι -> Real} (hx : x in (n : Real)⁻¹ • L)
  proof: by
  rw [← tag_index_eq_self_of_mem_smul_span n hx]; rw [← tag_index_eq_self_of_mem_smul_span n hy]; rw [h]

中文:
定理 eq_of_mem_smul_span_of_index_eq_index
  结论: {x y : ι -> 实数} (hx : x in (n : 实数)⁻¹ • L)
  证明: by
  rw [← tag_index_eq_self_of_mem_smul_span n hx]; rw [← tag_index_eq_self_of_mem_smul_span n hy]; rw [h]

Depends on / 依赖: tag_index_eq_self_of_mem_smul_span
-/
theorem eq_of_mem_smul_span_of_index_eq_index {x y : ι -> Real} (hx : x in (n : Real)⁻¹ • L)
    (hy : y in (n : Real)⁻¹ • L) (h : index n x = index n y) : x = y := by
  rw [← tag_index_eq_self_of_mem_smul_span n hx]; rw [← tag_index_eq_self_of_mem_smul_span n hy]; rw [h]

/--
Definition of `tendsto_card_div_pow₁` / `tendsto_card_div_pow₁` 的定义

English:
definition tendsto_card_div_pow₁
  signature: {c : Real} (hc : c != 0)
  body: Equiv.subtypeEquiv (Equiv.smulRight hc) (fun x => by
    simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hc,
      ← Set.mem_inv_smul_set_iff₀ hc])

中文:
定义 tendsto_card_div_pow₁
  签名: {c : 实数} (hc : c != 0)
  定义体: Equiv.subtypeEquiv (Equiv.smulRight hc) (fun x => by
    simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hc,
      ← Set.mem_inv_smul_set_iff₀ hc])
-/
private def tendsto_card_div_pow₁ {c : Real} (hc : c != 0) :
    ↑(s inter c⁻¹ • L) ≃ ↑(c • s inter L) :=
  Equiv.subtypeEquiv (Equiv.smulRight hc) (fun x => by
    simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hc,
      ← Set.mem_inv_smul_set_iff₀ hc])

/--
theorem `tendsto_card_div_pow₂` / 定理 `tendsto_card_div_pow₂`

English:
theorem tendsto_card_div_pow₂
  statement: (hs₁ : IsBounded s)
  proof: by
  have := Fintype.ofFinite ι
  rw [Nat.card_congr (tendsto_card_div_pow₁ s hx.ne')]; rw [Nat.card_congr (tendsto_card_div_pow₁ s (hx.trans_le hy).ne')]
  refine Nat.card_mono ?_ ?_
  · exact ZSpan.setFinite_inter _ (IsBounded.smul₀ hs₁ y)
· exact Set.inter_subset_inter_left _ hs₄ hx hy

中文:
定理 tendsto_card_div_pow₂
  结论: (hs₁ : IsBounded s)
  证明: by
  have := Fintype.ofFinite ι
  rw [Nat.card_congr (tendsto_card_div_pow₁ s hx.ne')]; rw [Nat.card_congr (tendsto_card_div_pow₁ s (hx.trans_le hy).ne')]
  refine Nat.card_mono ?_ ?_
  · exact ZSpan.setFinite_inter _ (IsBounded.smul₀ hs₁ y)
· exact Set.inter_subset_inter_left _ hs₄ hx hy
-/
private theorem tendsto_card_div_pow₂ (hs₁ : IsBounded s)
    (hs₄ : forall ⦃x y : Real⦄, 0 < x -> x <= y -> x • s subseteq y • s) {x y : Real} (hx : 0 < x) (hy : x <= y) :
    Nat.card ↑(s inter x⁻¹ • L) <= Nat.card ↑(s inter y⁻¹ • L) := by
  have := Fintype.ofFinite ι
  rw [Nat.card_congr (tendsto_card_div_pow₁ s hx.ne')]; rw [Nat.card_congr (tendsto_card_div_pow₁ s (hx.trans_le hy).ne')]
  refine Nat.card_mono ?_ ?_
  · exact ZSpan.setFinite_inter _ (IsBounded.smul₀ hs₁ y)
· exact Set.inter_subset_inter_left _ hs₄ hx hy

end finite

section fintype

variable [Fintype ι]

/--
theorem `integralSum_eq_tsum_div` / 定理 `integralSum_eq_tsum_div`

English:
theorem integralSum_eq_tsum_div
  given: {B : Box ι} (hB : hasIntegralVertices B) (hs₀ : s <= B)
  proof: by
  classical
  unfold integralSum
  have : Fintype ↑(s inter (n : Real)⁻¹ • L) := by
    apply Set.Finite.fintype
    rw [← coe_pointwise_smul]; rw [ZSpan.smul _ (inv_ne_zero (NeZero.ne _))]
    exact ZSpan.setFinite_inter _ (B.isBounded.subset hs₀)
  rw [tsum_fintype]; rw [Finset.sum_set_coe]; rw

中文:
定理 integralSum_eq_tsum_div
  条件: {B : Box ι} (hB : has整数egralVertices B) (hs₀ : s <= B)
  证明: by
  classical
  unfold integralSum
  have : Fintype ↑(s inter (n : Real)⁻¹ • L) := by
    apply Set.Finite.fintype
    rw [← coe_pointwise_smul]; rw [ZSpan.smul _ (inv_ne_zero (NeZero.ne _))]
    exact ZSpan.setFinite_inter _ (B.isBounded.subset hs₀)
  rw [tsum_fintype]; rw [Finset.sum_set_coe]; rw

Depends on / 依赖: B.isBounded.subset, BoxAdditiveMap, BoxAdditiveMap.toSMul_apply, Finite, Finset, Finset.sum, Finset.sum_const_zero, Finset.sum_div, Finset.sum_ite, Finset.sum_set_coe, Fintype, Measure, Measure.toBoxAdditive_apply, NeZero, NeZero.ne, Set.Finite.fintype, Set.indicator_apply, ZSpan.setFinite_inter, ZSpan.smul, add_zero
-/
theorem integralSum_eq_tsum_div {B : Box ι} (hB : hasIntegralVertices B) (hs₀ : s <= B) :
    integralSum (Set.indicator s F) (BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
      (prepartition n B) = (∑' x : ↑(s inter (n : Real)⁻¹ • L), F x) / n ^ card ι := by
  classical
  unfold integralSum
  have : Fintype ↑(s inter (n : Real)⁻¹ • L) := by
    apply Set.Finite.fintype
    rw [← coe_pointwise_smul]; rw [ZSpan.smul _ (inv_ne_zero (NeZero.ne _))]
    exact ZSpan.setFinite_inter _ (B.isBounded.subset hs₀)
  rw [tsum_fintype]; rw [Finset.sum_set_coe]; rw [Finset.sum_div]; rw [eq_comm]
  simp_rw [Set.indicator_apply, apply_ite, BoxAdditiveMap.toSMul_apply, Measure.toBoxAdditive_apply,
    smul_eq_mul, mul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_bij (fun x _ => box n (index n x)) (fun _ hx => Finset.mem_filter.mpr ?_)
    (fun _ hx _ hy h => ?_) (fun I hI => ?_) (fun _ hx => ?_)
  · rw [Set.mem_toFinset] at hx
    refine ⟨mem_prepartition_boxes_iff.mpr
      ⟨index n _, mem_admissibleIndex_of_mem_box n hB (hs₀ hx.1), rfl⟩, ?_⟩
    simp_rw [prepartition_tag n (mem_admissibleIndex_of_mem_box n hB (hs₀ hx.1)),
      tag_index_eq_self_of_mem_smul_span n hx.2, hx.1]
  · rw [Set.mem_toFinset] at hx hy
    exact eq_of_mem_smul_span_of_index_eq_index n hx.2 hy.2 (box_injective n h)
  · rw [Finset.mem_filter] at hI
    refine ⟨(prepartition n B).tag I, Set.mem_toFinset.mpr ⟨hI.2, ?_⟩, box_index_tag_eq_self n hI.1⟩
    rw [← box_index_tag_eq_self n hI.1]; rw [prepartition_tag n
      (mem_admissibleIndex_of_mem_box n hB (hs₀ hI.2))]
    exact tag_mem_smul_span _ _
  · rw [Set.mem_toFinset] at hx
    rw [measureReal_def]; rw [volume_box]; rw [prepartition_tag n (mem_admissibleIndex_of_mem_box n hB (hs₀ hx.1))]; rw [tag_index_eq_self_of_mem_smul_span n hx.2]; rw [ENNReal.toReal_div]; rw [ENNReal.toReal_one]; rw [ENNReal.toReal_pow]; rw [ENNReal.toReal_natCast]; rw [mul_comm_div]; rw [one_mul]

open Filter

/--
theorem `_root_.tendsto_tsum_div_pow_atTop_integral` / 定理 `_root_.tendsto_tsum_div_pow_atTop_integral`

English:
theorem _root_.tendsto_tsum_div_pow_atTop_integral
  statement: (hF : Continuous F) (hs₁ : IsBounded s)
  proof: by
  obtain ⟨B, hB, hs₀⟩ := le_hasIntegralVertices_of_isBounded hs₁
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have h₁ : exists C, forall x in Box.Icc B, ‖Set.indicator s F x‖ <= C := by
    obtain ⟨C₀, h₀⟩ := (Box.isCompact_Icc B).exists_bound_of_continuousOn hF.continuousOn
    refine ⟨max

中文:
定理 _root_.tendsto_tsum_div_pow_atTop_integral
  结论: (hF : 连续 F) (hs₁ : IsBounded s)
  证明: by
  obtain ⟨B, hB, hs₀⟩ := le_hasIntegralVertices_of_isBounded hs₁
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have h₁ : exists C, forall x in Box.Icc B, ‖Set.indicator s F x‖ <= C := by
    obtain ⟨C₀, h₀⟩ := (Box.isCompact_Icc B).exists_bound_of_continuousOn hF.continuousOn
    refine ⟨max

Depends on / 依赖: Box.Icc, Box.isCompact_Icc, ContinuousAt, Metric, Metric.tendsto_atTop.mpr, Set.indicator, continuousOn, exists_bound_of_continuousOn, filter_upwards, hF.continuousOn, indicator, isCompact_Icc, le_hasIntegralVertices_of_isBounded, le_max_left, le_max_of_le_right, norm_zero, norm_zero.trans_le, s.indicator, split_ifs, tendsto_atTop
-/
theorem _root_.tendsto_tsum_div_pow_atTop_integral (hF : Continuous F) (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : Nat => (∑' x : ↑(s inter (n : Real)⁻¹ • L), F x) / n ^ card ι)
      atTop (nhds (∫ x in s, F x)) := by
  obtain ⟨B, hB, hs₀⟩ := le_hasIntegralVertices_of_isBounded hs₁
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have h₁ : exists C, forall x in Box.Icc B, ‖Set.indicator s F x‖ <= C := by
    obtain ⟨C₀, h₀⟩ := (Box.isCompact_Icc B).exists_bound_of_continuousOn hF.continuousOn
    refine ⟨max 0 C₀, fun x hx => ?_⟩
    rw [Set.indicator]
    split_ifs with hs
    · exact le_max_of_le_right (h₀ x hx)
· exact norm_zero.trans_le le_max_left 0 _
  have h₂ : forallᵐ x, ContinuousAt (s.indicator F) x := by
    filter_upwards [compl_mem_ae_iff.mpr hs₃] with _ h
      using (hF.continuousOn).continuousAt_indicator h
  obtain ⟨r, hr₁, hr₂⟩ := (hasIntegral_iff.mp <|
      AEContinuous.hasBoxIntegral (volume : Measure (ι -> Real)) h₁ h₂
        IntegrationParams.Riemann) (ε / 2) (half_pos hε)
  refine ⟨⌈(r 0 0 : Real)⁻¹⌉₊, fun n hn => lt_of_le_of_lt ?_ (half_lt_self_iff.mpr hε)⟩
  have : NeZero n :=
⟨Nat.ne_zero_iff_zero_lt.mpr (Nat.ceil_pos.mpr (inv_pos.mpr (r 0 0).prop)).trans_le hn⟩
  rw [← integralSum_eq_tsum_div _ s F hB hs₀]; rw [← Measure.restrict_restrict_of_subset hs₀]; rw [← integral_indicator hs₂]
  refine hr₂ 0 _ ⟨?_, fun _ => ?_, fun h => ?_, fun h => ?_⟩ (prepartition_isPartition _ hB)
  · rw [show r 0 = fun _ => r 0 0 from funext_iff.mpr (hr₁ 0 rfl)]
    apply prepartition_isSubordinate n B
    rw [one_div]; rw [inv_le_comm₀ (mod_cast (Nat.pos_of_neZero n)) (r 0 0).prop]
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
  · exact prepartition_isHenstock n B
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h

/--
theorem `_root_.tendsto_card_div_pow_atTop_volume` / 定理 `_root_.tendsto_card_div_pow_atTop_volume`

English:
theorem _root_.tendsto_card_div_pow_atTop_volume
  statement: (hs₁ : IsBounded s)
  proof: by
  convert! tendsto_tsum_div_pow_atTop_integral s (fun _ => 1) continuous_const hs₁ hs₂ hs₃
  · rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  · rw [setIntegral_const, smul_eq_mul, mul_one]

中文:
定理 _root_.tendsto_card_div_pow_atTop_volume
  结论: (hs₁ : IsBounded s)
  证明: by
  convert! tendsto_tsum_div_pow_atTop_integral s (fun _ => 1) continuous_const hs₁ hs₂ hs₃
  · rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  · rw [setIntegral_const, smul_eq_mul, mul_one]

Depends on / 依赖: Nat.cast_inj, cast_inj, continuous_const, convert, mul_one, nsmul_eq_mul, setIntegral_const, smul_eq_mul, tendsto_tsum_div_pow_atTop_integral, tsum_const
-/
theorem _root_.tendsto_card_div_pow_atTop_volume (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : Nat => (Nat.card ↑(s inter (n : Real)⁻¹ • L) : Real) / n ^ card ι)
      atTop (𝓝 (volume.real s)) := by
  convert! tendsto_tsum_div_pow_atTop_integral s (fun _ => 1) continuous_const hs₁ hs₂ hs₃
  · rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  · rw [setIntegral_const, smul_eq_mul, mul_one]

/--
theorem `tendsto_card_div_pow₃` / 定理 `tendsto_card_div_pow₃`

English:
theorem tendsto_card_div_pow₃
  statement: (hs₁ : IsBounded s)
  proof: by
  filter_upwards [eventually_ge_atTop 1] with x hx
  gcongr
  exact tendsto_card_div_pow₂ s hs₁ hs₄ (Nat.cast_pos.mpr (Nat.floor_pos.mpr hx))
    (Nat.floor_le (zero_le_one.trans hx))

中文:
定理 tendsto_card_div_pow₃
  结论: (hs₁ : IsBounded s)
  证明: by
  filter_upwards [eventually_ge_atTop 1] with x hx
  gcongr
  exact tendsto_card_div_pow₂ s hs₁ hs₄ (Nat.cast_pos.mpr (Nat.floor_pos.mpr hx))
    (Nat.floor_le (zero_le_one.trans hx))
-/
private theorem tendsto_card_div_pow₃ (hs₁ : IsBounded s)
    (hs₄ : forall ⦃x y : Real⦄, 0 < x -> x <= y -> x • s subseteq y • s) :
    forallᶠ x : Real in atTop, (Nat.card ↑(s inter (⌊x⌋₊ : Real)⁻¹ • L) : Real) / x ^ card ι <=
      (Nat.card ↑(s inter x⁻¹ • L) : Real) / x ^ card ι := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  gcongr
  exact tendsto_card_div_pow₂ s hs₁ hs₄ (Nat.cast_pos.mpr (Nat.floor_pos.mpr hx))
    (Nat.floor_le (zero_le_one.trans hx))

/--
theorem `tendsto_card_div_pow₄` / 定理 `tendsto_card_div_pow₄`

English:
theorem tendsto_card_div_pow₄
  statement: (hs₁ : IsBounded s)
  proof: by
  filter_upwards [eventually_gt_atTop 0] with x hx
  gcongr
  exact tendsto_card_div_pow₂ s hs₁ hs₄ hx (Nat.le_ceil _)

中文:
定理 tendsto_card_div_pow₄
  结论: (hs₁ : IsBounded s)
  证明: by
  filter_upwards [eventually_gt_atTop 0] with x hx
  gcongr
  exact tendsto_card_div_pow₂ s hs₁ hs₄ hx (Nat.le_ceil _)
-/
private theorem tendsto_card_div_pow₄ (hs₁ : IsBounded s)
    (hs₄ : forall ⦃x y : Real⦄, 0 < x -> x <= y -> x • s subseteq y • s) :
    forallᶠ x : Real in atTop, (Nat.card ↑(s inter x⁻¹ • L) : Real) / x ^ card ι <=
      (Nat.card ↑(s inter (⌈x⌉₊ : Real)⁻¹ • L) : Real) / x ^ card ι := by
  filter_upwards [eventually_gt_atTop 0] with x hx
  gcongr
  exact tendsto_card_div_pow₂ s hs₁ hs₄ hx (Nat.le_ceil _)

/--
theorem `tendsto_card_div_pow₅` / 定理 `tendsto_card_div_pow₅`

English:
theorem tendsto_card_div_pow₅
  proof: by
  filter_upwards [eventually_ge_atTop 1] with x hx
  have : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  rw [div_pow]; rw [mul_div]; rw [div_mul_cancel₀ _ (by positivity)]

中文:
定理 tendsto_card_div_pow₅
  证明: by
  filter_upwards [eventually_ge_atTop 1] with x hx
  have : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  rw [div_pow]; rw [mul_div]; rw [div_mul_cancel₀ _ (by positivity)]
-/
private theorem tendsto_card_div_pow₅ :
    (fun x => (Nat.card ↑(s inter (⌊x⌋₊ : Real)⁻¹ • L) : Real) / ⌊x⌋₊ ^ card ι * (⌊x⌋₊ / x) ^ card ι)
      =ᶠ[atTop] (fun x => (Nat.card ↑(s inter (⌊x⌋₊ : Real)⁻¹ • L) : Real) / x ^ card ι) := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  have : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  rw [div_pow]; rw [mul_div]; rw [div_mul_cancel₀ _ (by positivity)]

/--
theorem `tendsto_card_div_pow₆` / 定理 `tendsto_card_div_pow₆`

English:
theorem tendsto_card_div_pow₆
  proof: by
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [div_pow]; rw [mul_div]; rw [div_mul_cancel₀ _ (by positivity)]

中文:
定理 tendsto_card_div_pow₆
  证明: by
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [div_pow]; rw [mul_div]; rw [div_mul_cancel₀ _ (by positivity)]
-/
private theorem tendsto_card_div_pow₆ :
    (fun x => (Nat.card ↑(s inter (⌈x⌉₊ : Real)⁻¹ • L) : Real) / ⌈x⌉₊ ^ card ι * (⌈x⌉₊ / x) ^ card ι)
          =ᶠ[atTop] (fun x => (Nat.card ↑(s inter (⌈x⌉₊ : Real)⁻¹ • L) : Real) / x ^ card ι) := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [div_pow]; rw [mul_div]; rw [div_mul_cancel₀ _ (by positivity)]

/--
theorem `_root_.tendsto_card_div_pow_atTop_volume'` / 定理 `_root_.tendsto_card_div_pow_atTop_volume'`

English:
theorem _root_.tendsto_card_div_pow_atTop_volume'
  statement: (hs₁ : IsBounded s)
  proof: by
  rw [show volume.real s = volume.real s * 1 ^ card ι by ring]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_
    (tendsto_card_div_pow₃ s hs₁ hs₄) (tendsto_card_div_pow₄ s hs₁ hs₄)
  · refine Tendsto.congr' (tendsto_card_div_pow₅ s) (Tendsto.mul ?_ (Tendsto.pow ?_ _))
    · exact Tend

中文:
定理 _root_.tendsto_card_div_pow_atTop_volume'
  结论: (hs₁ : IsBounded s)
  证明: by
  rw [show volume.real s = volume.real s * 1 ^ card ι by ring]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_
    (tendsto_card_div_pow₃ s hs₁ hs₄) (tendsto_card_div_pow₄ s hs₁ hs₄)
  · refine Tendsto.congr' (tendsto_card_div_pow₅ s) (Tendsto.mul ?_ (Tendsto.pow ?_ _))
    · exact Tend

Depends on / 依赖: Tendsto, Tendsto.comp, Tendsto.congr, Tendsto.mul, Tendsto.pow, tendsto_card_div_pow_atTop_volume, tendsto_nat_floor_atTop, tendsto_nat_floor_div_atTop, tendsto_of_tendsto_of_tendsto_of_le_of_le, volume, volume.real
-/
theorem _root_.tendsto_card_div_pow_atTop_volume' (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0)
    (hs₄ : forall ⦃x y : Real⦄, 0 < x -> x <= y -> x • s subseteq y • s) :
    Tendsto (fun x : Real => (Nat.card ↑(s inter x⁻¹ • L) : Real) / x ^ card ι)
      atTop (𝓝 (volume.real s)) := by
  rw [show volume.real s = volume.real s * 1 ^ card ι by ring]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_
    (tendsto_card_div_pow₃ s hs₁ hs₄) (tendsto_card_div_pow₄ s hs₁ hs₄)
  · refine Tendsto.congr' (tendsto_card_div_pow₅ s) (Tendsto.mul ?_ (Tendsto.pow ?_ _))
    · exact Tendsto.comp (tendsto_card_div_pow_atTop_volume s hs₁ hs₂ hs₃) tendsto_nat_floor_atTop
    · exact tendsto_nat_floor_div_atTop
  · refine Tendsto.congr' (tendsto_card_div_pow₆ s) (Tendsto.mul ?_ (Tendsto.pow ?_ _))
    · exact Tendsto.comp (tendsto_card_div_pow_atTop_volume s hs₁ hs₂ hs₃) tendsto_nat_ceil_atTop
    · exact tendsto_nat_ceil_div_atTop

end fintype

end BoxIntegral.unitPartition
