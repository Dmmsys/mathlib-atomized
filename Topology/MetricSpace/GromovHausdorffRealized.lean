/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Gluing
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The Gromov-Hausdorff distance is realized

In this file, we construct of a good coupling between nonempty compact metric spaces, minimizing
their Hausdorff distance. This construction is instrumental to study the Gromov-Hausdorff
distance between nonempty compact metric spaces.

Given two nonempty compact metric spaces `X` and `Y`, we define `OptimalGHCoupling X Y` as a
compact metric space, together with two isometric embeddings `optimalGHInjl` and `optimalGHInjr`
respectively of `X` and `Y` into `OptimalGHCoupling X Y`. The main property of the optimal
coupling is that the Hausdorff distance between `X` and `Y` in `OptimalGHCoupling X Y` is smaller
than the corresponding distance in any other coupling. We do not prove completely this fact in this
file, but we show a good enough approximation of this fact in `hausdorffDist_optimal_le_HD`, that
will suffice to obtain the full statement once the Gromov-Hausdorff distance is properly defined,
in `hausdorffDist_optimal`.

The key point in the construction is that the set of possible distances coming from isometric
embeddings of `X` and `Y` in metric spaces is a set of equicontinuous functions. By Arzela-Ascoli,
it is compact, and one can find such a distance which is minimal. This distance defines a premetric
space structure on `X ⊕ Y`. The corresponding metric quotient is `OptimalGHCoupling X Y`.
-/

@[expose] public section


noncomputable section

universe u v w

open Topology NNReal Set Function TopologicalSpace Filter Metric Quotient BoundedContinuousFunction
open Sum (inl inr)

attribute [local instance] metricSpaceSum

namespace GromovHausdorff


section GromovHausdorffRealized

/-! This section shows that the Gromov-Hausdorff distance
is realized. For this, we consider candidate distances on the disjoint union
`X ⊕ Y` of two compact nonempty metric spaces, almost realizing the Gromov-Hausdorff
distance, and show that they form a compact family by applying Arzela-Ascoli
theorem. The existence of a minimizer follows. -/
section Definitions

variable (X : Type u) (Y : Type v) [MetricSpace X] [MetricSpace Y]


set_option backward.privateInPublic true in
/--
Definition of `ProdSpaceFun` / `ProdSpaceFun` 的定义

English:
abbreviation ProdSpaceFun
  signature: : Type _
  body: (X oplus Y) × (X oplus Y) -> Real

中文:
缩写 ProdSpaceFun
  签名: : 类型 _
  定义体: (X oplus Y) × (X oplus Y) -> Real
-/
private abbrev ProdSpaceFun : Type _ :=
  (X oplus Y) × (X oplus Y) -> Real

set_option backward.privateInPublic true in
/--
Definition of `Cb` / `Cb` 的定义

English:
abbreviation Cb
  signature: : Type _
  body: BoundedContinuousFunction ((X oplus Y) × (X oplus Y)) Real

中文:
缩写 Cb
  签名: : 类型 _
  定义体: BoundedContinuousFunction ((X oplus Y) × (X oplus Y)) Real
-/
private abbrev Cb : Type _ :=
  BoundedContinuousFunction ((X oplus Y) × (X oplus Y)) Real

set_option backward.privateInPublic true in
/--
Definition of `maxVar` / `maxVar` 的定义

English:
definition maxVar
  signature: : Real>=0
  body: 2 * ⟨diam (univ : Set X), diam_nonneg⟩ + 1 + 2 * ⟨diam (univ : Set Y), diam_nonneg⟩

中文:
定义 maxVar
  签名: : 实数>=0
  定义体: 2 * ⟨diam (univ : Set X), diam_nonneg⟩ + 1 + 2 * ⟨diam (univ : Set Y), diam_nonneg⟩
-/
private def maxVar : Real>=0 :=
  2 * ⟨diam (univ : Set X), diam_nonneg⟩ + 1 + 2 * ⟨diam (univ : Set Y), diam_nonneg⟩

/--
theorem `one_le_maxVar` / 定理 `one_le_maxVar`

English:
theorem one_le_maxVar
  statement: 1 <= maxVar X Y
  proof: calc
    (1 : Real) = 2 * 0 + 1 + 2 * 0 := by simp
    _ <= 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by gcongr <;> positivity

中文:
定理 one_le_maxVar
  结论: 1 <= maxVar X Y
  证明: calc
    (1 : Real) = 2 * 0 + 1 + 2 * 0 := by simp
    _ <= 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by gcongr <;> positivity
-/
private theorem one_le_maxVar : 1 <= maxVar X Y :=
  calc
    (1 : Real) = 2 * 0 + 1 + 2 * 0 := by simp
    _ <= 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by gcongr <;> positivity

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `candidates` / `candidates` 的定义

English:
definition candidates
  signature: : Set (ProdSpaceFun X Y)
  body: { f | (((((forall x y : X, f (Sum.inl x, Sum.inl y) = dist x y) ∧
      forall x y : Y, f (Sum.inr x, Sum.inr y) = dist x y) ∧
      forall x y, f (x, y) = f (y, x)) ∧
      forall x y z, f (x, z) <= f (x, y) + f (y, z)) ∧
      forall x, f (x, x) = 0) ∧
      forall x y, f (x, y) <= maxVar X Y }

中文:
定义 candidates
  签名: : 集合 (ProdSpaceFun X Y)
  定义体: { f | (((((forall x y : X, f (Sum.inl x, Sum.inl y) = dist x y) ∧
      forall x y : Y, f (Sum.inr x, Sum.inr y) = dist x y) ∧
      forall x y, f (x, y) = f (y, x)) ∧
      forall x y z, f (x, z) <= f (x, y) + f (y, z)) ∧
      forall x, f (x, x) = 0) ∧
      forall x y, f (x, y) <= maxVar X Y }

Depends on / 依赖: Sum.inl, Sum.inr, maxVar
-/
def candidates : Set (ProdSpaceFun X Y) :=
  { f | (((((forall x y : X, f (Sum.inl x, Sum.inl y) = dist x y) ∧
      forall x y : Y, f (Sum.inr x, Sum.inr y) = dist x y) ∧
      forall x y, f (x, y) = f (y, x)) ∧
      forall x y z, f (x, z) <= f (x, y) + f (y, z)) ∧
      forall x, f (x, x) = 0) ∧
      forall x y, f (x, y) <= maxVar X Y }

set_option backward.privateInPublic true in
/--
Definition of `candidatesB` / `candidatesB` 的定义

English:
definition candidatesB
  signature: : Set (Cb X Y)
  body: { f : Cb X Y | (f : _ -> Real) in candidates X Y }

中文:
定义 candidatesB
  签名: : 集合 (Cb X Y)
  定义体: { f : Cb X Y | (f : _ -> Real) in candidates X Y }
-/
private def candidatesB : Set (Cb X Y) :=
  { f : Cb X Y | (f : _ -> Real) in candidates X Y }

end Definitions

section Constructions

variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  {f : ProdSpaceFun X Y} {x y z t : X oplus Y}

attribute [local instance 10] Classical.inhabited_of_nonempty'

/--
theorem `maxVar_bound` / 定理 `maxVar_bound`

English:
theorem maxVar_bound
  given: [CompactSpace X] [Nonempty X] [CompactSpace Y] [Nonempty Y]
  proof: calc
    dist x y <= diam (univ : Set (X oplus Y)) :=
      dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)
    _ = diam (range inl union range inr : Set (X oplus Y)) := by rw [range_inl_union_range_inr]
    _ <= diam (range inl : Set (X oplus Y)) + dist (inl default) (inr de

中文:
定理 maxVar_bound
  条件: [紧空间 X] [非空 X] [紧空间 Y] [非空 Y]
  证明: calc
    dist x y <= diam (univ : Set (X oplus Y)) :=
      dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)
    _ = diam (range inl union range inr : Set (X oplus Y)) := by rw [range_inl_union_range_inr]
    _ <= diam (range inl : Set (X oplus Y)) + dist (inl default) (inr de
-/
private theorem maxVar_bound [CompactSpace X] [Nonempty X] [CompactSpace Y] [Nonempty Y] :
    dist x y <= maxVar X Y :=
  calc
    dist x y <= diam (univ : Set (X oplus Y)) :=
      dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)
    _ = diam (range inl union range inr : Set (X oplus Y)) := by rw [range_inl_union_range_inr]
    _ <= diam (range inl : Set (X oplus Y)) + dist (inl default) (inr default) +
        diam (range inr : Set (X oplus Y)) :=
      (diam_union (mem_range_self _) (mem_range_self _))
    _ = diam (univ : Set X) + (dist (α := X) default default + 1 + dist (α := Y) default default) +
        diam (univ : Set Y) := by
      rw [isometry_inl.diam_range]; rw [isometry_inr.diam_range]
      rfl
    _ = 1 * diam (univ : Set X) + 1 + 1 * diam (univ : Set Y) := by simp
    _ <= 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by gcongr <;> norm_num

set_option backward.privateInPublic true in
/--
theorem `candidates_symm` / 定理 `candidates_symm`

English:
theorem candidates_symm
  given: (fA : f in candidates X Y)
  statement: f (x, y) = f (y, x)
  proof: fA.1.1.1.2 x y

中文:
定理 candidates_symm
  条件: (fA : f in candidates X Y)
  结论: f (x, y) = f (y, x)
  证明: fA.1.1.1.2 x y
-/
private theorem candidates_symm (fA : f in candidates X Y) : f (x, y) = f (y, x) :=
  fA.1.1.1.2 x y

set_option backward.privateInPublic true in
/--
theorem `candidates_triangle` / 定理 `candidates_triangle`

English:
theorem candidates_triangle
  given: (fA : f in candidates X Y)
  statement: f (x, z) <= f (x, y) + f (y, z)
  proof: fA.1.1.2 x y z

中文:
定理 candidates_triangle
  条件: (fA : f in candidates X Y)
  结论: f (x, z) <= f (x, y) + f (y, z)
  证明: fA.1.1.2 x y z
-/
private theorem candidates_triangle (fA : f in candidates X Y) : f (x, z) <= f (x, y) + f (y, z) :=
  fA.1.1.2 x y z

set_option backward.privateInPublic true in
/--
theorem `candidates_refl` / 定理 `candidates_refl`

English:
theorem candidates_refl
  given: (fA : f in candidates X Y)
  statement: f (x, x) = 0
  proof: fA.1.2 x

中文:
定理 candidates_refl
  条件: (fA : f in candidates X Y)
  结论: f (x, x) = 0
  证明: fA.1.2 x
-/
private theorem candidates_refl (fA : f in candidates X Y) : f (x, x) = 0 :=
  fA.1.2 x

set_option backward.privateInPublic true in
/--
theorem `candidates_nonneg` / 定理 `candidates_nonneg`

English:
theorem candidates_nonneg
  given: (fA : f in candidates X Y)
  statement: 0 <= f (x, y)
  proof: by
  grind [candidates_symm, candidates_triangle]

中文:
定理 candidates_nonneg
  条件: (fA : f in candidates X Y)
  结论: 0 <= f (x, y)
  证明: by
  grind [candidates_symm, candidates_triangle]
-/
private theorem candidates_nonneg (fA : f in candidates X Y) : 0 <= f (x, y) := by
  grind [candidates_symm, candidates_triangle]

set_option backward.privateInPublic true in
/--
theorem `candidates_dist_inl` / 定理 `candidates_dist_inl`

English:
theorem candidates_dist_inl
  given: (fA : f in candidates X Y) (x y : X)
  proof: fA.1.1.1.1.1 x y

中文:
定理 candidates_dist_inl
  条件: (fA : f in candidates X Y) (x y : X)
  证明: fA.1.1.1.1.1 x y
-/
private theorem candidates_dist_inl (fA : f in candidates X Y) (x y : X) :
    f (inl x, inl y) = dist x y :=
  fA.1.1.1.1.1 x y

set_option backward.privateInPublic true in
/--
theorem `candidates_dist_inr` / 定理 `candidates_dist_inr`

English:
theorem candidates_dist_inr
  given: (fA : f in candidates X Y) (x y : Y)
  proof: fA.1.1.1.1.2 x y

中文:
定理 candidates_dist_inr
  条件: (fA : f in candidates X Y) (x y : Y)
  证明: fA.1.1.1.1.2 x y
-/
private theorem candidates_dist_inr (fA : f in candidates X Y) (x y : Y) :
    f (inr x, inr y) = dist x y :=
  fA.1.1.1.1.2 x y

set_option backward.privateInPublic true in
/--
theorem `candidates_le_maxVar` / 定理 `candidates_le_maxVar`

English:
theorem candidates_le_maxVar
  given: (fA : f in candidates X Y)
  statement: f (x, y) <= maxVar X Y
  proof: fA.2 x y

中文:
定理 candidates_le_maxVar
  条件: (fA : f in candidates X Y)
  结论: f (x, y) <= maxVar X Y
  证明: fA.2 x y
-/
private theorem candidates_le_maxVar (fA : f in candidates X Y) : f (x, y) <= maxVar X Y :=
  fA.2 x y

set_option backward.privateInPublic true in
/--
theorem `candidates_dist_bound` / 定理 `candidates_dist_bound`

English:
theorem candidates_dist_bound
  given: (fA : f in candidates X Y)
  proof: candidates_dist_inl fA x y
      _ = dist (α := X oplus Y) (inl x) (inl y) := by
        rw [@Sum.dist_eq X Y]
        rfl
      _ = 1 * dist (α := X oplus Y) (inl x) (inl y) := by ring
      _ <= maxVar X Y * dist (inl x) (inl y) := by gcongr; exact one_le_maxVar X Y
  | inl x, inr y =>
    calc
  

中文:
定理 candidates_dist_bound
  条件: (fA : f in candidates X Y)
  证明: candidates_dist_inl fA x y
      _ = dist (α := X oplus Y) (inl x) (inl y) := by
        rw [@Sum.dist_eq X Y]
        rfl
      _ = 1 * dist (α := X oplus Y) (inl x) (inl y) := by ring
      _ <= maxVar X Y * dist (inl x) (inl y) := by gcongr; exact one_le_maxVar X Y
  | inl x, inr y =>
    calc
  
-/
private theorem candidates_dist_bound (fA : f in candidates X Y) :
    forall {x y : X oplus Y}, f (x, y) <= maxVar X Y * dist x y
  | inl x, inl y =>
    calc
      f (inl x, inl y) = dist x y := candidates_dist_inl fA x y
      _ = dist (α := X oplus Y) (inl x) (inl y) := by
        rw [@Sum.dist_eq X Y]
        rfl
      _ = 1 * dist (α := X oplus Y) (inl x) (inl y) := by ring
      _ <= maxVar X Y * dist (inl x) (inl y) := by gcongr; exact one_le_maxVar X Y
  | inl x, inr y =>
    calc
      f (inl x, inr y) <= maxVar X Y := candidates_le_maxVar fA
      _ = maxVar X Y * 1 := by simp
      _ <= maxVar X Y * dist (inl x) (inr y) := by gcongr; apply Sum.one_le_dist_inl_inr
  | inr x, inl y =>
    calc
      f (inr x, inl y) <= maxVar X Y := candidates_le_maxVar fA
      _ = maxVar X Y * 1 := by simp
      _ <= maxVar X Y * dist (inl x) (inr y) := by gcongr; apply Sum.one_le_dist_inl_inr
  | inr x, inr y =>
    calc
      f (inr x, inr y) = dist x y := candidates_dist_inr fA x y
      _ = dist (α := X oplus Y) (inr x) (inr y) := by
        rw [@Sum.dist_eq X Y]
        rfl
      _ = 1 * dist (α := X oplus Y) (inr x) (inr y) := by ring
      _ <= maxVar X Y * dist (inr x) (inr y) := by gcongr; exact one_le_maxVar X Y

set_option backward.privateInPublic true in
/--
theorem `candidates_lipschitz_aux` / 定理 `candidates_lipschitz_aux`

English:
theorem candidates_lipschitz_aux
  given: (fA : f in candidates X Y)
  proof: calc
    f (x, y) - f (z, t) <= f (x, z) + f (z, t) + f (t, y) - f (z, t) := by
      grind [candidates_triangle]
    _ = f (x, z) + f (t, y) := by simp [sub_eq_add_neg, add_assoc]
    _ <= maxVar X Y * dist x z + maxVar X Y * dist t y := by
      gcongr <;> apply candidates_dist_bound fA
    _ <= m

中文:
定理 candidates_lipschitz_aux
  条件: (fA : f in candidates X Y)
  证明: calc
    f (x, y) - f (z, t) <= f (x, z) + f (z, t) + f (t, y) - f (z, t) := by
      grind [candidates_triangle]
    _ = f (x, z) + f (t, y) := by simp [sub_eq_add_neg, add_assoc]
    _ <= maxVar X Y * dist x z + maxVar X Y * dist t y := by
      gcongr <;> apply candidates_dist_bound fA
    _ <= m
-/
private theorem candidates_lipschitz_aux (fA : f in candidates X Y) :
    f (x, y) - f (z, t) <= 2 * maxVar X Y * dist (x, y) (z, t) :=
  calc
    f (x, y) - f (z, t) <= f (x, z) + f (z, t) + f (t, y) - f (z, t) := by
      grind [candidates_triangle]
    _ = f (x, z) + f (t, y) := by simp [sub_eq_add_neg, add_assoc]
    _ <= maxVar X Y * dist x z + maxVar X Y * dist t y := by
      gcongr <;> apply candidates_dist_bound fA
    _ <= maxVar X Y * max (dist x z) (dist t y) + maxVar X Y * max (dist x z) (dist t y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = 2 * maxVar X Y * max (dist x z) (dist y t) := by
      rw [dist_comm t y]
      ring
    _ = 2 * maxVar X Y * dist (x, y) (z, t) := rfl

set_option backward.privateInPublic true in
/--
theorem `candidates_lipschitz` / 定理 `candidates_lipschitz`

English:
theorem candidates_lipschitz
  given: (fA : f in candidates X Y)
  proof: by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨x, y⟩ ⟨z, t⟩
  rw [Real.dist_eq]; rw [abs_sub_le_iff]
  use candidates_lipschitz_aux fA
  rw [dist_comm]
  exact candidates_lipschitz_aux fA

中文:
定理 candidates_lipschitz
  条件: (fA : f in candidates X Y)
  证明: by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨x, y⟩ ⟨z, t⟩
  rw [Real.dist_eq]; rw [abs_sub_le_iff]
  use candidates_lipschitz_aux fA
  rw [dist_comm]
  exact candidates_lipschitz_aux fA
-/
private theorem candidates_lipschitz (fA : f in candidates X Y) :
    LipschitzWith (2 * maxVar X Y) f := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨x, y⟩ ⟨z, t⟩
  rw [Real.dist_eq]; rw [abs_sub_le_iff]
  use candidates_lipschitz_aux fA
  rw [dist_comm]
  exact candidates_lipschitz_aux fA

/--
theorem `closed_candidatesB` / 定理 `closed_candidatesB`

English:
theorem closed_candidatesB
  statement: IsClosed (candidatesB X Y)
  proof: by
  have I1 : forall x y, IsClosed { f : Cb X Y | f (inl x, inl y) = dist x y } := fun x y =>
    isClosed_eq (continuous_eval_const _) continuous_const
  have I2 : forall x y, IsClosed { f : Cb X Y | f (inr x, inr y) = dist x y } := fun x y =>
    isClosed_eq (continuous_eval_const _) continuous_c

中文:
定理 closed_candidatesB
  结论: 是闭集 (candidatesB X Y)
  证明: by
  have I1 : forall x y, IsClosed { f : Cb X Y | f (inl x, inl y) = dist x y } := fun x y =>
    isClosed_eq (continuous_eval_const _) continuous_const
  have I2 : forall x y, IsClosed { f : Cb X Y | f (inr x, inr y) = dist x y } := fun x y =>
    isClosed_eq (continuous_eval_const _) continuous_c
-/
private theorem closed_candidatesB : IsClosed (candidatesB X Y) := by
  have I1 : forall x y, IsClosed { f : Cb X Y | f (inl x, inl y) = dist x y } := fun x y =>
    isClosed_eq (continuous_eval_const _) continuous_const
  have I2 : forall x y, IsClosed { f : Cb X Y | f (inr x, inr y) = dist x y } := fun x y =>
    isClosed_eq (continuous_eval_const _) continuous_const
  have I3 : forall x y, IsClosed { f : Cb X Y | f (x, y) = f (y, x) } := fun x y =>
    isClosed_eq (continuous_eval_const _) (continuous_eval_const _)
  have I4 : forall x y z, IsClosed { f : Cb X Y | f (x, z) <= f (x, y) + f (y, z) } := fun x y z =>
    isClosed_le (continuous_eval_const _) ((continuous_eval_const _).add (continuous_eval_const _))
  have I5 : forall x, IsClosed { f : Cb X Y | f (x, x) = 0 } := fun x =>
    isClosed_eq (continuous_eval_const _) continuous_const
  have I6 : forall x y, IsClosed { f : Cb X Y | f (x, y) <= maxVar X Y } := fun x y =>
    isClosed_le (continuous_eval_const _) continuous_const
  have : candidatesB X Y = (((((⋂ (x) (y), { f : Cb X Y | f (@inl X Y x, @inl X Y y) = dist x y }) inter
      ⋂ (x) (y), { f : Cb X Y | f (@inr X Y x, @inr X Y y) = dist x y }) inter
      ⋂ (x) (y), { f : Cb X Y | f (x, y) = f (y, x) }) inter
      ⋂ (x) (y) (z), { f : Cb X Y | f (x, z) <= f (x, y) + f (y, z) }) inter
      ⋂ x, { f : Cb X Y | f (x, x) = 0 }) inter
      ⋂ (x) (y), { f : Cb X Y | f (x, y) <= maxVar X Y } := by
    ext
    simp only [candidatesB, candidates, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [this]
  repeat'
    first
      | apply IsClosed.inter _ _
      | apply isClosed_iInter _
      | apply I1 _ _ | apply I2 _ _ | apply I3 _ _ | apply I4 _ _ _ | apply I5 _ | apply I6 _ _
      | intro x

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `HD` / `HD` 的定义

English:
definition HD
  signature: (f : Cb X Y)
  body: max (⨆ x, ⨅ y, f (inl x, inr y)) (⨆ y, ⨅ x, f (inl x, inr y))

中文:
定义 HD
  签名: (f : Cb X Y)
  定义体: max (⨆ x, ⨅ y, f (inl x, inr y)) (⨆ y, ⨅ x, f (inl x, inr y))
-/
def HD (f : Cb X Y) :=
  max (⨆ x, ⨅ y, f (inl x, inr y)) (⨆ y, ⨅ x, f (inl x, inr y))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `HD_below_aux1` / 定理 `HD_below_aux1`

English:
theorem HD_below_aux1
  given: {f : Cb X Y} (C : Real) {x : X}
  proof: let ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  ⟨cf + C, forall_mem_range.2 fun _ => by grw [hcf (mem_range_self _)]⟩

中文:
定理 HD_below_aux1
  条件: {f : Cb X Y} (C : 实数) {x : X}
  证明: let ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  ⟨cf + C, forall_mem_range.2 fun _ => by grw [hcf (mem_range_self _)]⟩

Depends on / 依赖: bddBelow, f.isBounded_range.bddBelow, forall_mem_range, isBounded_range, mem_range_self
-/
theorem HD_below_aux1 {f : Cb X Y} (C : Real) {x : X} :
    BddBelow (range fun y : Y => f (inl x, inr y) + C) :=
  let ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  ⟨cf + C, forall_mem_range.2 fun _ => by grw [hcf (mem_range_self _)]⟩

/--
theorem `HD_bound_aux1` / 定理 `HD_bound_aux1`

English:
theorem HD_bound_aux1
  given: [Nonempty Y] (f : Cb X Y) (C : Real)
  proof: by
  obtain ⟨Cf, hCf⟩ := f.isBounded_range.bddAbove
  refine ⟨Cf + C, forall_mem_range.2 fun x => ?_⟩
  calc
    ⨅ y, f (inl x, inr y) + C <= f (inl x, inr default) + C := ciInf_le (HD_below_aux1 C) default
    _ <= Cf + C := add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl

中文:
定理 HD_bound_aux1
  条件: [非空 Y] (f : Cb X Y) (C : 实数)
  证明: by
  obtain ⟨Cf, hCf⟩ := f.isBounded_range.bddAbove
  refine ⟨Cf + C, forall_mem_range.2 fun x => ?_⟩
  calc
    ⨅ y, f (inl x, inr y) + C <= f (inl x, inr default) + C := ciInf_le (HD_below_aux1 C) default
    _ <= Cf + C := add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl
-/
private theorem HD_bound_aux1 [Nonempty Y] (f : Cb X Y) (C : Real) :
    BddAbove (range fun x : X => ⨅ y, f (inl x, inr y) + C) := by
  obtain ⟨Cf, hCf⟩ := f.isBounded_range.bddAbove
  refine ⟨Cf + C, forall_mem_range.2 fun x => ?_⟩
  calc
    ⨅ y, f (inl x, inr y) + C <= f (inl x, inr default) + C := ciInf_le (HD_below_aux1 C) default
    _ <= Cf + C := add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `HD_below_aux2` / 定理 `HD_below_aux2`

English:
theorem HD_below_aux2
  given: {f : Cb X Y} (C : Real) {y : Y}
  proof: let ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  ⟨cf + C, forall_mem_range.2 fun _ => by grw [hcf (mem_range_self _)]⟩

中文:
定理 HD_below_aux2
  条件: {f : Cb X Y} (C : 实数) {y : Y}
  证明: let ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  ⟨cf + C, forall_mem_range.2 fun _ => by grw [hcf (mem_range_self _)]⟩

Depends on / 依赖: bddBelow, f.isBounded_range.bddBelow, forall_mem_range, isBounded_range, mem_range_self
-/
theorem HD_below_aux2 {f : Cb X Y} (C : Real) {y : Y} :
    BddBelow (range fun x : X => f (inl x, inr y) + C) :=
  let ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  ⟨cf + C, forall_mem_range.2 fun _ => by grw [hcf (mem_range_self _)]⟩

/--
theorem `HD_bound_aux2` / 定理 `HD_bound_aux2`

English:
theorem HD_bound_aux2
  given: [Nonempty X] (f : Cb X Y) (C : Real)
  proof: by
  obtain ⟨Cf, hCf⟩ := f.isBounded_range.bddAbove
  refine ⟨Cf + C, forall_mem_range.2 fun y => ?_⟩
  calc
    ⨅ x, f (inl x, inr y) + C <= f (inl default, inr y) + C := ciInf_le (HD_below_aux2 C) default
    _ <= Cf + C := add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl

中文:
定理 HD_bound_aux2
  条件: [非空 X] (f : Cb X Y) (C : 实数)
  证明: by
  obtain ⟨Cf, hCf⟩ := f.isBounded_range.bddAbove
  refine ⟨Cf + C, forall_mem_range.2 fun y => ?_⟩
  calc
    ⨅ x, f (inl x, inr y) + C <= f (inl default, inr y) + C := ciInf_le (HD_below_aux2 C) default
    _ <= Cf + C := add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl
-/
private theorem HD_bound_aux2 [Nonempty X] (f : Cb X Y) (C : Real) :
    BddAbove (range fun y : Y => ⨅ x, f (inl x, inr y) + C) := by
  obtain ⟨Cf, hCf⟩ := f.isBounded_range.bddAbove
  refine ⟨Cf + C, forall_mem_range.2 fun y => ?_⟩
  calc
    ⨅ x, f (inl x, inr y) + C <= f (inl default, inr y) + C := ciInf_le (HD_below_aux2 C) default
    _ <= Cf + C := add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl

section Nonempty
variable [Nonempty X] [Nonempty Y]

/--
theorem `HD_lipschitz_aux1` / 定理 `HD_lipschitz_aux1`

English:
theorem HD_lipschitz_aux1
  given: (f g : Cb X Y)
  proof: by
  obtain ⟨cg, hcg⟩ := g.isBounded_range.bddBelow
  have Hcg : forall x, cg <= g x := fun x => hcg (mem_range_self x)
  obtain ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  have Hcf : forall x, cf <= f x := fun x => hcf (mem_range_self x)
  -- prove the inequality but with `dist f g` inside, by using 

中文:
定理 HD_lipschitz_aux1
  条件: (f g : Cb X Y)
  证明: by
  obtain ⟨cg, hcg⟩ := g.isBounded_range.bddBelow
  have Hcg : forall x, cg <= g x := fun x => hcg (mem_range_self x)
  obtain ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  have Hcf : forall x, cf <= f x := fun x => hcf (mem_range_self x)
  -- prove the inequality but with `dist f g` inside, by using 
-/
private theorem HD_lipschitz_aux1 (f g : Cb X Y) :
    (⨆ x, ⨅ y, f (inl x, inr y)) <= (⨆ x, ⨅ y, g (inl x, inr y)) + dist f g := by
  obtain ⟨cg, hcg⟩ := g.isBounded_range.bddBelow
  have Hcg : forall x, cg <= g x := fun x => hcg (mem_range_self x)
  obtain ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  have Hcf : forall x, cf <= f x := fun x => hcf (mem_range_self x)
  -- prove the inequality but with `dist f g` inside, by using inequalities comparing
  -- iSup to iSup and iInf to iInf
  have Z : (⨆ x, ⨅ y, f (inl x, inr y)) <= ⨆ x, ⨅ y, g (inl x, inr y) + dist f g :=
    ciSup_mono (HD_bound_aux1 _ (dist f g)) fun x =>
      ciInf_mono ⟨cf, forall_mem_range.2 fun i => Hcf _⟩ fun y => coe_le_coe_add_dist
  -- move the `dist f g` out of the infimum and the supremum, arguing that continuous monotone maps
  -- (here the addition of `dist f g`) preserve infimum and supremum
  have E1 : forall x, (⨅ y, g (inl x, inr y)) + dist f g = ⨅ y, g (inl x, inr y) + dist f g := by
    intro x
    refine Monotone.map_ciInf_of_continuousAt (continuousAt_id.add continuousAt_const) ?_ ?_
    · intro x y hx
      simpa
    · change BddBelow (range fun y : Y => g (inl x, inr y))
      exact ⟨cg, forall_mem_range.2 fun i => Hcg _⟩
  have E2 : (⨆ x, ⨅ y, g (inl x, inr y)) + dist f g = ⨆ x, (⨅ y, g (inl x, inr y)) + dist f g := by
    refine Monotone.map_ciSup_of_continuousAt (continuousAt_id.add continuousAt_const) ?_ ?_
    · intro x y hx
      simpa
    · simpa using HD_bound_aux1 _ 0
  -- deduce the result from the above two steps
  simpa [E2, E1, Function.comp]

/--
theorem `HD_lipschitz_aux2` / 定理 `HD_lipschitz_aux2`

English:
theorem HD_lipschitz_aux2
  given: (f g : Cb X Y)
  proof: by
  obtain ⟨cg, hcg⟩ := g.isBounded_range.bddBelow
  have Hcg : forall x, cg <= g x := fun x => hcg (mem_range_self x)
  obtain ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  have Hcf : forall x, cf <= f x := fun x => hcf (mem_range_self x)
  -- prove the inequality but with `dist f g` inside, by using 

中文:
定理 HD_lipschitz_aux2
  条件: (f g : Cb X Y)
  证明: by
  obtain ⟨cg, hcg⟩ := g.isBounded_range.bddBelow
  have Hcg : forall x, cg <= g x := fun x => hcg (mem_range_self x)
  obtain ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  have Hcf : forall x, cf <= f x := fun x => hcf (mem_range_self x)
  -- prove the inequality but with `dist f g` inside, by using 
-/
private theorem HD_lipschitz_aux2 (f g : Cb X Y) :
    (⨆ y, ⨅ x, f (inl x, inr y)) <= (⨆ y, ⨅ x, g (inl x, inr y)) + dist f g := by
  obtain ⟨cg, hcg⟩ := g.isBounded_range.bddBelow
  have Hcg : forall x, cg <= g x := fun x => hcg (mem_range_self x)
  obtain ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  have Hcf : forall x, cf <= f x := fun x => hcf (mem_range_self x)
  -- prove the inequality but with `dist f g` inside, by using inequalities comparing
  -- iSup to iSup and iInf to iInf
  have Z : (⨆ y, ⨅ x, f (inl x, inr y)) <= ⨆ y, ⨅ x, g (inl x, inr y) + dist f g :=
    ciSup_mono (HD_bound_aux2 _ (dist f g)) fun y =>
      ciInf_mono ⟨cf, forall_mem_range.2 fun i => Hcf _⟩ fun y => coe_le_coe_add_dist
  -- move the `dist f g` out of the infimum and the supremum, arguing that continuous monotone maps
  -- (here the addition of `dist f g`) preserve infimum and supremum
  have E1 : forall y, (⨅ x, g (inl x, inr y)) + dist f g = ⨅ x, g (inl x, inr y) + dist f g := by
    intro y
    refine Monotone.map_ciInf_of_continuousAt (continuousAt_id.add continuousAt_const) ?_ ?_
    · intro x y hx
      simpa
    · change BddBelow (range fun x : X => g (inl x, inr y))
      exact ⟨cg, forall_mem_range.2 fun i => Hcg _⟩
  have E2 : (⨆ y, ⨅ x, g (inl x, inr y)) + dist f g = ⨆ y, (⨅ x, g (inl x, inr y)) + dist f g := by
    refine Monotone.map_ciSup_of_continuousAt (continuousAt_id.add continuousAt_const) ?_ ?_
    · intro x y hx
      simpa
    · simpa using HD_bound_aux2 _ 0
  -- deduce the result from the above two steps
  simpa [E2, E1]

/--
theorem `HD_lipschitz_aux3` / 定理 `HD_lipschitz_aux3`

English:
theorem HD_lipschitz_aux3
  given: (f g : Cb X Y)
  proof: max_le (by grw [HD_lipschitz_aux1 f g, HD, ← le_max_left])
    (by grw [HD_lipschitz_aux2 f g, HD, ← le_max_right])

中文:
定理 HD_lipschitz_aux3
  条件: (f g : Cb X Y)
  证明: max_le (by grw [HD_lipschitz_aux1 f g, HD, ← le_max_left])
    (by grw [HD_lipschitz_aux2 f g, HD, ← le_max_right])
-/
private theorem HD_lipschitz_aux3 (f g : Cb X Y) :
    HD f <= HD g + dist f g :=
  max_le (by grw [HD_lipschitz_aux1 f g, HD, ← le_max_left])
    (by grw [HD_lipschitz_aux2 f g, HD, ← le_max_right])

/--
theorem `HD_continuous` / 定理 `HD_continuous`

English:
theorem HD_continuous
  statement: Continuous (HD : Cb X Y -> Real)
  proof: LipschitzWith.continuous (LipschitzWith.of_le_add HD_lipschitz_aux3)

中文:
定理 HD_continuous
  结论: 连续 (HD : Cb X Y -> 实数)
  证明: LipschitzWith.continuous (LipschitzWith.of_le_add HD_lipschitz_aux3)
-/
private theorem HD_continuous : Continuous (HD : Cb X Y -> Real) :=
  LipschitzWith.continuous (LipschitzWith.of_le_add HD_lipschitz_aux3)

end Nonempty

variable [CompactSpace X] [CompactSpace Y]

/--
theorem `isCompact_candidatesB` / 定理 `isCompact_candidatesB`

English:
theorem isCompact_candidatesB
  statement: IsCompact (candidatesB X Y)
  proof: by
  refine arzela_ascoli₂
      (Icc 0 (maxVar X Y) : Set Real) isCompact_Icc (candidatesB X Y) closed_candidatesB ?_ ?_
  · rintro f ⟨x1, x2⟩ hf
    simp only [Set.mem_Icc]
    exact ⟨candidates_nonneg hf, candidates_le_maxVar hf⟩
  · refine equicontinuous_of_continuity_modulus (fun t => 2 * maxVa

中文:
定理 isCompact_candidatesB
  结论: 是紧集 (candidatesB X Y)
  证明: by
  refine arzela_ascoli₂
      (Icc 0 (maxVar X Y) : Set Real) isCompact_Icc (candidatesB X Y) closed_candidatesB ?_ ?_
  · rintro f ⟨x1, x2⟩ hf
    simp only [Set.mem_Icc]
    exact ⟨candidates_nonneg hf, candidates_le_maxVar hf⟩
  · refine equicontinuous_of_continuity_modulus (fun t => 2 * maxVa
-/
private theorem isCompact_candidatesB : IsCompact (candidatesB X Y) := by
  refine arzela_ascoli₂
      (Icc 0 (maxVar X Y) : Set Real) isCompact_Icc (candidatesB X Y) closed_candidatesB ?_ ?_
  · rintro f ⟨x1, x2⟩ hf
    simp only [Set.mem_Icc]
    exact ⟨candidates_nonneg hf, candidates_le_maxVar hf⟩
  · refine equicontinuous_of_continuity_modulus (fun t => 2 * maxVar X Y * t) ?_ _ ?_
    · have : Tendsto (fun t : Real => 2 * (maxVar X Y : Real) * t) (𝓝 0) (𝓝 (2 * maxVar X Y * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using this
    · rintro x y ⟨f, hf⟩
      exact (candidates_lipschitz hf).dist_le_mul _ _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `candidatesBOfCandidates` / `candidatesBOfCandidates` 的定义

English:
definition candidatesBOfCandidates
  signature: (f : ProdSpaceFun X Y) (fA : f in candidates X Y)
  body: BoundedContinuousFunction.mkOfCompact ⟨f, (candidates_lipschitz fA).continuous⟩

中文:
定义 candidatesBOfCandidates
  签名: (f : ProdSpaceFun X Y) (fA : f in candidates X Y)
  定义体: BoundedContinuousFunction.mkOfCompact ⟨f, (candidates_lipschitz fA).continuous⟩

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.mkOfCompact, candidates_lipschitz, continuous, mkOfCompact
-/
def candidatesBOfCandidates (f : ProdSpaceFun X Y) (fA : f in candidates X Y) : Cb X Y :=
  BoundedContinuousFunction.mkOfCompact ⟨f, (candidates_lipschitz fA).continuous⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `candidatesBOfCandidates_mem` / 定理 `candidatesBOfCandidates_mem`

English:
theorem candidatesBOfCandidates_mem
  given: (f : ProdSpaceFun X Y) (fA : f in candidates X Y)
  proof: fA

中文:
定理 candidatesBOfCandidates_mem
  条件: (f : ProdSpaceFun X Y) (fA : f in candidates X Y)
  证明: fA
-/
theorem candidatesBOfCandidates_mem (f : ProdSpaceFun X Y) (fA : f in candidates X Y) :
    candidatesBOfCandidates f fA in candidatesB X Y :=
  fA

variable [Nonempty X] [Nonempty Y]

set_option backward.privateInPublic true in
/--
theorem `dist_mem_candidates` / 定理 `dist_mem_candidates`

English:
theorem dist_mem_candidates
  proof: by
  simp_rw [candidates, Set.mem_ofPred_eq, dist_comm, dist_triangle, dist_self, maxVar_bound,
    forall_const, and_true]
  exact ⟨fun x y => rfl, fun x y => rfl⟩

中文:
定理 dist_mem_candidates
  证明: by
  simp_rw [candidates, Set.mem_ofPred_eq, dist_comm, dist_triangle, dist_self, maxVar_bound,
    forall_const, and_true]
  exact ⟨fun x y => rfl, fun x y => rfl⟩
-/
private theorem dist_mem_candidates :
    (fun p : (X oplus Y) × (X oplus Y) => dist p.1 p.2) in candidates X Y := by
  simp_rw [candidates, Set.mem_ofPred_eq, dist_comm, dist_triangle, dist_self, maxVar_bound,
    forall_const, and_true]
  exact ⟨fun x y => rfl, fun x y => rfl⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `candidatesBDist` / `candidatesBDist` 的定义

English:
definition candidatesBDist
  signature: (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Nonempty X]
  body: candidatesBOfCandidates _ dist_mem_candidates

中文:
定义 candidatesBDist
  签名: (X : 类型u) (Y : 类型v) [度量空间 X] [紧空间 X] [非空 X]
  定义体: candidatesBOfCandidates _ dist_mem_candidates

Depends on / 依赖: candidatesBOfCandidates, dist_mem_candidates
-/
def candidatesBDist (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] : Cb X Y :=
  candidatesBOfCandidates _ dist_mem_candidates

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `candidatesBDist_mem_candidatesB` / 定理 `candidatesBDist_mem_candidatesB`

English:
theorem candidatesBDist_mem_candidatesB
  proof: candidatesBOfCandidates_mem _ _

中文:
定理 candidatesBDist_mem_candidatesB
  证明: candidatesBOfCandidates_mem _ _

Depends on / 依赖: candidatesBOfCandidates_mem
-/
theorem candidatesBDist_mem_candidatesB :
    candidatesBDist X Y in candidatesB X Y :=
  candidatesBOfCandidates_mem _ _

/--
theorem `candidatesB_nonempty` / 定理 `candidatesB_nonempty`

English:
theorem candidatesB_nonempty
  statement: (candidatesB X Y).Nonempty
  proof: ⟨_, candidatesBDist_mem_candidatesB⟩

中文:
定理 candidatesB_nonempty
  结论: (candidatesB X Y).非空
  证明: ⟨_, candidatesBDist_mem_candidatesB⟩
-/
private theorem candidatesB_nonempty : (candidatesB X Y).Nonempty :=
  ⟨_, candidatesBDist_mem_candidatesB⟩

/--
theorem `HD_candidatesBDist_le` / 定理 `HD_candidatesBDist_le`

English:
theorem HD_candidatesBDist_le
  proof: by
  refine max_le (ciSup_le fun x => ?_) (ciSup_le fun y => ?_)
  · have A : ⨅ y, candidatesBDist X Y (inl x, inr y) <= candidatesBDist X Y (inl x, inr default) :=
      ciInf_le (by simpa using HD_below_aux1 0) default
    have B : dist (inl x) (inr default) <= diam (univ : Set X) + 1 + diam (univ

中文:
定理 HD_candidatesBDist_le
  证明: by
  refine max_le (ciSup_le fun x => ?_) (ciSup_le fun y => ?_)
  · have A : ⨅ y, candidatesBDist X Y (inl x, inr y) <= candidatesBDist X Y (inl x, inr default) :=
      ciInf_le (by simpa using HD_below_aux1 0) default
    have B : dist (inl x) (inr default) <= diam (univ : Set X) + 1 + diam (univ

Depends on / 依赖: HD_below_aux1, candidatesBDist, ciInf_le, ciSup_le, dist_le_diam_of_mem, isBounded_of, max_le
-/
theorem HD_candidatesBDist_le :
    HD (candidatesBDist X Y) <= diam (univ : Set X) + 1 + diam (univ : Set Y) := by
  refine max_le (ciSup_le fun x => ?_) (ciSup_le fun y => ?_)
  · have A : ⨅ y, candidatesBDist X Y (inl x, inr y) <= candidatesBDist X Y (inl x, inr default) :=
      ciInf_le (by simpa using HD_below_aux1 0) default
    have B : dist (inl x) (inr default) <= diam (univ : Set X) + 1 + diam (univ : Set Y) :=
      calc
        dist (inl x) (inr (default : Y)) = dist x (default : X) + 1 + dist default default := rfl
        _ <= diam (univ : Set X) + 1 + diam (univ : Set Y) := by
          gcongr <;>
            exact dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)
    exact le_trans A B
  · have A : ⨅ x, candidatesBDist X Y (inl x, inr y) <= candidatesBDist X Y (inl default, inr y) :=
      ciInf_le (by simpa using HD_below_aux2 0) default
    have B : dist (inl default) (inr y) <= diam (univ : Set X) + 1 + diam (univ : Set Y) :=
      calc
        dist (inl (default : X)) (inr y) = dist default default + 1 + dist default y := rfl
        _ <= diam (univ : Set X) + 1 + diam (univ : Set Y) := by
          gcongr <;>
            exact dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)
    exact le_trans A B

end Constructions

section Consequences

variable (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Y]
  [CompactSpace Y] [Nonempty Y]

/--
theorem `exists_minimizer` / 定理 `exists_minimizer`

English:
theorem exists_minimizer
  statement: exists f in candidatesB X Y, forall g in candidatesB X Y, HD f <= HD g
  proof: isCompact_candidatesB.exists_isMinOn candidatesB_nonempty HD_continuous.continuousOn

中文:
定理 存在_minimizer
  结论: 存在 f in candidatesB X Y, 对任意 g in candidatesB X Y, HD f <= HD g
  证明: isCompact_candidatesB.exists_isMinOn candidatesB_nonempty HD_continuous.continuousOn
-/
private theorem exists_minimizer : exists f in candidatesB X Y, forall g in candidatesB X Y, HD f <= HD g :=
  isCompact_candidatesB.exists_isMinOn candidatesB_nonempty HD_continuous.continuousOn

set_option backward.privateInPublic true in
/--
Definition of `optimalGHDist` / `optimalGHDist` 的定义

English:
definition optimalGHDist
  signature: : Cb X Y
  body: Classical.choose (exists_minimizer X Y)

中文:
定义 optimalGHDist
  签名: : Cb X Y
  定义体: Classical.choose (exists_minimizer X Y)
-/
private def optimalGHDist : Cb X Y :=
  Classical.choose (exists_minimizer X Y)

set_option backward.privateInPublic true in
/--
theorem `optimalGHDist_mem_candidatesB` / 定理 `optimalGHDist_mem_candidatesB`

English:
theorem optimalGHDist_mem_candidatesB
  statement: optimalGHDist X Y in candidatesB X Y
  proof: by
  cases Classical.choose_spec (exists_minimizer X Y)
  assumption

中文:
定理 optimalGHDist_mem_candidatesB
  结论: optimalGHDist X Y in candidatesB X Y
  证明: by
  cases Classical.choose_spec (exists_minimizer X Y)
  assumption
-/
private theorem optimalGHDist_mem_candidatesB : optimalGHDist X Y in candidatesB X Y := by
  cases Classical.choose_spec (exists_minimizer X Y)
  assumption

/--
theorem `HD_optimalGHDist_le` / 定理 `HD_optimalGHDist_le`

English:
theorem HD_optimalGHDist_le
  given: (g : Cb X Y) (hg : g in candidatesB X Y)
  proof: let ⟨_, Z2⟩ := Classical.choose_spec (exists_minimizer X Y)
  Z2 g hg

中文:
定理 HD_optimalGHDist_le
  条件: (g : Cb X Y) (hg : g in candidatesB X Y)
  证明: let ⟨_, Z2⟩ := Classical.choose_spec (exists_minimizer X Y)
  Z2 g hg
-/
private theorem HD_optimalGHDist_le (g : Cb X Y) (hg : g in candidatesB X Y) :
    HD (optimalGHDist X Y) <= HD g :=
  let ⟨_, Z2⟩ := Classical.choose_spec (exists_minimizer X Y)
  Z2 g hg

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- With the optimal candidate, construct a premetric space structure on `X ⊕ Y`, on which the
predistance is given by the candidate. Then, we will identify points at `0` predistance
to obtain a genuine metric space. -/
@[instance_reducible]
/--
Definition of `premetricOptimalGHDist` / `premetricOptimalGHDist` 的定义

English:
definition premetricOptimalGHDist
  signature: : PseudoMetricSpace (X oplus Y) where
  body: optimalGHDist X Y (p, q)
  dist_self _ := candidates_refl (optimalGHDist_mem_candidatesB X Y)
  dist_comm _ _ := candidates_symm (optimalGHDist_mem_candidatesB X Y)
  dist_triangle _ _ _ := candidates_triangle (optimalGHDist_mem_candidatesB X Y)

中文:
定义 premetricOptimalGHDist
  签名: : 伪度量空间 (X oplus Y) where
  定义体: optimalGHDist X Y (p, q)
  dist_self _ := candidates_refl (optimalGHDist_mem_candidatesB X Y)
  dist_comm _ _ := candidates_symm (optimalGHDist_mem_candidatesB X Y)
  dist_triangle _ _ _ := candidates_triangle (optimalGHDist_mem_candidatesB X Y)

Depends on / 依赖: optimalGHDist
-/
def premetricOptimalGHDist : PseudoMetricSpace (X oplus Y) where
  dist p q := optimalGHDist X Y (p, q)
  dist_self _ := candidates_refl (optimalGHDist_mem_candidatesB X Y)
  dist_comm _ _ := candidates_symm (optimalGHDist_mem_candidatesB X Y)
  dist_triangle _ _ _ := candidates_triangle (optimalGHDist_mem_candidatesB X Y)

attribute [local instance] premetricOptimalGHDist

/--
Definition of `OptimalGHCoupling` / `OptimalGHCoupling` 的定义

English:
definition OptimalGHCoupling
  signature: : Type _
  body: @SeparationQuotient (X oplus Y) (premetricOptimalGHDist X Y).toUniformSpace.toTopologicalSpace
deriving MetricSpace

中文:
定义 OptimalGHCoupling
  签名: : 类型 _
  定义体: @SeparationQuotient (X oplus Y) (premetricOptimalGHDist X Y).toUniformSpace.toTopologicalSpace
deriving MetricSpace

Depends on / 依赖: SeparationQuotient, premetricOptimalGHDist, toTopologicalSpace, toUniformSpace, toUniformSpace.toTopologicalSpace
-/
def OptimalGHCoupling : Type _ :=
  @SeparationQuotient (X oplus Y) (premetricOptimalGHDist X Y).toUniformSpace.toTopologicalSpace
deriving MetricSpace

/--
Definition of `optimalGHInjl` / `optimalGHInjl` 的定义

English:
definition optimalGHInjl
  signature: (x : X)
  body: Quotient.mk'' (inl x)

中文:
定义 optimalGHInjl
  签名: (x : X)
  定义体: Quotient.mk'' (inl x)

Depends on / 依赖: Quotient, Quotient.mk
-/
def optimalGHInjl (x : X) : OptimalGHCoupling X Y :=
  Quotient.mk'' (inl x)

/--
theorem `isometry_optimalGHInjl` / 定理 `isometry_optimalGHInjl`

English:
theorem isometry_optimalGHInjl
  statement: Isometry (optimalGHInjl X Y)
  proof: Isometry.of_dist_eq fun _ _ => candidates_dist_inl (optimalGHDist_mem_candidatesB X Y) _ _

中文:
定理 isometry_optimalGHInjl
  结论: 等距 (optimalGHInjl X Y)
  证明: Isometry.of_dist_eq fun _ _ => candidates_dist_inl (optimalGHDist_mem_candidatesB X Y) _ _

Depends on / 依赖: Isometry, Isometry.of_dist_eq, candidates_dist_inl, of_dist_eq, optimalGHDist_mem_candidatesB
-/
theorem isometry_optimalGHInjl : Isometry (optimalGHInjl X Y) :=
  Isometry.of_dist_eq fun _ _ => candidates_dist_inl (optimalGHDist_mem_candidatesB X Y) _ _

/--
Definition of `optimalGHInjr` / `optimalGHInjr` 的定义

English:
definition optimalGHInjr
  signature: (y : Y)
  body: Quotient.mk'' (inr y)

中文:
定义 optimalGHInjr
  签名: (y : Y)
  定义体: Quotient.mk'' (inr y)

Depends on / 依赖: Quotient, Quotient.mk
-/
def optimalGHInjr (y : Y) : OptimalGHCoupling X Y :=
  Quotient.mk'' (inr y)

/--
theorem `isometry_optimalGHInjr` / 定理 `isometry_optimalGHInjr`

English:
theorem isometry_optimalGHInjr
  statement: Isometry (optimalGHInjr X Y)
  proof: Isometry.of_dist_eq fun _ _ => candidates_dist_inr (optimalGHDist_mem_candidatesB X Y) _ _

中文:
定理 isometry_optimalGHInjr
  结论: 等距 (optimalGHInjr X Y)
  证明: Isometry.of_dist_eq fun _ _ => candidates_dist_inr (optimalGHDist_mem_candidatesB X Y) _ _

Depends on / 依赖: Isometry, Isometry.of_dist_eq, candidates_dist_inr, of_dist_eq, optimalGHDist_mem_candidatesB
-/
theorem isometry_optimalGHInjr : Isometry (optimalGHInjr X Y) :=
  Isometry.of_dist_eq fun _ _ => candidates_dist_inr (optimalGHDist_mem_candidatesB X Y) _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `compactSpace_optimalGHCoupling` / 实例 `compactSpace_optimalGHCoupling`

English:
instance compactSpace_optimalGHCoupling
  signature: : CompactSpace (OptimalGHCoupling X Y)
  body: ⟨by
  rw [← range_quotient_mk']
  exact isCompact_range (continuous_sum_dom.2
    ⟨(isometry_optimalGHInjl X Y).continuous, (isometry_optimalGHInjr X Y).continuous⟩)⟩

中文:
实例 compactSpace_optimalGHCoupling
  签名: : 紧空间 (OptimalGHCoupling X Y)
  定义体: ⟨by
  rw [← range_quotient_mk']
  exact isCompact_range (continuous_sum_dom.2
    ⟨(isometry_optimalGHInjl X Y).continuous, (isometry_optimalGHInjr X Y).continuous⟩)⟩

Depends on / 依赖: continuous, continuous_sum_dom, isCompact_range, isometry_optimalGHInjl, isometry_optimalGHInjr, range_quotient_mk
-/
instance compactSpace_optimalGHCoupling : CompactSpace (OptimalGHCoupling X Y) := ⟨by
  rw [← range_quotient_mk']
  exact isCompact_range (continuous_sum_dom.2
    ⟨(isometry_optimalGHInjl X Y).continuous, (isometry_optimalGHInjr X Y).continuous⟩)⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `hausdorffDist_optimal_le_HD` / 定理 `hausdorffDist_optimal_le_HD`

English:
theorem hausdorffDist_optimal_le_HD
  given: {f} (h : f in candidatesB X Y)
  proof: by
  refine le_trans (le_of_forall_gt_imp_ge_of_dense fun r hr => ?_) (HD_optimalGHDist_le X Y f h)
  have A : forall x in range (optimalGHInjl X Y), exists y in range (optimalGHInjr X Y), dist x y <= r := by
    rintro _ ⟨z, rfl⟩
    have I1 : (⨆ x, ⨅ y, optimalGHDist X Y (inl x, inr y)) < r :=
   

中文:
定理 hausdorffDist_optimal_le_HD
  条件: {f} (h : f in candidatesB X Y)
  证明: by
  refine le_trans (le_of_forall_gt_imp_ge_of_dense fun r hr => ?_) (HD_optimalGHDist_le X Y f h)
  have A : forall x in range (optimalGHInjl X Y), exists y in range (optimalGHInjr X Y), dist x y <= r := by
    rintro _ ⟨z, rfl⟩
    have I1 : (⨆ x, ⨅ y, optimalGHDist X Y (inl x, inr y)) < r :=
   

Depends on / 依赖: HD_bound_aux1, HD_optimalGHDist_le, le_csSup, le_max_left, le_of_forall_gt_imp_ge_of_dense, le_trans, lt_of_le_of_lt, mem_range_self, optimalGHDist, optimalGHInjl, optimalGHInjr
-/
theorem hausdorffDist_optimal_le_HD {f} (h : f in candidatesB X Y) :
    hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) <= HD f := by
  refine le_trans (le_of_forall_gt_imp_ge_of_dense fun r hr => ?_) (HD_optimalGHDist_le X Y f h)
  have A : forall x in range (optimalGHInjl X Y), exists y in range (optimalGHInjr X Y), dist x y <= r := by
    rintro _ ⟨z, rfl⟩
    have I1 : (⨆ x, ⨅ y, optimalGHDist X Y (inl x, inr y)) < r :=
      lt_of_le_of_lt (le_max_left _ _) hr
    have I2 :
        ⨅ y, optimalGHDist X Y (inl z, inr y) <= ⨆ x, ⨅ y, optimalGHDist X Y (inl x, inr y) :=
      le_csSup (by simpa using HD_bound_aux1 _ 0) (mem_range_self _)
    have I : ⨅ y, optimalGHDist X Y (inl z, inr y) < r := lt_of_le_of_lt I2 I1
    rcases exists_lt_of_csInf_lt (range_nonempty _) I with ⟨r', ⟨z', rfl⟩, hr'⟩
    exact ⟨optimalGHInjr X Y z', mem_range_self _, le_of_lt hr'⟩
  refine hausdorffDist_le_of_mem_dist ?_ A ?_
  · inhabit X
    rcases A _ (mem_range_self default) with ⟨y, -, hy⟩
    exact le_trans dist_nonneg hy
  · rintro _ ⟨z, rfl⟩
    have I1 : (⨆ y, ⨅ x, optimalGHDist X Y (inl x, inr y)) < r :=
      lt_of_le_of_lt (le_max_right _ _) hr
    have I2 :
        ⨅ x, optimalGHDist X Y (inl x, inr z) <= ⨆ y, ⨅ x, optimalGHDist X Y (inl x, inr y) :=
      le_csSup (by simpa using HD_bound_aux2 _ 0) (mem_range_self _)
    have I : ⨅ x, optimalGHDist X Y (inl x, inr z) < r := lt_of_le_of_lt I2 I1
    rcases exists_lt_of_csInf_lt (range_nonempty _) I with ⟨r', ⟨z', rfl⟩, hr'⟩
    refine ⟨optimalGHInjl X Y z', mem_range_self _, le_of_lt ?_⟩
    rwa [dist_comm]

end Consequences

-- We are done with the construction of the optimal coupling
end GromovHausdorffRealized

end GromovHausdorff
