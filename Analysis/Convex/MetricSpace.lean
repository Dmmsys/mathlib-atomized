/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Mathlib.Geometry.Convex.ConvexSpace.Module

/-!

# Convex spaces with compatible metric structure

A convex space has a compatible metric structure if `dist(∑ tᵢ xᵢ, ∑ tᵢ yᵢ) ≤ ∑ tᵢ dist(xᵢ, yᵢ)`.
This is what one would expect from the triangle inequality.

Note that there is a separate notion of
[convex metric spaces](https://en.wikipedia.org/wiki/Convex_metric_space) in the literature
that has little to do with this definition.

## Main results

- `Convexity.IsConvexDist`: The (`Prop`-valued) class of convex spaces with
  compatible metric structure.
- `Convexity.continuous_convexCombPair`: Binary convex combination is continuous.
- `Convexity.IsConvexDist.of_convex`:
  Convex subspaces of normed spaces are convex metric spaces.

## TODO

- Equip `StdSimplex` with a topology and show the analogous continuity result for n-ary
  convex combinations.
- Tidy up the imports with `Mathlib.Geometric.Convex.ConvexSpace.AffineSpace`.
- Define convex functions with domain a convex space, and redefine `IsConvexDist` as saying that
  `dist : X × X → ℝ` is convex.
-/

public section

namespace Convexity

open ConvexSpace

variable {I X : Type*}

variable (X) in
/--
Definition of `IsConvexDist` / `IsConvexDist` 的定义

English:
class IsConvexDist
  parameters: [inst₁ : ConvexSpace Real X] [inst₂ : MetricSpace X]
  axioms and operations (1):
    - dist_iConvexComb_fst_snd_le([inst₁] [inst₂] (f : StdSimplex Real (X × X))) : dist (f.iConvexComb Prod.fst) (f.iConvexComb Prod.snd) <= f.iConvexComb fun x => dist x.1 x.2

中文:
类 IsConvexDist
  参数: [inst₁ : ConvexSpace 实数 X] [inst₂ : MetricSpace X]
  公理与运算 (1 个):
    - dist_iConvexComb_fst_snd_le([inst₁] [inst₂] (f : StdSimplex 实数 (X × X))) : dist (f.iConvexComb Prod.fst) (f.iConvexComb Prod.snd) <= f.iConvexComb fun x => dist x.1 x.2
-/
class IsConvexDist [inst₁ : ConvexSpace Real X] [inst₂ : MetricSpace X] : Prop where
  /-- Use `dist_iConvexComb_le` instead. -/
  dist_iConvexComb_fst_snd_le [inst₁] [inst₂] (f : StdSimplex Real (X × X)) :
    dist (f.iConvexComb Prod.fst) (f.iConvexComb Prod.snd) <= f.iConvexComb fun x => dist x.1 x.2

@[deprecated (since := "2026-05-15")] alias IsConvexMetricSpace := IsConvexDist

variable [ConvexSpace Real X] [MetricSpace X] [IsConvexDist X]

/--
lemma `dist_iConvexComb_le` / 引理 `dist_iConvexComb_le`

English:
lemma dist_iConvexComb_le
  given: {ι : Type*} (f : StdSimplex Real ι) (x y : ι -> X)
  proof: by
  simpa [iConvexComb_map, Finsupp.sum_mapDomain_index, add_mul]
    using IsConvexDist.dist_iConvexComb_fst_snd_le (f.map fun i => (x i, y i))

@[deprecated (since := "2026-05-15")] alias dist_convexCombination_right_le := dist_iConvexComb_le

中文:
引理 dist_iConvexComb_le
  条件: {ι : 类型} (f : StdSimplex 实数 ι) (x y : ι -> X)
  证明: by
  simpa [iConvexComb_map, Finsupp.sum_mapDomain_index, add_mul]
    using IsConvexDist.dist_iConvexComb_fst_snd_le (f.map fun i => (x i, y i))

@[deprecated (since := "2026-05-15")] alias dist_convexCombination_right_le := dist_iConvexComb_le

Depends on / 依赖: Finsupp, Finsupp.sum_mapDomain_index, IsConvexDist, IsConvexDist.dist_iConvexComb_fst_snd_le, add_mul, dist_iConvexComb_fst_snd_le, f.map, iConvexComb_map, sum_mapDomain_index
-/
lemma dist_iConvexComb_le {ι : Type*} (f : StdSimplex Real ι) (x y : ι -> X) :
    dist (f.iConvexComb x) (f.iConvexComb y) <= f.iConvexComb fun i => dist (x i) (y i) := by
  simpa [iConvexComb_map, Finsupp.sum_mapDomain_index, add_mul]
    using IsConvexDist.dist_iConvexComb_fst_snd_le (f.map fun i => (x i, y i))

@[deprecated (since := "2026-05-15")] alias dist_convexCombination_right_le := dist_iConvexComb_le

/--
lemma `dist_iConvexComb_left_le` / 引理 `dist_iConvexComb_left_le`

English:
lemma dist_iConvexComb_left_le
  given: (f : StdSimplex Real I) (g : I -> X) (x : X)
  proof: by
  simpa using dist_iConvexComb_le f g (fun _ => x)

中文:
引理 dist_iConvexComb_left_le
  条件: (f : StdSimplex 实数 I) (g : I -> X) (x : X)
  证明: by
  simpa using dist_iConvexComb_le f g (fun _ => x)

Depends on / 依赖: dist_iConvexComb_le
-/
lemma dist_iConvexComb_left_le (f : StdSimplex Real I) (g : I -> X) (x : X) :
    dist (f.iConvexComb g) x <= f.iConvexComb fun i => dist (g i) x := by
  simpa using dist_iConvexComb_le f g (fun _ => x)

/--
lemma `dist_iConvexComb_right_le` / 引理 `dist_iConvexComb_right_le`

English:
lemma dist_iConvexComb_right_le
  given: (x : X) (f : StdSimplex Real I) (g : I -> X)
  proof: by
  simpa using dist_iConvexComb_le f (fun _ => x) g

中文:
引理 dist_iConvexComb_right_le
  条件: (x : X) (f : StdSimplex 实数 I) (g : I -> X)
  证明: by
  simpa using dist_iConvexComb_le f (fun _ => x) g

Depends on / 依赖: dist_iConvexComb_le
-/
lemma dist_iConvexComb_right_le (x : X) (f : StdSimplex Real I) (g : I -> X) :
    dist x (f.iConvexComb g) <= f.iConvexComb fun i => dist x (g i) := by
  simpa using dist_iConvexComb_le f (fun _ => x) g

/--
lemma `dist_sConvexComb_left_le` / 引理 `dist_sConvexComb_left_le`

English:
lemma dist_sConvexComb_left_le
  given: (f : StdSimplex Real X) (x : X)
  proof: by
  simpa using dist_iConvexComb_left_le f id x

中文:
引理 dist_sConvexComb_left_le
  条件: (f : StdSimplex 实数 X) (x : X)
  证明: by
  simpa using dist_iConvexComb_left_le f id x

Depends on / 依赖: dist_iConvexComb_left_le
-/
lemma dist_sConvexComb_left_le (f : StdSimplex Real X) (x : X) :
    dist f.sConvexComb x <= f.iConvexComb (dist · x) := by
  simpa using dist_iConvexComb_left_le f id x

/--
lemma `dist_sConvexComb_right_le` / 引理 `dist_sConvexComb_right_le`

English:
lemma dist_sConvexComb_right_le
  given: (x : X) (f : StdSimplex Real X)
  proof: by
  simpa using dist_iConvexComb_right_le x f id

@[simp]

中文:
引理 dist_sConvexComb_right_le
  条件: (x : X) (f : StdSimplex 实数 X)
  证明: by
  simpa using dist_iConvexComb_right_le x f id

@[simp]

Depends on / 依赖: dist_iConvexComb_right_le
-/
lemma dist_sConvexComb_right_le (x : X) (f : StdSimplex Real X) :
    dist x f.sConvexComb <= f.iConvexComb (dist x) := by
  simpa using dist_iConvexComb_right_le x f id

@[simp]
/--
lemma `dist_convexCombPair_left` / 引理 `dist_convexCombPair_left`

English:
lemma dist_convexCombPair_left
  proof: by
  classical
  suffices H : forall {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : X),
      dist (convexCombPair s t hs ht h x y) x <= t * dist x y by
    refine (H ..).antisymm ?_
    conv_lhs => rw [eq_sub_iff_add_eq'.mpr h, sub_mul, one_mul]
    grw [sub_le_iff_le_add, dist_com

中文:
引理 dist_convexCombPair_left
  证明: by
  classical
  suffices H : forall {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : X),
      dist (convexCombPair s t hs ht h x y) x <= t * dist x y by
    refine (H ..).antisymm ?_
    conv_lhs => rw [eq_sub_iff_add_eq'.mpr h, sub_mul, one_mul]
    grw [sub_le_iff_le_add, dist_com

Depends on / 依赖: Finsupp, Finsupp.sum_add_index, add_comm, antisymm, classical, conv_lhs, convexCombPair, convexCombPair_symm, dist_comm, dist_sConvexComb_left_le, dist_triangle_left, eq_sub_iff_add_eq, iConvexComb_eq_sum, one_mul, sub_le_iff_le_add, sub_mul, sum_add_index
-/
lemma dist_convexCombPair_left
    {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : X) :
    dist (convexCombPair s t hs ht h x y) x = t * dist x y := by
  classical
  suffices H : forall {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : X),
      dist (convexCombPair s t hs ht h x y) x <= t * dist x y by
    refine (H ..).antisymm ?_
    conv_lhs => rw [eq_sub_iff_add_eq'.mpr h, sub_mul, one_mul]
    grw [sub_le_iff_le_add, dist_comm x y, ← H ht hs ((add_comm _ _).trans h) y x, dist_comm,
      convexCombPair_symm, ← dist_triangle_left]
  intro s t hs ht h x y
  grw [convexCombPair, dist_sConvexComb_left_le]
  simp [iConvexComb_eq_sum, Finsupp.sum_add_index, add_mul, dist_comm y x]

@[simp]
/--
lemma `dist_convexCombPair_right` / 引理 `dist_convexCombPair_right`

English:
lemma dist_convexCombPair_right
  proof: by
  rw [convexCombPair_symm]; rw [dist_convexCombPair_left]; rw [dist_comm]

@[simp]

中文:
引理 dist_convexCombPair_right
  证明: by
  rw [convexCombPair_symm]; rw [dist_convexCombPair_left]; rw [dist_comm]

@[simp]

Depends on / 依赖: convexCombPair_symm, dist_comm, dist_convexCombPair_left
-/
lemma dist_convexCombPair_right
    {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : X) :
    dist (convexCombPair s t hs ht h x y) y = s * dist x y := by
  rw [convexCombPair_symm]; rw [dist_convexCombPair_left]; rw [dist_comm]

@[simp]
/--
lemma `dist_left_convexCombPair` / 引理 `dist_left_convexCombPair`

English:
lemma dist_left_convexCombPair
  proof: by
  rw [dist_comm]; rw [dist_convexCombPair_left]

@[simp]

中文:
引理 dist_left_convexCombPair
  证明: by
  rw [dist_comm]; rw [dist_convexCombPair_left]

@[simp]

Depends on / 依赖: dist_comm, dist_convexCombPair_left
-/
lemma dist_left_convexCombPair
    {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : X) :
    dist x (convexCombPair s t hs ht h x y) = t * dist x y := by
  rw [dist_comm]; rw [dist_convexCombPair_left]

@[simp]
/--
lemma `dist_right_convexCombPair` / 引理 `dist_right_convexCombPair`

English:
lemma dist_right_convexCombPair
  proof: by
  rw [dist_comm]; rw [dist_convexCombPair_right]

中文:
引理 dist_right_convexCombPair
  证明: by
  rw [dist_comm]; rw [dist_convexCombPair_right]

Depends on / 依赖: dist_comm, dist_convexCombPair_right
-/
lemma dist_right_convexCombPair
    {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : X) :
    dist y (convexCombPair s t hs ht h x y) = s * dist x y := by
  rw [dist_comm]; rw [dist_convexCombPair_right]

/--
lemma `dist_convexCombPair_convexCombPair` / 引理 `dist_convexCombPair_convexCombPair`

English:
lemma dist_convexCombPair_convexCombPair
  proof: by
  wlog hss' : s' <= s generalizing s t s' t'
  · rw [dist_comm, this, abs_sub_comm]; exact le_of_not_ge hss'
  suffices dist (convexCombPair s t hs ht h x y) (convexCombPair s' t' hs' ht' h' x y) <=
      |s - s'| * dist x y by
    refine this.antisymm ?_
    nth_grw 2 [← abs_dist_sub_le (z := x)

中文:
引理 dist_convexCombPair_convexCombPair
  证明: by
  wlog hss' : s' <= s generalizing s t s' t'
  · rw [dist_comm, this, abs_sub_comm]; exact le_of_not_ge hss'
  suffices dist (convexCombPair s t hs ht h x y) (convexCombPair s' t' hs' ht' h' x y) <=
      |s - s'| * dist x y by
    refine this.antisymm ?_
    nth_grw 2 [← abs_dist_sub_le (z := x)

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite.sym, StdSimplex, abs_dist_sub_le, abs_sub_comm, antisymm, convexCombPair, dist_comm, eq_sub_iff_add_eq, eq_sub_iff_add_eq.mpr, equivFunOnFinite, generalizing, le_of_not_ge, nth_grw, sub_mul, this.antisymm, weights
-/
lemma dist_convexCombPair_convexCombPair
    {s t s' t' : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1)
    (hs' : 0 <= s') (ht' : 0 <= t') (h' : s' + t' = 1) (x y : X) :
    dist (convexCombPair s t hs ht h x y) (convexCombPair s' t' hs' ht' h' x y) =
      |s - s'| * dist x y := by
  wlog hss' : s' <= s generalizing s t s' t'
  · rw [dist_comm, this, abs_sub_comm]; exact le_of_not_ge hss'
  suffices dist (convexCombPair s t hs ht h x y) (convexCombPair s' t' hs' ht' h' x y) <=
      |s - s'| * dist x y by
    refine this.antisymm ?_
    nth_grw 2 [← abs_dist_sub_le (z := x)]
    have : |t - t'| = |s - s'| := by
      rw [eq_sub_iff_add_eq.mpr h]; rw [eq_sub_iff_add_eq.mpr h']; simp [abs_sub_comm t t']
    simp [← sub_mul, this]
  let f : StdSimplex Real (Fin 3) :=
  { weights := Finsupp.equivFunOnFinite.symm ![s', s - s', t]
    nonneg i := by fin_cases i <;> simp [*]
    total := by simp [Finsupp.sum_fintype, Fin.sum_univ_succ, ← add_assoc, h] }
  convert dist_iConvexComb_le f ![x, x, y] ![x, y, y] using 1
  swap; · simp [Finsupp.sum_fintype, Fin.sum_univ_succ, f, hss', iConvexComb_eq_sum]
  congr 1
  · delta convexCombPair
    congr 1
    ext a
    simp [StdSimplex.duple, StdSimplex.map, Finsupp.mapDomain,
      Finsupp.sum_fintype, Fin.sum_univ_succ, f, ← add_assoc]
  · delta convexCombPair
    congr 1
    ext a
    simp [StdSimplex.duple, StdSimplex.map, Finsupp.mapDomain,
      Finsupp.sum_fintype, Fin.sum_univ_succ, f, show t' = s - s' + t by grind]

/--
lemma `dist_convexCombPair_convexCombPair_le` / 引理 `dist_convexCombPair_convexCombPair_le`

English:
lemma dist_convexCombPair_convexCombPair_le
  proof: by
  convert dist_iConvexComb_le (.duple (M := Fin 2) 0 1 hs ht h) ![x, y] ![x', y']
  · simp [convexCombPair_def]
  · simp [convexCombPair_def]
  · simp [Finsupp.sum_fintype, Fin.sum_univ_succ, StdSimplex.duple, iConvexComb_eq_sum]

中文:
引理 dist_convexCombPair_convexCombPair_le
  证明: by
  convert dist_iConvexComb_le (.duple (M := Fin 2) 0 1 hs ht h) ![x, y] ![x', y']
  · simp [convexCombPair_def]
  · simp [convexCombPair_def]
  · simp [Finsupp.sum_fintype, Fin.sum_univ_succ, StdSimplex.duple, iConvexComb_eq_sum]

Depends on / 依赖: Fin.sum_univ_succ, Finsupp, Finsupp.sum_fintype, StdSimplex, StdSimplex.duple, convert, convexCombPair_def, dist_iConvexComb_le, iConvexComb_eq_sum, sum_fintype, sum_univ_succ
-/
lemma dist_convexCombPair_convexCombPair_le
    {s t : Real} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y x' y' : X) :
    dist (convexCombPair s t hs ht h x y) (convexCombPair s t hs ht h x' y') <=
      s * dist x x' + t * dist y y' := by
  convert dist_iConvexComb_le (.duple (M := Fin 2) 0 1 hs ht h) ![x, y] ![x', y']
  · simp [convexCombPair_def]
  · simp [convexCombPair_def]
  · simp [Finsupp.sum_fintype, Fin.sum_univ_succ, StdSimplex.duple, iConvexComb_eq_sum]

/--
lemma `continuous_convexCombPair` / 引理 `continuous_convexCombPair`

English:
lemma continuous_convexCombPair
  proof: by
  apply continuous_prod_of_continuous_lipschitzWith' (K := 1)
  · intro i x y
    simp only [← coe_nnreal_ennreal_nndist, ENNReal.coe_one, one_mul, ENNReal.coe_le_coe,
      NNReal.toReal_le, coe_nndist]
    grw [dist_convexCombPair_convexCombPair_le, Prod.dist_eq]
    nth_grw 1 [le_max_left (dis

中文:
引理 continuous_convexCombPair
  证明: by
  apply continuous_prod_of_continuous_lipschitzWith' (K := 1)
  · intro i x y
    simp only [← coe_nnreal_ennreal_nndist, ENNReal.coe_one, one_mul, ENNReal.coe_le_coe,
      NNReal.toReal_le, coe_nndist]
    grw [dist_convexCombPair_convexCombPair_le, Prod.dist_eq]
    nth_grw 1 [le_max_left (dis
-/
lemma continuous_convexCombPair :
    Continuous fun x : Set.Icc (0 : Real) 1 × (X × X) => convexCombPair (R := Real)
      ↑x.1 (1 - ↑x.1) x.1.prop.left (by simpa using x.1.prop.right) (add_sub_cancel ..)
      x.2.1 x.2.2 := by
  apply continuous_prod_of_continuous_lipschitzWith' (K := 1)
  · intro i x y
    simp only [← coe_nnreal_ennreal_nndist, ENNReal.coe_one, one_mul, ENNReal.coe_le_coe,
      NNReal.toReal_le, coe_nndist]
    grw [dist_convexCombPair_convexCombPair_le, Prod.dist_eq]
    nth_grw 1 [le_max_left (dist x.1 y.1) (dist x.2 y.2)]
    swap; · simpa using i.prop.left
    nth_grw 2 [le_max_right (dist x.1 y.1) (dist x.2 y.2)]
    swap; · simpa using i.prop.right
    rw [← add_mul]; rw [add_sub_cancel]; rw [one_mul]
  · intro b
    refine LipschitzWith.continuous (K := nndist b.1 b.2) fun x y => ?_
    rw [mul_comm]
    simp [← coe_nnreal_ennreal_nndist, ← ENNReal.coe_mul, NNReal.toReal_le,
      dist_convexCombPair_convexCombPair, Subtype.dist_eq, dist_eq_norm]

@[deprecated (since := "2026-05-15")] alias continuous_convexComboPair := continuous_convexCombPair

/--
lemma `continuous_convexCombPair_of_isBounded` / 引理 `continuous_convexCombPair_of_isBounded`

English:
lemma continuous_convexCombPair_of_isBounded
  proof: by
  obtain ⟨D, hD, hD'⟩ := ((Metric.isBounded_iff_eventually.mp (hx'.union hy')).and
    (Filter.eventually_gt_atTop 0)).exists
  replace hD := fun t₁ t₂ => hD (.inl (Set.mem_range_self t₁)) (.inr (Set.mem_range_self t₂))
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : f t in Set.Ioo 0

中文:
引理 continuous_convexCombPair_of_isBounded
  证明: by
  obtain ⟨D, hD, hD'⟩ := ((Metric.isBounded_iff_eventually.mp (hx'.union hy')).and
    (Filter.eventually_gt_atTop 0)).exists
  replace hD := fun t₁ t₂ => hD (.inl (Set.mem_range_self t₁)) (.inr (Set.mem_range_self t₂))
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : f t in Set.Ioo 0

Depends on / 依赖: Filter, Filter.eventually_gt_atTop, Ioo_subset_Icc_self, Metric, Metric.isBounded_iff_eventually.mp, Set.Ioo, Set.Ioo_subset_Icc_self, Set.mem_range_self, continuousAt_iff, continuous_convexCombPair, continuous_iff_continuousAt, eventually_gt_atTop, isBounded_iff_eventually, isOpenEmbedding_subtypeVal, isOpenEmbedding_subtypeVal.continuousAt_iff, isOpen_Ioo, isOpen_Ioo.preimage, mem_range_self, preimage, replace
-/
lemma continuous_convexCombPair_of_isBounded
    {T : Type*} [TopologicalSpace T] (f : T -> Real) (hf : Continuous f)
    (hf0 : forall t, 0 <= f t) (hf1 : forall t, f t <= 1) (x y : T -> X)
    (hx : ContinuousOn x (f ⁻¹' {0}ᶜ)) (hy : ContinuousOn y (f ⁻¹' {1}ᶜ))
    (hx' : Bornology.IsBounded (Set.range x)) (hy' : Bornology.IsBounded (Set.range y)) :
    Continuous fun i => convexCombPair (f i) (1 - f i) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x i) (y i) := by
  obtain ⟨D, hD, hD'⟩ := ((Metric.isBounded_iff_eventually.mp (hx'.union hy')).and
    (Filter.eventually_gt_atTop 0)).exists
  replace hD := fun t₁ t₂ => hD (.inl (Set.mem_range_self t₁)) (.inr (Set.mem_range_self t₂))
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : f t in Set.Ioo 0 1
  · exact ((isOpen_Ioo.preimage hf).isOpenEmbedding_subtypeVal.continuousAt_iff
      (x := ⟨t, ht⟩)).mp ((continuous_convexCombPair (X := X)).comp₃ (W := f ⁻¹' Set.Ioo 0 1)
      (e := fun i => ⟨f i, Set.Ioo_subset_Icc_self i.prop⟩) (f := x ∘ (↑)) (k := y ∘ (↑))
      (by fun_prop) (hx.comp_continuous continuous_subtype_val (by simp_all; grind))
      (hy.comp_continuous continuous_subtype_val (by simp_all; grind))).continuousAt
  obtain ht | ht : f t = 0 ∨ f t = 1 := by
    simpa [le_antisymm_iff, hf0, hf1, -not_and, not_and_or] using ht
  · simp only [ContinuousAt, ht, sub_zero, convexCombPair_zero]
    rw [Metric.nhds_basis_ball.tendsto_right_iff]
    intro r hr
    filter_upwards [hy.continuousAt ((hf.isOpen_preimage _ isClosed_singleton.isOpen_compl).mem_nhds
      (x := t) (by simp [*])) (Metric.ball_mem_nhds _ (show 0 < r / 3 by simpa)),
      hf.tendsto' _ _ ht (Metric.ball_mem_nhds _ (show 0 < r / D / 3 by simp [*]))] with j hj hj'
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hj hj' ⊢
    grw [dist_triangle _ (convexCombPair (f j) (1 - f j) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x j) (y t)), dist_convexCombPair_convexCombPair_le]
    simp only [dist_self, mul_zero, zero_add, dist_convexCombPair_right]
    grw [sub_le_self _ (hf0 _), hj, hD, (le_abs_self _).trans hj'.le]
    · field_simp; norm_num
    · exact hf0 _
  · simp only [ContinuousAt, ht, sub_self, convexCombPair_one]
    rw [Metric.nhds_basis_ball.tendsto_right_iff]
    intro r hr
    filter_upwards [hx.continuousAt ((hf.isOpen_preimage _ isClosed_singleton.isOpen_compl).mem_nhds
      (x := t) (by simp [*])) (Metric.ball_mem_nhds _ (show 0 < r / 3 by simpa)),
      hf.tendsto' _ _ ht (Metric.ball_mem_nhds _ (show 0 < r / D / 3 by simp [*]))] with j hj hj'
    simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hj hj' ⊢
    grw [dist_triangle _ (convexCombPair (f j) (1 - f j) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x t) (y j)), dist_convexCombPair_convexCombPair_le]
    simp only [dist_self, mul_zero, add_zero, dist_convexCombPair_left]
    grw [abs_sub_comm, ← le_abs_self] at hj'
    grw [hj.le, hj'.le, hf1, hD]
    · field_simp; norm_num
    · exact hf0 _

/--
lemma `continuous_convexCombPair'` / 引理 `continuous_convexCombPair'`

English:
lemma continuous_convexCombPair'
  statement: [BoundedSpace X]
  proof: continuous_convexCombPair_of_isBounded f hf hf0 hf1 x y hx hy (.all _) (.all _)

@[deprecated (since := "2026-05-15")]
alias continuous_convexComboPair' := continuous_convexCombPair'

中文:
引理 continuous_convexCombPair'
  结论: [BoundedSpace X]
  证明: continuous_convexCombPair_of_isBounded f hf hf0 hf1 x y hx hy (.all _) (.all _)

@[deprecated (since := "2026-05-15")]
alias continuous_convexComboPair' := continuous_convexCombPair'

Depends on / 依赖: continuous_convexCombPair_of_isBounded
-/
lemma continuous_convexCombPair' [BoundedSpace X]
    {T : Type*} [TopologicalSpace T] (f : T -> Real) (hf : Continuous f)
    (hf0 : forall t, 0 <= f t) (hf1 : forall t, f t <= 1) (x y : T -> X)
    (hx : ContinuousOn x (f ⁻¹' {0}ᶜ)) (hy : ContinuousOn y (f ⁻¹' {1}ᶜ)) :
    Continuous fun i => convexCombPair (f i) (1 - f i) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x i) (y i) :=
  continuous_convexCombPair_of_isBounded f hf hf0 hf1 x y hx hy (.all _) (.all _)

@[deprecated (since := "2026-05-15")]
alias continuous_convexComboPair' := continuous_convexCombPair'

attribute [local instance] AddTorsor.toConvexSpace in
instance (priority := low) {V P : Type*}
    [NormedAddCommGroup V] [NormedSpace Real V] [MetricSpace P] [NormedAddTorsor V P] :
    IsConvexDist P where
  dist_iConvexComb_fst_snd_le f := by
    let p : P := Nonempty.some inferInstance
    simp only [AddTorsor.iConvexComb_eq_affineCombination]
    rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ f.total p]; rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ f.total p]
    suffices ‖f.weights.sum fun a b => b • (a.1 -ᵥ a.2)‖ <=
      f.weights.sum fun a b => b * ‖a.1 -ᵥ a.2‖ by
      simpa [dist_eq_norm_vsub, Finsupp.sum, ← Finset.sum_sub_distrib, ← smul_sub]
    grw [Finsupp.sum, Finsupp.sum, norm_sum_le]
    simp [norm_smul, abs_eq_self.mpr (f.nonneg _)]

/--
Instance `IsConvexDist.subtype` / 实例 `IsConvexDist.subtype`

English:
instance IsConvexDist.subtype
  signature: (s : Set X) (hs : IsConvexSet Real s)
  body: .subtype s hs
    IsConvexDist s := by
  let : ConvexSpace Real s := .subtype s hs
  refine ⟨fun f => ?_⟩
  convert dist_iConvexComb_fst_snd_le (X := X) (f.map fun x => (x.1, x.2)) <;>
    simp [Subtype.dist_eq, Finsupp.sum_mapDomain_index, add_mul]

中文:
实例 IsConvexDist.subtype
  签名: (s : Set X) (hs : IsConvexSet 实数 s)
  定义体: .subtype s hs
    IsConvexDist s := by
  let : ConvexSpace Real s := .subtype s hs
  refine ⟨fun f => ?_⟩
  convert dist_iConvexComb_fst_snd_le (X := X) (f.map fun x => (x.1, x.2)) <;>
    simp [Subtype.dist_eq, Finsupp.sum_mapDomain_index, add_mul]

Depends on / 依赖: subtype
-/
instance IsConvexDist.subtype (s : Set X) (hs : IsConvexSet Real s) :
    letI : ConvexSpace Real s := .subtype s hs
    IsConvexDist s := by
  let : ConvexSpace Real s := .subtype s hs
  refine ⟨fun f => ?_⟩
  convert dist_iConvexComb_fst_snd_le (X := X) (f.map fun x => (x.1, x.2)) <;>
    simp [Subtype.dist_eq, Finsupp.sum_mapDomain_index, add_mul]

/--
Instance `IsConvexDist.submodule` / 实例 `IsConvexDist.submodule`

English:
instance IsConvexDist.submodule
  signature: {F M : Type*} [AddCommGroup M] [MetricSpace M]
  body: .subtype _ _

中文:
实例 IsConvexDist.submodule
  签名: {F M : 类型} [AddCommGroup M] [MetricSpace M]
  定义体: .subtype _ _

Depends on / 依赖: subtype
-/
instance IsConvexDist.submodule {F M : Type*} [AddCommGroup M] [MetricSpace M]
    [Module Real M] [ConvexSpace Real M] [IsModuleConvexSpace Real M] [IsConvexDist M]
    [SetLike F M] [AddSubmonoidClass F M] [SMulMemClass F Real M] {S : F} :
    IsConvexDist S := .subtype _ _

end Convexity
