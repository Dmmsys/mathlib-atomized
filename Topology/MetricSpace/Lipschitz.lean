/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.Bornology.Hom
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.
Finally, `f : α → β` is called *locally Lipschitz continuous* if each `x : α` has a neighbourhood
on which `f` is Lipschitz continuous (with some constant).

In this file we specialize various facts about Lipschitz continuous maps
to the case of (pseudo) metric spaces.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `LipschitzWith (Real.toNNReal K) f`.
-/

@[expose] public section

assert_not_exists Module.Basis Ideal ContinuousMul

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

/--
theorem `lipschitzWith_iff_dist_le_mul` / 定理 `lipschitzWith_iff_dist_le_mul`

English:
theorem lipschitzWith_iff_dist_le_mul
  statement: [PseudoMetricSpace α] [PseudoMetricSpace β] {K : Real>=0}
  proof: by
  simp only [LipschitzWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzWith.dist_le_mul, LipschitzWith.of_dist_le_mul⟩ := lipschitzWith_iff_dist_le_mul

中文:
定理 lipschitzWith_iff_dist_le_mul
  结论: [伪度量空间 α] [伪度量空间 β] {K : 实数>=0}
  证明: by
  simp only [LipschitzWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzWith.dist_le_mul, LipschitzWith.of_dist_le_mul⟩ := lipschitzWith_iff_dist_le_mul

Depends on / 依赖: LipschitzWith, dist_nndist, edist_nndist
-/
theorem lipschitzWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : Real>=0}
    {f : α -> β} : LipschitzWith K f ↔ forall x y, dist (f x) (f y) <= K * dist x y := by
  simp only [LipschitzWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzWith.dist_le_mul, LipschitzWith.of_dist_le_mul⟩ := lipschitzWith_iff_dist_le_mul

/--
theorem `lipschitzOnWith_iff_dist_le_mul` / 定理 `lipschitzOnWith_iff_dist_le_mul`

English:
theorem lipschitzOnWith_iff_dist_le_mul
  statement: [PseudoMetricSpace α] [PseudoMetricSpace β] {K : Real>=0}
  proof: by
  simp only [LipschitzOnWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzOnWith.dist_le_mul, LipschitzOnWith.of_dist_le_mul⟩ :=
  lipschitzOnWith_iff_dist_le_mul

中文:
定理 lipschitzOnWith_iff_dist_le_mul
  结论: [伪度量空间 α] [伪度量空间 β] {K : 实数>=0}
  证明: by
  simp only [LipschitzOnWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzOnWith.dist_le_mul, LipschitzOnWith.of_dist_le_mul⟩ :=
  lipschitzOnWith_iff_dist_le_mul

Depends on / 依赖: LipschitzOnWith, dist_nndist, edist_nndist
-/
theorem lipschitzOnWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : Real>=0}
    {s : Set α} {f : α -> β} :
    LipschitzOnWith K f s ↔ forall x in s, forall y in s, dist (f x) (f y) <= K * dist x y := by
  simp only [LipschitzOnWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzOnWith.dist_le_mul, LipschitzOnWith.of_dist_le_mul⟩ :=
  lipschitzOnWith_iff_dist_le_mul

namespace LipschitzWith

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ] {K : Real>=0} {f : α -> β}
  {x y : α} {r : Real}

/--
theorem `of_dist_le'` / 定理 `of_dist_le'`

English:
theorem of_dist_le'
  given: {K : Real} (h : forall x y, dist (f x) (f y) <= K * dist x y)
  proof: of_dist_le_mul fun x y =>
le_trans (h x y) by gcongr; apply Real.le_coe_toNNReal

中文:
定理 of_dist_le'
  条件: {K : 实数} (h : 对任意 x y, dist (f x) (f y) <= K * dist x y)
  证明: of_dist_le_mul fun x y =>
le_trans (h x y) by gcongr; apply Real.le_coe_toNNReal
-/
protected theorem of_dist_le' {K : Real} (h : forall x y, dist (f x) (f y) <= K * dist x y) :
    LipschitzWith (Real.toNNReal K) f :=
  of_dist_le_mul fun x y =>
le_trans (h x y) by gcongr; apply Real.le_coe_toNNReal

/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  given: (h : forall x y, dist (f x) (f y) <= dist x y)
  statement: LipschitzWith 1 f
  proof: of_dist_le_mul by simpa only [NNReal.coe_one, one_mul] using h

中文:
定理 mk_one
  条件: (h : 对任意 x y, dist (f x) (f y) <= dist x y)
  结论: LipschitzWith 1 f
  证明: of_dist_le_mul by simpa only [NNReal.coe_one, one_mul] using h
-/
protected theorem mk_one (h : forall x y, dist (f x) (f y) <= dist x y) : LipschitzWith 1 f :=
of_dist_le_mul by simpa only [NNReal.coe_one, one_mul] using h

/--
theorem `of_le_add_mul'` / 定理 `of_le_add_mul'`

English:
theorem of_le_add_mul'
  given: {f : α -> Real} (K : Real) (h : forall x y, f x <= f y + K * dist x y)
  proof: have I : forall x y, f x - f y <= K * dist x y := fun x y => sub_le_iff_le_add'.2 (h x y)
  LipschitzWith.of_dist_le' fun x y => abs_sub_le_iff.2 ⟨I x y, dist_comm y x ▸ I y x⟩

中文:
定理 of_le_add_mul'
  条件: {f : α -> 实数} (K : 实数) (h : 对任意 x y, f x <= f y + K * dist x y)
  证明: have I : forall x y, f x - f y <= K * dist x y := fun x y => sub_le_iff_le_add'.2 (h x y)
  LipschitzWith.of_dist_le' fun x y => abs_sub_le_iff.2 ⟨I x y, dist_comm y x ▸ I y x⟩
-/
protected theorem of_le_add_mul' {f : α -> Real} (K : Real) (h : forall x y, f x <= f y + K * dist x y) :
    LipschitzWith (Real.toNNReal K) f :=
  have I : forall x y, f x - f y <= K * dist x y := fun x y => sub_le_iff_le_add'.2 (h x y)
  LipschitzWith.of_dist_le' fun x y => abs_sub_le_iff.2 ⟨I x y, dist_comm y x ▸ I y x⟩

/--
theorem `of_le_add_mul` / 定理 `of_le_add_mul`

English:
theorem of_le_add_mul
  given: {f : α -> Real} (K : Real>=0) (h : forall x y, f x <= f y + K * dist x y)
  proof: by simpa only [Real.toNNReal_coe] using LipschitzWith.of_le_add_mul' K h

中文:
定理 of_le_add_mul
  条件: {f : α -> 实数} (K : 实数>=0) (h : 对任意 x y, f x <= f y + K * dist x y)
  证明: by simpa only [Real.toNNReal_coe] using LipschitzWith.of_le_add_mul' K h
-/
protected theorem of_le_add_mul {f : α -> Real} (K : Real>=0) (h : forall x y, f x <= f y + K * dist x y) :
    LipschitzWith K f := by simpa only [Real.toNNReal_coe] using LipschitzWith.of_le_add_mul' K h

/--
theorem `of_le_add` / 定理 `of_le_add`

English:
theorem of_le_add
  given: {f : α -> Real} (h : forall x y, f x <= f y + dist x y)
  statement: LipschitzWith 1 f
  proof: LipschitzWith.of_le_add_mul 1 by simpa only [NNReal.coe_one, one_mul]

中文:
定理 of_le_add
  条件: {f : α -> 实数} (h : 对任意 x y, f x <= f y + dist x y)
  结论: LipschitzWith 1 f
  证明: LipschitzWith.of_le_add_mul 1 by simpa only [NNReal.coe_one, one_mul]
-/
protected theorem of_le_add {f : α -> Real} (h : forall x y, f x <= f y + dist x y) : LipschitzWith 1 f :=
LipschitzWith.of_le_add_mul 1 by simpa only [NNReal.coe_one, one_mul]

/--
theorem `le_add_mul` / 定理 `le_add_mul`

English:
theorem le_add_mul
  given: {f : α -> Real} {K : Real>=0} (h : LipschitzWith K f) (x y)
  proof: sub_le_iff_le_add'.1 le_trans (le_abs_self _) h.dist_le_mul x y

中文:
定理 le_add_mul
  条件: {f : α -> 实数} {K : 实数>=0} (h : LipschitzWith K f) (x y)
  证明: sub_le_iff_le_add'.1 le_trans (le_abs_self _) h.dist_le_mul x y
-/
protected theorem le_add_mul {f : α -> Real} {K : Real>=0} (h : LipschitzWith K f) (x y) :
    f x <= f y + K * dist x y :=
sub_le_iff_le_add'.1 le_trans (le_abs_self _) h.dist_le_mul x y

/--
theorem `iff_le_add_mul` / 定理 `iff_le_add_mul`

English:
theorem iff_le_add_mul
  given: {f : α -> Real} {K : Real>=0}
  proof: ⟨LipschitzWith.le_add_mul, LipschitzWith.of_le_add_mul K⟩

中文:
定理 iff_le_add_mul
  条件: {f : α -> 实数} {K : 实数>=0}
  证明: ⟨LipschitzWith.le_add_mul, LipschitzWith.of_le_add_mul K⟩
-/
protected theorem iff_le_add_mul {f : α -> Real} {K : Real>=0} :
    LipschitzWith K f ↔ forall x y, f x <= f y + K * dist x y :=
  ⟨LipschitzWith.le_add_mul, LipschitzWith.of_le_add_mul K⟩

/--
theorem `nndist_le` / 定理 `nndist_le`

English:
theorem nndist_le
  given: (hf : LipschitzWith K f) (x y : α)
  statement: nndist (f x) (f y) <= K * nndist x y
  proof: hf.dist_le_mul x y

中文:
定理 nndist_le
  条件: (hf : LipschitzWith K f) (x y : α)
  结论: nndist (f x) (f y) <= K * nndist x y
  证明: hf.dist_le_mul x y

Depends on / 依赖: dist_le_mul, hf.dist_le_mul
-/
theorem nndist_le (hf : LipschitzWith K f) (x y : α) : nndist (f x) (f y) <= K * nndist x y :=
  hf.dist_le_mul x y

/--
theorem `dist_le_mul_of_le` / 定理 `dist_le_mul_of_le`

English:
theorem dist_le_mul_of_le
  given: (hf : LipschitzWith K f) (hr : dist x y <= r)
  statement: dist (f x) (f y) <= K * r
  proof: (hf.dist_le_mul x y).trans by gcongr

中文:
定理 dist_le_mul_of_le
  条件: (hf : LipschitzWith K f) (hr : dist x y <= r)
  结论: dist (f x) (f y) <= K * r
  证明: (hf.dist_le_mul x y).trans by gcongr

Depends on / 依赖: dist_le_mul, hf.dist_le_mul
-/
theorem dist_le_mul_of_le (hf : LipschitzWith K f) (hr : dist x y <= r) : dist (f x) (f y) <= K * r :=
(hf.dist_le_mul x y).trans by gcongr

/--
theorem `mapsTo_closedBall` / 定理 `mapsTo_closedBall`

English:
theorem mapsTo_closedBall
  given: (hf : LipschitzWith K f) (x : α) (r : Real)
  proof: fun _y hy =>
  hf.dist_le_mul_of_le hy

中文:
定理 mapsTo_closedBall
  条件: (hf : LipschitzWith K f) (x : α) (r : 实数)
  证明: fun _y hy =>
  hf.dist_le_mul_of_le hy
-/
theorem mapsTo_closedBall (hf : LipschitzWith K f) (x : α) (r : Real) :
    MapsTo f (Metric.closedBall x r) (Metric.closedBall (f x) (K * r)) := fun _y hy =>
  hf.dist_le_mul_of_le hy

/--
theorem `dist_lt_mul_of_lt` / 定理 `dist_lt_mul_of_lt`

English:
theorem dist_lt_mul_of_lt
  given: (hf : LipschitzWith K f) (hK : K != 0) (hr : dist x y < r)
  proof: (hf.dist_le_mul x y).trans_lt by gcongr

中文:
定理 dist_lt_mul_of_lt
  条件: (hf : LipschitzWith K f) (hK : K != 0) (hr : dist x y < r)
  证明: (hf.dist_le_mul x y).trans_lt by gcongr

Depends on / 依赖: dist_le_mul, hf.dist_le_mul, trans_lt
-/
theorem dist_lt_mul_of_lt (hf : LipschitzWith K f) (hK : K != 0) (hr : dist x y < r) :
    dist (f x) (f y) < K * r :=
(hf.dist_le_mul x y).trans_lt by gcongr

/--
theorem `mapsTo_ball` / 定理 `mapsTo_ball`

English:
theorem mapsTo_ball
  given: (hf : LipschitzWith K f) (hK : K != 0) (x : α) (r : Real)
  proof: fun _y hy =>
  hf.dist_lt_mul_of_lt hK hy

中文:
定理 mapsTo_ball
  条件: (hf : LipschitzWith K f) (hK : K != 0) (x : α) (r : 实数)
  证明: fun _y hy =>
  hf.dist_lt_mul_of_lt hK hy
-/
theorem mapsTo_ball (hf : LipschitzWith K f) (hK : K != 0) (x : α) (r : Real) :
    MapsTo f (Metric.ball x r) (Metric.ball (f x) (K * r)) := fun _y hy =>
  hf.dist_lt_mul_of_lt hK hy

/--
Definition of `toLocallyBoundedMap` / `toLocallyBoundedMap` 的定义

English:
definition toLocallyBoundedMap
  signature: (f : α -> β) (hf : LipschitzWith K f)
  body: LocallyBoundedMap.ofMapBounded f fun _s hs =>
    let ⟨C, hC⟩ := Metric.isBounded_iff.1 hs
    Metric.isBounded_iff.2 ⟨K * C, forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy =>
      hf.dist_le_mul_of_le (hC hx hy)⟩

@[simp]

中文:
定义 toLocallyBoundedMap
  签名: (f : α -> β) (hf : LipschitzWith K f)
  定义体: LocallyBoundedMap.ofMapBounded f fun _s hs =>
    let ⟨C, hC⟩ := Metric.isBounded_iff.1 hs
    Metric.isBounded_iff.2 ⟨K * C, forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy =>
      hf.dist_le_mul_of_le (hC hx hy)⟩

@[simp]

Depends on / 依赖: LocallyBoundedMap, LocallyBoundedMap.ofMapBounded, Metric, Metric.isBounded_iff, dist_le_mul_of_le, forall_mem_image, hf.dist_le_mul_of_le, isBounded_iff, ofMapBounded
-/
def toLocallyBoundedMap (f : α -> β) (hf : LipschitzWith K f) : LocallyBoundedMap α β :=
  LocallyBoundedMap.ofMapBounded f fun _s hs =>
    let ⟨C, hC⟩ := Metric.isBounded_iff.1 hs
    Metric.isBounded_iff.2 ⟨K * C, forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy =>
      hf.dist_le_mul_of_le (hC hx hy)⟩

@[simp]
/--
theorem `coe_toLocallyBoundedMap` / 定理 `coe_toLocallyBoundedMap`

English:
theorem coe_toLocallyBoundedMap
  given: (hf : LipschitzWith K f)
  statement: ⇑(hf.toLocallyBoundedMap f) = f
  proof: rfl

中文:
定理 coe_toLocallyBoundedMap
  条件: (hf : LipschitzWith K f)
  结论: ⇑(hf.toLocallyBoundedMap f) = f
  证明: rfl
-/
theorem coe_toLocallyBoundedMap (hf : LipschitzWith K f) : ⇑(hf.toLocallyBoundedMap f) = f :=
  rfl

/--
theorem `comap_cobounded_le` / 定理 `comap_cobounded_le`

English:
theorem comap_cobounded_le
  given: (hf : LipschitzWith K f)
  proof: (hf.toLocallyBoundedMap f).2

中文:
定理 comap_cobounded_le
  条件: (hf : LipschitzWith K f)
  证明: (hf.toLocallyBoundedMap f).2

Depends on / 依赖: hf.toLocallyBoundedMap, toLocallyBoundedMap
-/
theorem comap_cobounded_le (hf : LipschitzWith K f) :
    comap f (Bornology.cobounded β) <= Bornology.cobounded α :=
  (hf.toLocallyBoundedMap f).2

/--
theorem `isBounded_image` / 定理 `isBounded_image`

English:
theorem isBounded_image
  given: (hf : LipschitzWith K f) {s : Set α} (hs : IsBounded s)
  proof: hs.image (toLocallyBoundedMap f hf)

中文:
定理 isBounded_image
  条件: (hf : LipschitzWith K f) {s : 集合 α} (hs : IsBounded s)
  证明: hs.image (toLocallyBoundedMap f hf)

Depends on / 依赖: hs.image, toLocallyBoundedMap
-/
theorem isBounded_image (hf : LipschitzWith K f) {s : Set α} (hs : IsBounded s) :
    IsBounded (f '' s) :=
  hs.image (toLocallyBoundedMap f hf)

/--
theorem `diam_image_le` / 定理 `diam_image_le`

English:
theorem diam_image_le
  given: (hf : LipschitzWith K f) (s : Set α) (hs : IsBounded s)
  proof: Metric.diam_le_of_forall_dist_le (mul_nonneg K.coe_nonneg Metric.diam_nonneg)
    forall_mem_image.2 fun _x hx =>
forall_mem_image.2 fun _y hy => hf.dist_le_mul_of_le Metric.dist_le_diam_of_mem hs hx hy

中文:
定理 diam_image_le
  条件: (hf : LipschitzWith K f) (s : 集合 α) (hs : IsBounded s)
  证明: Metric.diam_le_of_forall_dist_le (mul_nonneg K.coe_nonneg Metric.diam_nonneg)
    forall_mem_image.2 fun _x hx =>
forall_mem_image.2 fun _y hy => hf.dist_le_mul_of_le Metric.dist_le_diam_of_mem hs hx hy

Depends on / 依赖: K.coe_nonneg, Metric, Metric.diam_le_of_forall_dist_le, Metric.diam_nonneg, Metric.dist_le_diam_of_mem, coe_nonneg, diam_le_of_forall_dist_le, diam_nonneg, dist_le_diam_of_mem, dist_le_mul_of_le, forall_mem_image, hf.dist_le_mul_of_le, mul_nonneg
-/
theorem diam_image_le (hf : LipschitzWith K f) (s : Set α) (hs : IsBounded s) :
    Metric.diam (f '' s) <= K * Metric.diam s :=
Metric.diam_le_of_forall_dist_le (mul_nonneg K.coe_nonneg Metric.diam_nonneg)
    forall_mem_image.2 fun _x hx =>
forall_mem_image.2 fun _y hy => hf.dist_le_mul_of_le Metric.dist_le_diam_of_mem hs hx hy

/--
theorem `dist_left` / 定理 `dist_left`

English:
theorem dist_left
  given: (y : α)
  statement: LipschitzWith 1 (dist · y)
  proof: LipschitzWith.mk_one fun _ _ => dist_dist_dist_le_left _ _ _

中文:
定理 dist_left
  条件: (y : α)
  结论: LipschitzWith 1 (dist · y)
  证明: LipschitzWith.mk_one fun _ _ => dist_dist_dist_le_left _ _ _
-/
protected theorem dist_left (y : α) : LipschitzWith 1 (dist · y) :=
  LipschitzWith.mk_one fun _ _ => dist_dist_dist_le_left _ _ _

/--
theorem `dist_right` / 定理 `dist_right`

English:
theorem dist_right
  given: (x : α)
  statement: LipschitzWith 1 (dist x)
  proof: LipschitzWith.of_le_add fun _ _ => dist_triangle_right _ _ _

中文:
定理 dist_right
  条件: (x : α)
  结论: LipschitzWith 1 (dist x)
  证明: LipschitzWith.of_le_add fun _ _ => dist_triangle_right _ _ _
-/
protected theorem dist_right (x : α) : LipschitzWith 1 (dist x) :=
  LipschitzWith.of_le_add fun _ _ => dist_triangle_right _ _ _

/--
theorem `dist` / 定理 `dist`

English:
theorem dist
  statement: LipschitzWith 2 (Function.uncurry <| @dist α _)
  proof: by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry LipschitzWith.dist_left LipschitzWith.dist_right

中文:
定理 dist
  结论: LipschitzWith 2 (函数.uncurry <| @dist α _)
  证明: by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry LipschitzWith.dist_left LipschitzWith.dist_right
-/
protected theorem dist : LipschitzWith 2 (Function.uncurry <| @dist α _) := by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry LipschitzWith.dist_left LipschitzWith.dist_right

/--
theorem `dist_iterate_succ_le_geometric` / 定理 `dist_iterate_succ_le_geometric`

English:
theorem dist_iterate_succ_le_geometric
  given: {f : α -> α} (hf : LipschitzWith K f) (x n)
  proof: by
  rw [iterate_succ]; rw [mul_comm]
  simpa only [NNReal.coe_pow] using! (hf.iterate n).dist_le_mul x (f x)

中文:
定理 dist_iterate_succ_le_geometric
  条件: {f : α -> α} (hf : LipschitzWith K f) (x n)
  证明: by
  rw [iterate_succ]; rw [mul_comm]
  simpa only [NNReal.coe_pow] using! (hf.iterate n).dist_le_mul x (f x)

Depends on / 依赖: NNReal, NNReal.coe_pow, coe_pow, dist_le_mul, hf.iterate, iterate, iterate_succ, mul_comm
-/
theorem dist_iterate_succ_le_geometric {f : α -> α} (hf : LipschitzWith K f) (x n) :
    dist (f^[n] x) (f^[n + 1] x) <= dist x (f x) * (K : Real) ^ n := by
  rw [iterate_succ]; rw [mul_comm]
  simpa only [NNReal.coe_pow] using! (hf.iterate n).dist_le_mul x (f x)

/--
theorem `_root_.lipschitzWith_max` / 定理 `_root_.lipschitzWith_max`

English:
theorem _root_.lipschitzWith_max
  statement: LipschitzWith 1 fun p : Real × Real => max p.1 p.2
  proof: LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1
    (le_abs_self _).trans (abs_max_sub_max_le_max _ _ _ _)

中文:
定理 _root_.lipschitzWith_max
  结论: LipschitzWith 1 fun p : 实数 × 实数 => 最大值 p.1 p.2
  证明: LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1
    (le_abs_self _).trans (abs_max_sub_max_le_max _ _ _ _)

Depends on / 依赖: LipschitzWith, LipschitzWith.of_le_add, abs_max_sub_max_le_max, le_abs_self, of_le_add, sub_le_iff_le_add
-/
theorem _root_.lipschitzWith_max : LipschitzWith 1 fun p : Real × Real => max p.1 p.2 :=
LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1
    (le_abs_self _).trans (abs_max_sub_max_le_max _ _ _ _)

/--
theorem `_root_.lipschitzWith_min` / 定理 `_root_.lipschitzWith_min`

English:
theorem _root_.lipschitzWith_min
  statement: LipschitzWith 1 fun p : Real × Real => min p.1 p.2
  proof: LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1
    (le_abs_self _).trans (abs_min_sub_min_le_max _ _ _ _)

中文:
定理 _root_.lipschitzWith_min
  结论: LipschitzWith 1 fun p : 实数 × 实数 => 最小值 p.1 p.2
  证明: LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1
    (le_abs_self _).trans (abs_min_sub_min_le_max _ _ _ _)

Depends on / 依赖: LipschitzWith, LipschitzWith.of_le_add, abs_min_sub_min_le_max, le_abs_self, of_le_add, sub_le_iff_le_add
-/
theorem _root_.lipschitzWith_min : LipschitzWith 1 fun p : Real × Real => min p.1 p.2 :=
LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1
    (le_abs_self _).trans (abs_min_sub_min_le_max _ _ _ _)

/--
lemma `_root_.Real.lipschitzWith_toNNReal` / 引理 `_root_.Real.lipschitzWith_toNNReal`

English:
lemma _root_.Real.lipschitzWith_toNNReal
  statement: LipschitzWith 1 Real.toNNReal
  proof: by
  refine lipschitzWith_iff_dist_le_mul.mpr (fun x y => ?_)
  simpa only [NNReal.coe_one, dist_prod_same_right, one_mul, Real.dist_eq] using!
    lipschitzWith_iff_dist_le_mul.mp lipschitzWith_max (x, 0) (y, 0)

中文:
引理 _root_.实数.lipschitzWith_toNN实数
  结论: LipschitzWith 1 实数.toNN实数
  证明: by
  refine lipschitzWith_iff_dist_le_mul.mpr (fun x y => ?_)
  simpa only [NNReal.coe_one, dist_prod_same_right, one_mul, Real.dist_eq] using!
    lipschitzWith_iff_dist_le_mul.mp lipschitzWith_max (x, 0) (y, 0)

Depends on / 依赖: NNReal, NNReal.coe_one, Real.dist_eq, coe_one, dist_eq, dist_prod_same_right, lipschitzWith_iff_dist_le_mul, lipschitzWith_iff_dist_le_mul.mp, lipschitzWith_iff_dist_le_mul.mpr, lipschitzWith_max, one_mul
-/
lemma _root_.Real.lipschitzWith_toNNReal : LipschitzWith 1 Real.toNNReal := by
  refine lipschitzWith_iff_dist_le_mul.mpr (fun x y => ?_)
  simpa only [NNReal.coe_one, dist_prod_same_right, one_mul, Real.dist_eq] using!
    lipschitzWith_iff_dist_le_mul.mp lipschitzWith_max (x, 0) (y, 0)

/--
theorem `_root_.Set.separatesPoints_lipschitzWith_one` / 定理 `_root_.Set.separatesPoints_lipschitzWith_one`

English:
theorem _root_.Set.separatesPoints_lipschitzWith_one
  given: (E : Type*) [MetricSpace E]
  proof: fun _ y _ => ⟨(dist · y), by simp [LipschitzWith.dist_left], by simpa⟩

中文:
定理 _root_.集合.separatesPoints_lipschitzWith_one
  条件: (E : 类型) [度量空间 E]
  证明: fun _ y _ => ⟨(dist · y), by simp [LipschitzWith.dist_left], by simpa⟩

Depends on / 依赖: LipschitzWith, LipschitzWith.dist_left, dist_left
-/
theorem _root_.Set.separatesPoints_lipschitzWith_one (E : Type*) [MetricSpace E] :
    { f : E -> Real | LipschitzWith 1 f }.SeparatesPoints :=
  fun _ y _ => ⟨(dist · y), by simp [LipschitzWith.dist_left], by simpa⟩

end Metric

section EMetric

variable [PseudoEMetricSpace α] {f g : α -> Real} {Kf Kg : Real>=0}

/--
theorem `max` / 定理 `max`

English:
theorem max
  given: (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
  proof: by
  simpa only [(· ∘ ·), one_mul] using! lipschitzWith_max.comp (hf.prodMk hg)

中文:
定理 最大值
  条件: (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
  证明: by
  simpa only [(· ∘ ·), one_mul] using! lipschitzWith_max.comp (hf.prodMk hg)
-/
protected theorem max (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (max Kf Kg) fun x => max (f x) (g x) := by
  simpa only [(· ∘ ·), one_mul] using! lipschitzWith_max.comp (hf.prodMk hg)

/--
theorem `min` / 定理 `min`

English:
theorem min
  given: (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
  proof: by
  simpa only [(· ∘ ·), one_mul] using! lipschitzWith_min.comp (hf.prodMk hg)

中文:
定理 最小值
  条件: (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
  证明: by
  simpa only [(· ∘ ·), one_mul] using! lipschitzWith_min.comp (hf.prodMk hg)
-/
protected theorem min (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (max Kf Kg) fun x => min (f x) (g x) := by
  simpa only [(· ∘ ·), one_mul] using! lipschitzWith_min.comp (hf.prodMk hg)

/--
theorem `max_const` / 定理 `max_const`

English:
theorem max_const
  given: (hf : LipschitzWith Kf f) (a : Real)
  statement: LipschitzWith Kf fun x => max (f x) a
  proof: by
  simpa using hf.max (LipschitzWith.const a)

中文:
定理 max_const
  条件: (hf : LipschitzWith Kf f) (a : 实数)
  结论: LipschitzWith Kf fun x => 最大值 (f x) a
  证明: by
  simpa using hf.max (LipschitzWith.const a)

Depends on / 依赖: LipschitzWith, LipschitzWith.const, hf.max
-/
theorem max_const (hf : LipschitzWith Kf f) (a : Real) : LipschitzWith Kf fun x => max (f x) a := by
  simpa using hf.max (LipschitzWith.const a)

/--
theorem `const_max` / 定理 `const_max`

English:
theorem const_max
  given: (hf : LipschitzWith Kf f) (a : Real)
  statement: LipschitzWith Kf fun x => max a (f x)
  proof: by
  simpa only [max_comm] using hf.max_const a

中文:
定理 const_max
  条件: (hf : LipschitzWith Kf f) (a : 实数)
  结论: LipschitzWith Kf fun x => 最大值 a (f x)
  证明: by
  simpa only [max_comm] using hf.max_const a

Depends on / 依赖: hf.max_const, max_comm, max_const
-/
theorem const_max (hf : LipschitzWith Kf f) (a : Real) : LipschitzWith Kf fun x => max a (f x) := by
  simpa only [max_comm] using hf.max_const a

/--
theorem `min_const` / 定理 `min_const`

English:
theorem min_const
  given: (hf : LipschitzWith Kf f) (a : Real)
  statement: LipschitzWith Kf fun x => min (f x) a
  proof: by
  simpa using hf.min (LipschitzWith.const a)

中文:
定理 min_const
  条件: (hf : LipschitzWith Kf f) (a : 实数)
  结论: LipschitzWith Kf fun x => 最小值 (f x) a
  证明: by
  simpa using hf.min (LipschitzWith.const a)

Depends on / 依赖: LipschitzWith, LipschitzWith.const, hf.min
-/
theorem min_const (hf : LipschitzWith Kf f) (a : Real) : LipschitzWith Kf fun x => min (f x) a := by
  simpa using hf.min (LipschitzWith.const a)

/--
theorem `const_min` / 定理 `const_min`

English:
theorem const_min
  given: (hf : LipschitzWith Kf f) (a : Real)
  statement: LipschitzWith Kf fun x => min a (f x)
  proof: by
  simpa only [min_comm] using hf.min_const a

中文:
定理 const_min
  条件: (hf : LipschitzWith Kf f) (a : 实数)
  结论: LipschitzWith Kf fun x => 最小值 a (f x)
  证明: by
  simpa only [min_comm] using hf.min_const a

Depends on / 依赖: hf.min_const, min_comm, min_const
-/
theorem const_min (hf : LipschitzWith Kf f) (a : Real) : LipschitzWith Kf fun x => min a (f x) := by
  simpa only [min_comm] using hf.min_const a

end EMetric

/--
theorem `projIcc` / 定理 `projIcc`

English:
theorem projIcc
  given: {a b : Real} (h : a <= b)
  statement: LipschitzWith 1 (projIcc a b h)
  proof: ((LipschitzWith.id.const_min _).const_max _).subtype_mk _

中文:
定理 projIcc
  条件: {a b : 实数} (h : a <= b)
  结论: LipschitzWith 1 (projIcc a b h)
  证明: ((LipschitzWith.id.const_min _).const_max _).subtype_mk _
-/
protected theorem projIcc {a b : Real} (h : a <= b) : LipschitzWith 1 (projIcc a b h) :=
  ((LipschitzWith.id.const_min _).const_max _).subtype_mk _

end LipschitzWith

/--
lemma `LipschitzWith.properSpace` / 引理 `LipschitzWith.properSpace`

English:
lemma LipschitzWith.properSpace
  statement: {X Y : Type*} [PseudoMetricSpace X]
  proof: ⟨fun x r => (hf.isCompact_preimage (isCompact_closedBall (f x) (K * r))).of_isClosed_subset
    Metric.isClosed_closedBall (hf'.mapsTo_closedBall x r).subset_preimage⟩

中文:
引理 LipschitzWith.properSpace
  结论: {X Y : 类型} [伪度量空间 X]
  证明: ⟨fun x r => (hf.isCompact_preimage (isCompact_closedBall (f x) (K * r))).of_isClosed_subset
    Metric.isClosed_closedBall (hf'.mapsTo_closedBall x r).subset_preimage⟩

Depends on / 依赖: Metric, Metric.isClosed_closedBall, hf.isCompact_preimage, isClosed_closedBall, isCompact_closedBall, isCompact_preimage, mapsTo_closedBall, of_isClosed_subset, subset_preimage
-/
lemma LipschitzWith.properSpace {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] [ProperSpace Y] {f : X -> Y} (hf : IsProperMap f)
    {K : Real>=0} (hf' : LipschitzWith K f) : ProperSpace X :=
  ⟨fun x r => (hf.isCompact_preimage (isCompact_closedBall (f x) (K * r))).of_isClosed_subset
    Metric.isClosed_closedBall (hf'.mapsTo_closedBall x r).subset_preimage⟩

namespace LipschitzOnWith

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
variable {K : Real>=0} {s : Set α} {f : α -> β}

/--
theorem `of_dist_le'` / 定理 `of_dist_le'`

English:
theorem of_dist_le'
  given: {K : Real} (h : forall x in s, forall y in s, dist (f x) (f y) <= K * dist x y)
  proof: of_dist_le_mul fun x hx y hy =>
le_trans (h x hx y hy) by gcongr; apply Real.le_coe_toNNReal

中文:
定理 of_dist_le'
  条件: {K : 实数} (h : 对任意 x in s, 对任意 y in s, dist (f x) (f y) <= K * dist x y)
  证明: of_dist_le_mul fun x hx y hy =>
le_trans (h x hx y hy) by gcongr; apply Real.le_coe_toNNReal
-/
protected theorem of_dist_le' {K : Real} (h : forall x in s, forall y in s, dist (f x) (f y) <= K * dist x y) :
    LipschitzOnWith (Real.toNNReal K) f s :=
  of_dist_le_mul fun x hx y hy =>
le_trans (h x hx y hy) by gcongr; apply Real.le_coe_toNNReal

/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  given: (h : forall x in s, forall y in s, dist (f x) (f y) <= dist x y)
  proof: of_dist_le_mul by simpa only [NNReal.coe_one, one_mul] using h

中文:
定理 mk_one
  条件: (h : 对任意 x in s, 对任意 y in s, dist (f x) (f y) <= dist x y)
  证明: of_dist_le_mul by simpa only [NNReal.coe_one, one_mul] using h
-/
protected theorem mk_one (h : forall x in s, forall y in s, dist (f x) (f y) <= dist x y) :
    LipschitzOnWith 1 f s :=
of_dist_le_mul by simpa only [NNReal.coe_one, one_mul] using h

/--
theorem `of_le_add_mul'` / 定理 `of_le_add_mul'`

English:
theorem of_le_add_mul'
  statement: {f : α -> Real} (K : Real)
  proof: have I : forall x in s, forall y in s, f x - f y <= K * dist x y := fun x hx y hy =>
    sub_le_iff_le_add'.2 (h x hx y hy)
  LipschitzOnWith.of_dist_le' fun x hx y hy =>
    abs_sub_le_iff.2 ⟨I x hx y hy, dist_comm y x ▸ I y hy x hx⟩

中文:
定理 of_le_add_mul'
  结论: {f : α -> 实数} (K : 实数)
  证明: have I : forall x in s, forall y in s, f x - f y <= K * dist x y := fun x hx y hy =>
    sub_le_iff_le_add'.2 (h x hx y hy)
  LipschitzOnWith.of_dist_le' fun x hx y hy =>
    abs_sub_le_iff.2 ⟨I x hx y hy, dist_comm y x ▸ I y hy x hx⟩
-/
protected theorem of_le_add_mul' {f : α -> Real} (K : Real)
    (h : forall x in s, forall y in s, f x <= f y + K * dist x y) : LipschitzOnWith (Real.toNNReal K) f s :=
  have I : forall x in s, forall y in s, f x - f y <= K * dist x y := fun x hx y hy =>
    sub_le_iff_le_add'.2 (h x hx y hy)
  LipschitzOnWith.of_dist_le' fun x hx y hy =>
    abs_sub_le_iff.2 ⟨I x hx y hy, dist_comm y x ▸ I y hy x hx⟩

/--
theorem `of_le_add_mul` / 定理 `of_le_add_mul`

English:
theorem of_le_add_mul
  statement: {f : α -> Real} (K : Real>=0)
  proof: by
  simpa only [Real.toNNReal_coe] using LipschitzOnWith.of_le_add_mul' K h

中文:
定理 of_le_add_mul
  结论: {f : α -> 实数} (K : 实数>=0)
  证明: by
  simpa only [Real.toNNReal_coe] using LipschitzOnWith.of_le_add_mul' K h
-/
protected theorem of_le_add_mul {f : α -> Real} (K : Real>=0)
    (h : forall x in s, forall y in s, f x <= f y + K * dist x y) : LipschitzOnWith K f s := by
  simpa only [Real.toNNReal_coe] using LipschitzOnWith.of_le_add_mul' K h

/--
theorem `of_le_add` / 定理 `of_le_add`

English:
theorem of_le_add
  given: {f : α -> Real} (h : forall x in s, forall y in s, f x <= f y + dist x y)
  proof: LipschitzOnWith.of_le_add_mul 1 by simpa only [NNReal.coe_one, one_mul]

中文:
定理 of_le_add
  条件: {f : α -> 实数} (h : 对任意 x in s, 对任意 y in s, f x <= f y + dist x y)
  证明: LipschitzOnWith.of_le_add_mul 1 by simpa only [NNReal.coe_one, one_mul]
-/
protected theorem of_le_add {f : α -> Real} (h : forall x in s, forall y in s, f x <= f y + dist x y) :
    LipschitzOnWith 1 f s :=
LipschitzOnWith.of_le_add_mul 1 by simpa only [NNReal.coe_one, one_mul]

/--
theorem `le_add_mul` / 定理 `le_add_mul`

English:
theorem le_add_mul
  statement: {f : α -> Real} {K : Real>=0} (h : LipschitzOnWith K f s) {x : α} (hx : x in s)
  proof: sub_le_iff_le_add'.1 le_trans (le_abs_self _) h.dist_le_mul x hx y hy

中文:
定理 le_add_mul
  结论: {f : α -> 实数} {K : 实数>=0} (h : LipschitzOnWith K f s) {x : α} (hx : x in s)
  证明: sub_le_iff_le_add'.1 le_trans (le_abs_self _) h.dist_le_mul x hx y hy
-/
protected theorem le_add_mul {f : α -> Real} {K : Real>=0} (h : LipschitzOnWith K f s) {x : α} (hx : x in s)
    {y : α} (hy : y in s) : f x <= f y + K * dist x y :=
sub_le_iff_le_add'.1 le_trans (le_abs_self _) h.dist_le_mul x hx y hy

/--
theorem `iff_le_add_mul` / 定理 `iff_le_add_mul`

English:
theorem iff_le_add_mul
  given: {f : α -> Real} {K : Real>=0}
  proof: ⟨LipschitzOnWith.le_add_mul, LipschitzOnWith.of_le_add_mul K⟩

中文:
定理 iff_le_add_mul
  条件: {f : α -> 实数} {K : 实数>=0}
  证明: ⟨LipschitzOnWith.le_add_mul, LipschitzOnWith.of_le_add_mul K⟩
-/
protected theorem iff_le_add_mul {f : α -> Real} {K : Real>=0} :
    LipschitzOnWith K f s ↔ forall x in s, forall y in s, f x <= f y + K * dist x y :=
  ⟨LipschitzOnWith.le_add_mul, LipschitzOnWith.of_le_add_mul K⟩

/--
theorem `isBounded_image2` / 定理 `isBounded_image2`

English:
theorem isBounded_image2
  statement: (f : α -> β -> γ) {K₁ K₂ : Real>=0} {s : Set α} {t : Set β}
  proof: Metric.isBounded_iff_ediam_ne_top.2
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hs.ediam_ne_top,
          ENNReal.mul_ne_top ENNReal.coe_ne_top ht.ediam_ne_top⟩)
      (ediam_image2_le _ _ _ hf₁ hf₂)

中文:
定理 isBounded_image2
  结论: (f : α -> β -> γ) {K₁ K₂ : 实数>=0} {s : 集合 α} {t : 集合 β}
  证明: Metric.isBounded_iff_ediam_ne_top.2
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hs.ediam_ne_top,
          ENNReal.mul_ne_top ENNReal.coe_ne_top ht.ediam_ne_top⟩)
      (ediam_image2_le _ _ _ hf₁ hf₂)

Depends on / 依赖: ENNReal, ENNReal.add_ne_top.mpr, ENNReal.coe_ne_top, ENNReal.mul_ne_top, Metric, Metric.isBounded_iff_ediam_ne_top, add_ne_top, coe_ne_top, ediam_image2_le, ediam_ne_top, hs.ediam_ne_top, ht.ediam_ne_top, isBounded_iff_ediam_ne_top, mul_ne_top, ne_top_of_le_ne_top
-/
theorem isBounded_image2 (f : α -> β -> γ) {K₁ K₂ : Real>=0} {s : Set α} {t : Set β}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t)
    (hf₁ : forall b in t, LipschitzOnWith K₁ (fun a => f a b) s)
    (hf₂ : forall a in s, LipschitzOnWith K₂ (f a) t) : Bornology.IsBounded (Set.image2 f s t) :=
Metric.isBounded_iff_ediam_ne_top.2
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hs.ediam_ne_top,
          ENNReal.mul_ne_top ENNReal.coe_ne_top ht.ediam_ne_top⟩)
      (ediam_image2_le _ _ _ hf₁ hf₂)

end Metric

end LipschitzOnWith

namespace LocallyLipschitz

section Real

variable [PseudoEMetricSpace α] {f g : α -> Real}

/--
lemma `min` / 引理 `min`

English:
lemma min
  given: (hf : LocallyLipschitz f) (hg : LocallyLipschitz g)
  proof: lipschitzWith_min.locallyLipschitz.comp (hf.prodMk hg)

中文:
引理 最小值
  条件: (hf : LocallyLipschitz f) (hg : LocallyLipschitz g)
  证明: lipschitzWith_min.locallyLipschitz.comp (hf.prodMk hg)
-/
protected lemma min (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => min (f x) (g x)) :=
  lipschitzWith_min.locallyLipschitz.comp (hf.prodMk hg)

/--
lemma `max` / 引理 `max`

English:
lemma max
  given: (hf : LocallyLipschitz f) (hg : LocallyLipschitz g)
  proof: lipschitzWith_max.locallyLipschitz.comp (hf.prodMk hg)

中文:
引理 最大值
  条件: (hf : LocallyLipschitz f) (hg : LocallyLipschitz g)
  证明: lipschitzWith_max.locallyLipschitz.comp (hf.prodMk hg)
-/
protected lemma max (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => max (f x) (g x)) :=
  lipschitzWith_max.locallyLipschitz.comp (hf.prodMk hg)

/--
theorem `max_const` / 定理 `max_const`

English:
theorem max_const
  given: (hf : LocallyLipschitz f) (a : Real)
  statement: LocallyLipschitz fun x => max (f x) a
  proof: hf.max (LocallyLipschitz.const a)

中文:
定理 max_const
  条件: (hf : LocallyLipschitz f) (a : 实数)
  结论: LocallyLipschitz fun x => 最大值 (f x) a
  证明: hf.max (LocallyLipschitz.const a)

Depends on / 依赖: LocallyLipschitz, LocallyLipschitz.const, hf.max
-/
theorem max_const (hf : LocallyLipschitz f) (a : Real) : LocallyLipschitz fun x => max (f x) a :=
  hf.max (LocallyLipschitz.const a)

/--
theorem `const_max` / 定理 `const_max`

English:
theorem const_max
  given: (hf : LocallyLipschitz f) (a : Real)
  statement: LocallyLipschitz fun x => max a (f x)
  proof: by
  simpa [max_comm] using (hf.max_const a)

中文:
定理 const_max
  条件: (hf : LocallyLipschitz f) (a : 实数)
  结论: LocallyLipschitz fun x => 最大值 a (f x)
  证明: by
  simpa [max_comm] using (hf.max_const a)

Depends on / 依赖: hf.max_const, max_comm, max_const
-/
theorem const_max (hf : LocallyLipschitz f) (a : Real) : LocallyLipschitz fun x => max a (f x) := by
  simpa [max_comm] using (hf.max_const a)

/--
theorem `min_const` / 定理 `min_const`

English:
theorem min_const
  given: (hf : LocallyLipschitz f) (a : Real)
  statement: LocallyLipschitz fun x => min (f x) a
  proof: hf.min (LocallyLipschitz.const a)

中文:
定理 min_const
  条件: (hf : LocallyLipschitz f) (a : 实数)
  结论: LocallyLipschitz fun x => 最小值 (f x) a
  证明: hf.min (LocallyLipschitz.const a)

Depends on / 依赖: LocallyLipschitz, LocallyLipschitz.const, hf.min
-/
theorem min_const (hf : LocallyLipschitz f) (a : Real) : LocallyLipschitz fun x => min (f x) a :=
  hf.min (LocallyLipschitz.const a)

/--
theorem `const_min` / 定理 `const_min`

English:
theorem const_min
  given: (hf : LocallyLipschitz f) (a : Real)
  statement: LocallyLipschitz fun x => min a (f x)
  proof: by
  simpa [min_comm] using (hf.min_const a)

中文:
定理 const_min
  条件: (hf : LocallyLipschitz f) (a : 实数)
  结论: LocallyLipschitz fun x => 最小值 a (f x)
  证明: by
  simpa [min_comm] using (hf.min_const a)

Depends on / 依赖: hf.min_const, min_comm, min_const
-/
theorem const_min (hf : LocallyLipschitz f) (a : Real) : LocallyLipschitz fun x => min a (f x) := by
  simpa [min_comm] using (hf.min_const a)

end Real
end LocallyLipschitz

open Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α -> β}

/--
theorem `LipschitzOnWith.extend_real` / 定理 `LipschitzOnWith.extend_real`

English:
theorem LipschitzOnWith.extend_real
  given: {f : α -> Real} {s : Set α} {K : Real>=0} (hf : LipschitzOnWith K f s)
  proof: by
  /- An extension is given by `g y = Inf {f x + K * dist y x | x ∈ s}`. Taking `x = y`, one has
    `g y ≤ f y` for `y ∈ s`, and the other inequality holds because `f` is `K`-Lipschitz, so that it
    cannot counterbalance the growth of `K * dist y x`. One readily checks from the formula that
    the extended function is also `K`-Lipschitz. -/
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · exact ⟨fun _ => 0, (LipschitzWith.const _).weaken zero_le, eqOn_empty _ _⟩
  have : Nonempty s := by simp only [hs, nonempty_coe_sort]
  let g := fun y : α => iInf fun x : s => f x + K * dist y x
  have B : forall y : α, BddBelow (range fun x : s => f x + K * dist y x) := fun y => by
    rcases hs with ⟨z, hz⟩
    refine ⟨f z - K * dist y z, ?_⟩
    rintro w ⟨t, rfl⟩
    dsimp
    rw [sub_le_iff_le_add]; rw [add_assoc]; rw [← mul_add]; rw [add_comm (dist y t)]
    calc
      f z <= f t + K * dist z t := hf.le_add_mul hz t.2
      _ <= f t + K * (dist y z + dist y t) := by gcongr; apply dist_triangle_left
  have E : EqOn f g s := fun x hx => by
    refine le_antisymm (le_ciInf fun y => hf.le_add_mul hx y.2) ?_
    simpa only [add_zero, Subtype.coe_mk, mul_zero, dist_self] using ciInf_le (B x) ⟨x, hx⟩
  refine ⟨g, LipschitzWith.of_le_add_mul K fun x y => ?_, E⟩
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun z => ?_
  rw [sub_le_iff_le_add]
  calc
    g x <= f z + K * dist x z := ciInf_le (B x) _
    _ <= f z + K * dist y z + K * dist x y := by
      rw [add_assoc]; rw [← mul_add]; rw [add_comm (dist y z)]
      gcongr
      apply dist_triangle

中文:
定理 LipschitzOnWith.extend_real
  条件: {f : α -> 实数} {s : 集合 α} {K : 实数>=0} (hf : LipschitzOnWith K f s)
  证明: by
  /- An extension is given by `g y = Inf {f x + K * dist y x | x ∈ s}`. Taking `x = y`, one has
    `g y ≤ f y` for `y ∈ s`, and the other inequality holds because `f` is `K`-Lipschitz, so that it
    cannot counterbalance the growth of `K * dist y x`. One readily checks from the formula that
    the extended function is also `K`-Lipschitz. -/
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · exact ⟨fun _ => 0, (LipschitzWith.const _).weaken zero_le, eqOn_empty _ _⟩
  have : Nonempty s := by simp only [hs, nonempty_coe_sort]
  let g := fun y : α => iInf fun x : s => f x + K * dist y x
  have B : forall y : α, BddBelow (range fun x : s => f x + K * dist y x) := fun y => by
    rcases hs with ⟨z, hz⟩
    refine ⟨f z - K * dist y z, ?_⟩
    rintro w ⟨t, rfl⟩
    dsimp
    rw [sub_le_iff_le_add]; rw [add_assoc]; rw [← mul_add]; rw [add_comm (dist y t)]
    calc
      f z <= f t + K * dist z t := hf.le_add_mul hz t.2
      _ <= f t + K * (dist y z + dist y t) := by gcongr; apply dist_triangle_left
  have E : EqOn f g s := fun x hx => by
    refine le_antisymm (le_ciInf fun y => hf.le_add_mul hx y.2) ?_
    simpa only [add_zero, Subtype.coe_mk, mul_zero, dist_self] using ciInf_le (B x) ⟨x, hx⟩
  refine ⟨g, LipschitzWith.of_le_add_mul K fun x y => ?_, E⟩
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun z => ?_
  rw [sub_le_iff_le_add]
  calc
    g x <= f z + K * dist x z := ciInf_le (B x) _
    _ <= f z + K * dist y z + K * dist x y := by
      rw [add_assoc]; rw [← mul_add]; rw [add_comm (dist y z)]
      gcongr
      apply dist_triangle
-/
theorem LipschitzOnWith.extend_real {f : α -> Real} {s : Set α} {K : Real>=0} (hf : LipschitzOnWith K f s) :
    exists g : α -> Real, LipschitzWith K g ∧ EqOn f g s := by
  /- An extension is given by `g y = Inf {f x + K * dist y x | x ∈ s}`. Taking `x = y`, one has
    `g y ≤ f y` for `y ∈ s`, and the other inequality holds because `f` is `K`-Lipschitz, so that it
    cannot counterbalance the growth of `K * dist y x`. One readily checks from the formula that
    the extended function is also `K`-Lipschitz. -/
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · exact ⟨fun _ => 0, (LipschitzWith.const _).weaken zero_le, eqOn_empty _ _⟩
  have : Nonempty s := by simp only [hs, nonempty_coe_sort]
  let g := fun y : α => iInf fun x : s => f x + K * dist y x
  have B : forall y : α, BddBelow (range fun x : s => f x + K * dist y x) := fun y => by
    rcases hs with ⟨z, hz⟩
    refine ⟨f z - K * dist y z, ?_⟩
    rintro w ⟨t, rfl⟩
    dsimp
    rw [sub_le_iff_le_add]; rw [add_assoc]; rw [← mul_add]; rw [add_comm (dist y t)]
    calc
      f z <= f t + K * dist z t := hf.le_add_mul hz t.2
      _ <= f t + K * (dist y z + dist y t) := by gcongr; apply dist_triangle_left
  have E : EqOn f g s := fun x hx => by
    refine le_antisymm (le_ciInf fun y => hf.le_add_mul hx y.2) ?_
    simpa only [add_zero, Subtype.coe_mk, mul_zero, dist_self] using ciInf_le (B x) ⟨x, hx⟩
  refine ⟨g, LipschitzWith.of_le_add_mul K fun x y => ?_, E⟩
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun z => ?_
  rw [sub_le_iff_le_add]
  calc
    g x <= f z + K * dist x z := ciInf_le (B x) _
    _ <= f z + K * dist y z + K * dist x y := by
      rw [add_assoc]; rw [← mul_add]; rw [add_comm (dist y z)]
      gcongr
      apply dist_triangle

/--
theorem `LipschitzOnWith.extend_pi` / 定理 `LipschitzOnWith.extend_pi`

English:
theorem LipschitzOnWith.extend_pi
  statement: [Fintype ι] {f : α -> ι -> Real} {s : Set α}
  proof: by
  have : forall i, exists g : α -> Real, LipschitzWith K g ∧ EqOn (fun x => f x i) g s := fun i => by
    have : LipschitzOnWith K (fun x : α => f x i) s :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
        (dist_le_pi_dist _ _ i).trans (hf.dist_le_mul x hx y hy)
    exact this.extend_real
  choose g hg using this
  refine ⟨fun x i => g i x, LipschitzWith.of_dist_le_mul fun x y => ?_, fun x hx => ?_⟩
  · exact (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).2 fun i => (hg i).1.dist_le_mul x y
  · ext1 i
    exact (hg i).2 hx

中文:
定理 LipschitzOnWith.extend_pi
  结论: [有限类型 ι] {f : α -> ι -> 实数} {s : 集合 α}
  证明: by
  have : forall i, exists g : α -> Real, LipschitzWith K g ∧ EqOn (fun x => f x i) g s := fun i => by
    have : LipschitzOnWith K (fun x : α => f x i) s :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
        (dist_le_pi_dist _ _ i).trans (hf.dist_le_mul x hx y hy)
    exact this.extend_real
  choose g hg using this
  refine ⟨fun x i => g i x, LipschitzWith.of_dist_le_mul fun x y => ?_, fun x hx => ?_⟩
  · exact (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).2 fun i => (hg i).1.dist_le_mul x y
  · ext1 i
    exact (hg i).2 hx

Depends on / 依赖: LipschitzOnWith, LipschitzOnWith.of_dist_le_mul, LipschitzWith, LipschitzWith.of_dist_le_mul, dist_le_mul, dist_le_pi_dist, dist_nonneg, dist_pi_le_iff, extend_real, hf.dist_le_mul, mul_nonneg, of_dist_le_mul, this.extend_real
-/
theorem LipschitzOnWith.extend_pi [Fintype ι] {f : α -> ι -> Real} {s : Set α}
    {K : Real>=0} (hf : LipschitzOnWith K f s) : exists g : α -> ι -> Real, LipschitzWith K g ∧ EqOn f g s := by
  have : forall i, exists g : α -> Real, LipschitzWith K g ∧ EqOn (fun x => f x i) g s := fun i => by
    have : LipschitzOnWith K (fun x : α => f x i) s :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
        (dist_le_pi_dist _ _ i).trans (hf.dist_le_mul x hx y hy)
    exact this.extend_real
  choose g hg using this
  refine ⟨fun x i => g i x, LipschitzWith.of_dist_le_mul fun x y => ?_, fun x hx => ?_⟩
  · exact (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).2 fun i => (hg i).1.dist_le_mul x y
  · ext1 i
    exact (hg i).2 hx
