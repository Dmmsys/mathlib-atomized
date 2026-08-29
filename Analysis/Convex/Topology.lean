/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Strict
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Topological properties of convex sets

We prove the following facts:

* `Convex.interior` : interior of a convex set is convex;
* `Convex.closure` : closure of a convex set is convex;
* `closedConvexHull_closure_eq_closedConvexHull` : the closed convex hull of the closure of a set is
  equal to the closed convex hull of the set;
* `Set.Finite.isCompact_convexHull` : convex hull of a finite set is compact;
* `Set.Finite.isClosed_convexHull` : convex hull of a finite set is closed.
-/

@[expose] public section

assert_not_exists Cardinal Norm

open Metric Bornology Set Pointwise Convex

variable {ι 𝕜 E : Type*}

namespace Real
variable {s : Set Real} {r ε : Real}

/--
lemma `closedBall_eq_segment` / 引理 `closedBall_eq_segment`

English:
lemma closedBall_eq_segment
  given: (hε : 0 <= ε)
  statement: closedBall r ε = segment Real (r - ε) (r + ε)
  proof: by
  rw [closedBall_eq_Icc]; rw [segment_eq_Icc ((sub_le_self _ hε).trans <| le_add_of_nonneg_right hε)]

中文:
引理 closedBall_eq_segment
  条件: (hε : 0 <= ε)
  结论: closedBall r ε = segment 实数 (r - ε) (r + ε)
  证明: by
  rw [closedBall_eq_Icc]; rw [segment_eq_Icc ((sub_le_self _ hε).trans <| le_add_of_nonneg_right hε)]

Depends on / 依赖: closedBall_eq_Icc, le_add_of_nonneg_right, segment_eq_Icc, sub_le_self
-/
lemma closedBall_eq_segment (hε : 0 <= ε) : closedBall r ε = segment Real (r - ε) (r + ε) := by
  rw [closedBall_eq_Icc]; rw [segment_eq_Icc ((sub_le_self _ hε).trans <| le_add_of_nonneg_right hε)]

/--
lemma `ball_eq_openSegment` / 引理 `ball_eq_openSegment`

English:
lemma ball_eq_openSegment
  given: (hε : 0 < ε)
  statement: ball r ε = openSegment Real (r - ε) (r + ε)
  proof: by
  rw [ball_eq_Ioo]; rw [openSegment_eq_Ioo ((sub_lt_self _ hε).trans <| lt_add_of_pos_right _ hε)]

中文:
引理 ball_eq_openSegment
  条件: (hε : 0 < ε)
  结论: ball r ε = openSegment 实数 (r - ε) (r + ε)
  证明: by
  rw [ball_eq_Ioo]; rw [openSegment_eq_Ioo ((sub_lt_self _ hε).trans <| lt_add_of_pos_right _ hε)]

Depends on / 依赖: ball_eq_Ioo, lt_add_of_pos_right, openSegment_eq_Ioo, sub_lt_self
-/
lemma ball_eq_openSegment (hε : 0 < ε) : ball r ε = openSegment Real (r - ε) (r + ε) := by
  rw [ball_eq_Ioo]; rw [openSegment_eq_Ioo ((sub_lt_self _ hε).trans <| lt_add_of_pos_right _ hε)]

/--
theorem `convex_iff_isPreconnected` / 定理 `convex_iff_isPreconnected`

English:
theorem convex_iff_isPreconnected
  statement: Convex Real s ↔ IsPreconnected s
  proof: convex_iff_ordConnected.trans isPreconnected_iff_ordConnected.symm

中文:
定理 convex_iff_isPreconnected
  结论: 凸 实数 s ↔ 是预连通 s
  证明: convex_iff_ordConnected.trans isPreconnected_iff_ordConnected.symm

Depends on / 依赖: convex_iff_ordConnected, convex_iff_ordConnected.trans, isPreconnected_iff_ordConnected, isPreconnected_iff_ordConnected.symm
-/
theorem convex_iff_isPreconnected : Convex Real s ↔ IsPreconnected s :=
  convex_iff_ordConnected.trans isPreconnected_iff_ordConnected.symm

end Real

alias ⟨_, IsPreconnected.convex⟩ := Real.convex_iff_isPreconnected

/-! ### Topological vector spaces -/
section TopologicalSpace

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  {x y : E}

/--
theorem `segment_subset_closure_openSegment` / 定理 `segment_subset_closure_openSegment`

English:
theorem segment_subset_closure_openSegment
  statement: [x -[𝕜] y] subseteq closure (openSegment 𝕜 x y)
  proof: by
  rw [segment_eq_image]; rw [openSegment_eq_image]; rw [← closure_Ioo (zero_ne_one' 𝕜)]
  exact image_closure_subset_closure_image (by fun_prop)

中文:
定理 segment_subset_closure_openSegment
  结论: [x -[𝕜] y] subseteq closure (openSegment 𝕜 x y)
  证明: by
  rw [segment_eq_image]; rw [openSegment_eq_image]; rw [← closure_Ioo (zero_ne_one' 𝕜)]
  exact image_closure_subset_closure_image (by fun_prop)

Depends on / 依赖: closure_Ioo, fun_prop, image_closure_subset_closure_image, openSegment_eq_image, segment_eq_image, zero_ne_one
-/
theorem segment_subset_closure_openSegment : [x -[𝕜] y] subseteq closure (openSegment 𝕜 x y) := by
  rw [segment_eq_image]; rw [openSegment_eq_image]; rw [← closure_Ioo (zero_ne_one' 𝕜)]
  exact image_closure_subset_closure_image (by fun_prop)

end TopologicalSpace

section PseudoMetricSpace

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
  [PseudoMetricSpace 𝕜] [OrderTopology 𝕜]
  [ProperSpace 𝕜] [CompactIccSpace 𝕜] [AddCommGroup E] [TopologicalSpace E] [T2Space E]
  [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]

@[simp]
/--
theorem `closure_openSegment` / 定理 `closure_openSegment`

English:
theorem closure_openSegment
  given: (x y : E)
  statement: closure (openSegment 𝕜 x y) = [x -[𝕜] y]
  proof: by
  rw [segment_eq_image]; rw [openSegment_eq_image]; rw [← closure_Ioo (zero_ne_one' 𝕜)]
  exact (image_closure_of_isCompact (isBounded_Ioo _ _).isCompact_closure <|
Continuous.continuousOn by fun_prop).symm

中文:
定理 closure_openSegment
  条件: (x y : E)
  结论: closure (openSegment 𝕜 x y) = [x -[𝕜] y]
  证明: by
  rw [segment_eq_image]; rw [openSegment_eq_image]; rw [← closure_Ioo (zero_ne_one' 𝕜)]
  exact (image_closure_of_isCompact (isBounded_Ioo _ _).isCompact_closure <|
Continuous.continuousOn by fun_prop).symm

Depends on / 依赖: Continuous, Continuous.continuousOn, closure_Ioo, continuousOn, fun_prop, image_closure_of_isCompact, isBounded_Ioo, isCompact_closure, openSegment_eq_image, segment_eq_image, zero_ne_one
-/
theorem closure_openSegment (x y : E) : closure (openSegment 𝕜 x y) = [x -[𝕜] y] := by
  rw [segment_eq_image]; rw [openSegment_eq_image]; rw [← closure_Ioo (zero_ne_one' 𝕜)]
  exact (image_closure_of_isCompact (isBounded_Ioo _ _).isCompact_closure <|
Continuous.continuousOn by fun_prop).symm

end PseudoMetricSpace

section ContinuousConstSMul

variable [Field 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

/--
theorem `Convex.combo_interior_closure_subset_interior` / 定理 `Convex.combo_interior_closure_subset_interior`

English:
theorem Convex.combo_interior_closure_subset_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
  proof: interior_smul₀ ha.ne' s ▸
    calc
      interior (a • s) + b • closure s subseteq interior (a • s) + closure (b • s) :=
        add_subset_add Subset.rfl (smul_closure_subset b s)
      _ = interior (a • s) + b • s := by rw [isOpen_interior.add_closure (b • s)]
      _ subseteq interior (a • s + b • s) := subset_interior_add_left
_ subseteq interior s := interior_mono hs.set_combo_subset ha.le hb hab

中文:
定理 凸.combo_interior_closure_subset_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {a b : 𝕜}
  证明: interior_smul₀ ha.ne' s ▸
    calc
      interior (a • s) + b • closure s subseteq interior (a • s) + closure (b • s) :=
        add_subset_add Subset.rfl (smul_closure_subset b s)
      _ = interior (a • s) + b • s := by rw [isOpen_interior.add_closure (b • s)]
      _ subseteq interior (a • s + b • s) := subset_interior_add_left
_ subseteq interior s := interior_mono hs.set_combo_subset ha.le hb hab

Depends on / 依赖: Subset, Subset.rfl, add_closure, add_subset_add, closure, ha.le, ha.ne, hs.set_combo_subset, interior, interior_mono, isOpen_interior, isOpen_interior.add_closure, set_combo_subset, smul_closure_subset, subset_interior_add_left, subseteq
-/
theorem Convex.combo_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 <= b) (hab : a + b = 1) : a • interior s + b • closure s subseteq interior s :=
  interior_smul₀ ha.ne' s ▸
    calc
      interior (a • s) + b • closure s subseteq interior (a • s) + closure (b • s) :=
        add_subset_add Subset.rfl (smul_closure_subset b s)
      _ = interior (a • s) + b • s := by rw [isOpen_interior.add_closure (b • s)]
      _ subseteq interior (a • s + b • s) := subset_interior_add_left
_ subseteq interior s := interior_mono hs.set_combo_subset ha.le hb hab

/--
theorem `Convex.combo_interior_self_subset_interior` / 定理 `Convex.combo_interior_self_subset_interior`

English:
theorem Convex.combo_interior_self_subset_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
  proof: calc
    a • interior s + b • s subseteq a • interior s + b • closure s :=
add_subset_add Subset.rfl image_mono subset_closure
    _ subseteq interior s := hs.combo_interior_closure_subset_interior ha hb hab

中文:
定理 凸.combo_interior_self_subset_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {a b : 𝕜}
  证明: calc
    a • interior s + b • s subseteq a • interior s + b • closure s :=
add_subset_add Subset.rfl image_mono subset_closure
    _ subseteq interior s := hs.combo_interior_closure_subset_interior ha hb hab

Depends on / 依赖: Subset, Subset.rfl, add_subset_add, closure, combo_interior_closure_subset_interior, hs.combo_interior_closure_subset_interior, image_mono, interior, subset_closure, subseteq
-/
theorem Convex.combo_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 <= b) (hab : a + b = 1) : a • interior s + b • s subseteq interior s :=
  calc
    a • interior s + b • s subseteq a • interior s + b • closure s :=
add_subset_add Subset.rfl image_mono subset_closure
    _ subseteq interior s := hs.combo_interior_closure_subset_interior ha hb hab

/--
theorem `Convex.combo_closure_interior_subset_interior` / 定理 `Convex.combo_closure_interior_subset_interior`

English:
theorem Convex.combo_closure_interior_subset_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
  proof: by
  rw [add_comm]
  exact hs.combo_interior_closure_subset_interior hb ha (add_comm a b ▸ hab)

中文:
定理 凸.combo_closure_interior_subset_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {a b : 𝕜}
  证明: by
  rw [add_comm]
  exact hs.combo_interior_closure_subset_interior hb ha (add_comm a b ▸ hab)

Depends on / 依赖: add_comm, combo_interior_closure_subset_interior, hs.combo_interior_closure_subset_interior
-/
theorem Convex.combo_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 <= a) (hb : 0 < b) (hab : a + b = 1) : a • closure s + b • interior s subseteq interior s := by
  rw [add_comm]
  exact hs.combo_interior_closure_subset_interior hb ha (add_comm a b ▸ hab)

/--
theorem `Convex.combo_self_interior_subset_interior` / 定理 `Convex.combo_self_interior_subset_interior`

English:
theorem Convex.combo_self_interior_subset_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
  proof: by
  rw [add_comm]
  exact hs.combo_interior_self_subset_interior hb ha (add_comm a b ▸ hab)

中文:
定理 凸.combo_self_interior_subset_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {a b : 𝕜}
  证明: by
  rw [add_comm]
  exact hs.combo_interior_self_subset_interior hb ha (add_comm a b ▸ hab)

Depends on / 依赖: add_comm, combo_interior_self_subset_interior, hs.combo_interior_self_subset_interior
-/
theorem Convex.combo_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 <= a) (hb : 0 < b) (hab : a + b = 1) : a • s + b • interior s subseteq interior s := by
  rw [add_comm]
  exact hs.combo_interior_self_subset_interior hb ha (add_comm a b ▸ hab)

/--
theorem `Convex.combo_interior_closure_mem_interior` / 定理 `Convex.combo_interior_closure_mem_interior`

English:
theorem Convex.combo_interior_closure_mem_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E}
  proof: hs.combo_interior_closure_subset_interior ha hb hab
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

中文:
定理 凸.combo_interior_closure_mem_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E}
  证明: hs.combo_interior_closure_subset_interior ha hb hab
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

Depends on / 依赖: add_mem_add, combo_interior_closure_subset_interior, hs.combo_interior_closure_subset_interior, smul_mem_smul_set
-/
theorem Convex.combo_interior_closure_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x in interior s) (hy : y in closure s) {a b : 𝕜} (ha : 0 < a) (hb : 0 <= b)
    (hab : a + b = 1) : a • x + b • y in interior s :=
hs.combo_interior_closure_subset_interior ha hb hab
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

/--
theorem `Convex.combo_interior_self_mem_interior` / 定理 `Convex.combo_interior_self_mem_interior`

English:
theorem Convex.combo_interior_self_mem_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E}
  proof: hs.combo_interior_closure_mem_interior hx (subset_closure hy) ha hb hab

中文:
定理 凸.combo_interior_self_mem_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E}
  证明: hs.combo_interior_closure_mem_interior hx (subset_closure hy) ha hb hab

Depends on / 依赖: combo_interior_closure_mem_interior, hs.combo_interior_closure_mem_interior, subset_closure
-/
theorem Convex.combo_interior_self_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x in interior s) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 <= b) (hab : a + b = 1) :
    a • x + b • y in interior s :=
  hs.combo_interior_closure_mem_interior hx (subset_closure hy) ha hb hab

/--
theorem `Convex.combo_closure_interior_mem_interior` / 定理 `Convex.combo_closure_interior_mem_interior`

English:
theorem Convex.combo_closure_interior_mem_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E}
  proof: hs.combo_closure_interior_subset_interior ha hb hab
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

中文:
定理 凸.combo_closure_interior_mem_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E}
  证明: hs.combo_closure_interior_subset_interior ha hb hab
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

Depends on / 依赖: add_mem_add, combo_closure_interior_subset_interior, hs.combo_closure_interior_subset_interior, smul_mem_smul_set
-/
theorem Convex.combo_closure_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x in closure s) (hy : y in interior s) {a b : 𝕜} (ha : 0 <= a) (hb : 0 < b)
    (hab : a + b = 1) : a • x + b • y in interior s :=
hs.combo_closure_interior_subset_interior ha hb hab
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

/--
theorem `Convex.combo_self_interior_mem_interior` / 定理 `Convex.combo_self_interior_mem_interior`

English:
theorem Convex.combo_self_interior_mem_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in s)
  proof: hs.combo_closure_interior_mem_interior (subset_closure hx) hy ha hb hab

中文:
定理 凸.combo_self_interior_mem_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E} (hx : x in s)
  证明: hs.combo_closure_interior_mem_interior (subset_closure hx) hy ha hb hab

Depends on / 依赖: combo_closure_interior_mem_interior, hs.combo_closure_interior_mem_interior, subset_closure
-/
theorem Convex.combo_self_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in s)
    (hy : y in interior s) {a b : 𝕜} (ha : 0 <= a) (hb : 0 < b) (hab : a + b = 1) :
    a • x + b • y in interior s :=
  hs.combo_closure_interior_mem_interior (subset_closure hx) hy ha hb hab

/--
theorem `Convex.openSegment_interior_closure_subset_interior` / 定理 `Convex.openSegment_interior_closure_subset_interior`

English:
theorem Convex.openSegment_interior_closure_subset_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E}
  proof: by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_interior_closure_mem_interior hx hy ha hb.le hab

中文:
定理 凸.openSegment_interior_closure_subset_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E}
  证明: by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_interior_closure_mem_interior hx hy ha hb.le hab

Depends on / 依赖: combo_interior_closure_mem_interior, hb.le, hs.combo_interior_closure_mem_interior
-/
theorem Convex.openSegment_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x in interior s) (hy : y in closure s) : openSegment 𝕜 x y subseteq interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_interior_closure_mem_interior hx hy ha hb.le hab

/--
theorem `Convex.openSegment_interior_self_subset_interior` / 定理 `Convex.openSegment_interior_self_subset_interior`

English:
theorem Convex.openSegment_interior_self_subset_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E}
  proof: hs.openSegment_interior_closure_subset_interior hx (subset_closure hy)

中文:
定理 凸.openSegment_interior_self_subset_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E}
  证明: hs.openSegment_interior_closure_subset_interior hx (subset_closure hy)

Depends on / 依赖: hs.openSegment_interior_closure_subset_interior, openSegment_interior_closure_subset_interior, subset_closure
-/
theorem Convex.openSegment_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x in interior s) (hy : y in s) : openSegment 𝕜 x y subseteq interior s :=
  hs.openSegment_interior_closure_subset_interior hx (subset_closure hy)

/--
theorem `Convex.openSegment_closure_interior_subset_interior` / 定理 `Convex.openSegment_closure_interior_subset_interior`

English:
theorem Convex.openSegment_closure_interior_subset_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E}
  proof: by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_closure_interior_mem_interior hx hy ha.le hb hab

中文:
定理 凸.openSegment_closure_interior_subset_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E}
  证明: by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_closure_interior_mem_interior hx hy ha.le hb hab

Depends on / 依赖: combo_closure_interior_mem_interior, ha.le, hs.combo_closure_interior_mem_interior
-/
theorem Convex.openSegment_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x in closure s) (hy : y in interior s) : openSegment 𝕜 x y subseteq interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_closure_interior_mem_interior hx hy ha.le hb hab

/--
theorem `Convex.openSegment_self_interior_subset_interior` / 定理 `Convex.openSegment_self_interior_subset_interior`

English:
theorem Convex.openSegment_self_interior_subset_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E}
  proof: hs.openSegment_closure_interior_subset_interior (subset_closure hx) hy

中文:
定理 凸.openSegment_self_interior_subset_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E}
  证明: hs.openSegment_closure_interior_subset_interior (subset_closure hx) hy

Depends on / 依赖: hs.openSegment_closure_interior_subset_interior, openSegment_closure_interior_subset_interior, subset_closure
-/
theorem Convex.openSegment_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x in s) (hy : y in interior s) : openSegment 𝕜 x y subseteq interior s :=
  hs.openSegment_closure_interior_subset_interior (subset_closure hx) hy

section

variable [AddRightMono 𝕜]

/--
theorem `Convex.add_smul_sub_mem_interior'` / 定理 `Convex.add_smul_sub_mem_interior'`

English:
theorem Convex.add_smul_sub_mem_interior'
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E}
  proof: by
  simpa only [sub_smul, smul_sub, one_smul, add_sub, add_comm] using
    hs.combo_interior_closure_mem_interior hy hx ht.1 (sub_nonneg.mpr ht.2)
      (add_sub_cancel _ _)

中文:
定理 凸.add_smul_sub_mem_interior'
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E}
  证明: by
  simpa only [sub_smul, smul_sub, one_smul, add_sub, add_comm] using
    hs.combo_interior_closure_mem_interior hy hx ht.1 (sub_nonneg.mpr ht.2)
      (add_sub_cancel _ _)

Depends on / 依赖: add_comm, add_sub, add_sub_cancel, combo_interior_closure_mem_interior, hs.combo_interior_closure_mem_interior, one_smul, smul_sub, sub_nonneg, sub_nonneg.mpr, sub_smul
-/
theorem Convex.add_smul_sub_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x in closure s) (hy : y in interior s) {t : 𝕜} (ht : t in Ioc (0 : 𝕜) 1) :
    x + t • (y - x) in interior s := by
  simpa only [sub_smul, smul_sub, one_smul, add_sub, add_comm] using
    hs.combo_interior_closure_mem_interior hy hx ht.1 (sub_nonneg.mpr ht.2)
      (add_sub_cancel _ _)

/--
theorem `Convex.add_smul_sub_mem_interior` / 定理 `Convex.add_smul_sub_mem_interior`

English:
theorem Convex.add_smul_sub_mem_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in s)
  proof: hs.add_smul_sub_mem_interior' (subset_closure hx) hy ht

中文:
定理 凸.add_smul_sub_mem_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E} (hx : x in s)
  证明: hs.add_smul_sub_mem_interior' (subset_closure hx) hy ht

Depends on / 依赖: add_smul_sub_mem_interior, hs.add_smul_sub_mem_interior, subset_closure
-/
theorem Convex.add_smul_sub_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in s)
    (hy : y in interior s) {t : 𝕜} (ht : t in Ioc (0 : 𝕜) 1) : x + t • (y - x) in interior s :=
  hs.add_smul_sub_mem_interior' (subset_closure hx) hy ht

/--
theorem `Convex.add_smul_mem_interior'` / 定理 `Convex.add_smul_mem_interior'`

English:
theorem Convex.add_smul_mem_interior'
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in closure s)
  proof: by
  simpa only [add_sub_cancel_left] using hs.add_smul_sub_mem_interior' hx hy ht

中文:
定理 凸.add_smul_mem_interior'
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E} (hx : x in closure s)
  证明: by
  simpa only [add_sub_cancel_left] using hs.add_smul_sub_mem_interior' hx hy ht

Depends on / 依赖: add_smul_sub_mem_interior, add_sub_cancel_left, hs.add_smul_sub_mem_interior
-/
theorem Convex.add_smul_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in closure s)
    (hy : x + y in interior s) {t : 𝕜} (ht : t in Ioc (0 : 𝕜) 1) : x + t • y in interior s := by
  simpa only [add_sub_cancel_left] using hs.add_smul_sub_mem_interior' hx hy ht

/--
theorem `Convex.add_smul_mem_interior` / 定理 `Convex.add_smul_mem_interior`

English:
theorem Convex.add_smul_mem_interior
  statement: {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in s)
  proof: hs.add_smul_mem_interior' (subset_closure hx) hy ht

中文:
定理 凸.add_smul_mem_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s) {x y : E} (hx : x in s)
  证明: hs.add_smul_mem_interior' (subset_closure hx) hy ht

Depends on / 依赖: add_smul_mem_interior, hs.add_smul_mem_interior, subset_closure
-/
theorem Convex.add_smul_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in s)
    (hy : x + y in interior s) {t : 𝕜} (ht : t in Ioc (0 : 𝕜) 1) : x + t • y in interior s :=
  hs.add_smul_mem_interior' (subset_closure hx) hy ht

end

/--
theorem `Convex.interior` / 定理 `Convex.interior`

English:
theorem Convex.interior
  given: [ZeroLEOneClass 𝕜] {s : Set E} (hs : Convex 𝕜 s)
  proof: convex_iff_openSegment_subset.mpr fun _ hx _ hy =>
    hs.openSegment_closure_interior_subset_interior (interior_subset_closure hx) hy

中文:
定理 凸.interior
  条件: [ZeroLEOne类 𝕜] {s : 集合 E} (hs : 凸 𝕜 s)
  证明: convex_iff_openSegment_subset.mpr fun _ hx _ hy =>
    hs.openSegment_closure_interior_subset_interior (interior_subset_closure hx) hy
-/
protected theorem Convex.interior [ZeroLEOneClass 𝕜] {s : Set E} (hs : Convex 𝕜 s) :
    Convex 𝕜 (interior s) :=
  convex_iff_openSegment_subset.mpr fun _ hx _ hy =>
    hs.openSegment_closure_interior_subset_interior (interior_subset_closure hx) hy

/--
theorem `Convex.closure` / 定理 `Convex.closure`

English:
theorem Convex.closure
  given: {s : Set E} (hs : Convex 𝕜 s)
  statement: Convex 𝕜 (closure s)
  proof: fun x hx y hy a b ha hb hab =>
  let f : E -> E -> E := fun x' y' => a • x' + b • y'
  have hf : Continuous (Function.uncurry f) :=
    (continuous_fst.const_smul _).add (continuous_snd.const_smul _)
  show f x y in closure s from map_mem_closure₂ hf hx hy fun _ hx' _ hy' => hs hx' hy' ha hb hab

中文:
定理 凸.closure
  条件: {s : 集合 E} (hs : 凸 𝕜 s)
  结论: 凸 𝕜 (closure s)
  证明: fun x hx y hy a b ha hb hab =>
  let f : E -> E -> E := fun x' y' => a • x' + b • y'
  have hf : Continuous (Function.uncurry f) :=
    (continuous_fst.const_smul _).add (continuous_snd.const_smul _)
  show f x y in closure s from map_mem_closure₂ hf hx hy fun _ hx' _ hy' => hs hx' hy' ha hb hab
-/
protected theorem Convex.closure {s : Set E} (hs : Convex 𝕜 s) : Convex 𝕜 (closure s) :=
  fun x hx y hy a b ha hb hab =>
  let f : E -> E -> E := fun x' y' => a • x' + b • y'
  have hf : Continuous (Function.uncurry f) :=
    (continuous_fst.const_smul _).add (continuous_snd.const_smul _)
  show f x y in closure s from map_mem_closure₂ hf hx hy fun _ hx' _ hy' => hs hx' hy' ha hb hab

/--
lemma `convexHull_interior_subset` / 引理 `convexHull_interior_subset`

English:
lemma convexHull_interior_subset
  given: [ZeroLEOneClass 𝕜] (s : Set E)
  proof: convexHull_min (interior_mono <| subset_convexHull 𝕜 s) (convex_convexHull 𝕜 s).interior

中文:
引理 convexHull_interior_subset
  条件: [ZeroLEOne类 𝕜] (s : 集合 E)
  证明: convexHull_min (interior_mono <| subset_convexHull 𝕜 s) (convex_convexHull 𝕜 s).interior

Depends on / 依赖: convexHull_min, convex_convexHull, interior, interior_mono, subset_convexHull
-/
lemma convexHull_interior_subset [ZeroLEOneClass 𝕜] (s : Set E) :
    convexHull 𝕜 (interior s) subseteq interior (convexHull 𝕜 s) :=
  convexHull_min (interior_mono <| subset_convexHull 𝕜 s) (convex_convexHull 𝕜 s).interior

/--
theorem `IsOpen.convexHull` / 定理 `IsOpen.convexHull`

English:
theorem IsOpen.convexHull
  given: [ZeroLEOneClass 𝕜] {s : Set E} (hs : IsOpen s)
  proof: by
  simpa [← subset_interior_iff_isOpen, hs.interior_eq] using convexHull_interior_subset s

中文:
定理 是开集.convexHull
  条件: [ZeroLEOne类 𝕜] {s : 集合 E} (hs : 是开集 s)
  证明: by
  simpa [← subset_interior_iff_isOpen, hs.interior_eq] using convexHull_interior_subset s
-/
protected theorem IsOpen.convexHull [ZeroLEOneClass 𝕜] {s : Set E} (hs : IsOpen s) :
    IsOpen (convexHull 𝕜 s) := by
  simpa [← subset_interior_iff_isOpen, hs.interior_eq] using convexHull_interior_subset s

end ContinuousConstSMul

section ContinuousConstSMul

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

open AffineMap

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Convex.strictConvex'` / 定理 `Convex.strictConvex'`

English:
theorem Convex.strictConvex'
  statement: {s : Set E} (hs : Convex 𝕜 s)
  proof: by
  refine strictConvex_iff_openSegment_subset.2 ?_
  intro x hx y hy hne
  by_cases hx' : x in interior s
  · exact hs.openSegment_interior_self_subset_interior hx' hy
  by_cases hy' : y in interior s
  · exact hs.openSegment_self_interior_subset_interior hx hy'
  rcases h ⟨hx, hx'⟩ ⟨hy, hy'⟩ hne with ⟨c, hc⟩
  refine (openSegment_subset_union x y ⟨c, rfl⟩).trans
    (insert_subset_iff.2 ⟨hc, union_subset ?_ ?_⟩)
  exacts [hs.openSegment_self_interior_subset_interior hx hc,
    hs.openSegment_interior_self_subset_interior hc hy]

中文:
定理 凸.strictConvex'
  结论: {s : 集合 E} (hs : 凸 𝕜 s)
  证明: by
  refine strictConvex_iff_openSegment_subset.2 ?_
  intro x hx y hy hne
  by_cases hx' : x in interior s
  · exact hs.openSegment_interior_self_subset_interior hx' hy
  by_cases hy' : y in interior s
  · exact hs.openSegment_self_interior_subset_interior hx hy'
  rcases h ⟨hx, hx'⟩ ⟨hy, hy'⟩ hne with ⟨c, hc⟩
  refine (openSegment_subset_union x y ⟨c, rfl⟩).trans
    (insert_subset_iff.2 ⟨hc, union_subset ?_ ?_⟩)
  exacts [hs.openSegment_self_interior_subset_interior hx hc,
    hs.openSegment_interior_self_subset_interior hc hy]
-/
protected theorem Convex.strictConvex' {s : Set E} (hs : Convex 𝕜 s)
    (h : (s \ interior s).Pairwise fun x y => exists c : 𝕜, lineMap x y c in interior s) :
    StrictConvex 𝕜 s := by
  refine strictConvex_iff_openSegment_subset.2 ?_
  intro x hx y hy hne
  by_cases hx' : x in interior s
  · exact hs.openSegment_interior_self_subset_interior hx' hy
  by_cases hy' : y in interior s
  · exact hs.openSegment_self_interior_subset_interior hx hy'
  rcases h ⟨hx, hx'⟩ ⟨hy, hy'⟩ hne with ⟨c, hc⟩
  refine (openSegment_subset_union x y ⟨c, rfl⟩).trans
    (insert_subset_iff.2 ⟨hc, union_subset ?_ ?_⟩)
  exacts [hs.openSegment_self_interior_subset_interior hx hc,
    hs.openSegment_interior_self_subset_interior hc hy]

/--
theorem `Convex.strictConvex` / 定理 `Convex.strictConvex`

English:
theorem Convex.strictConvex
  statement: {s : Set E} (hs : Convex 𝕜 s)
  proof: by
refine hs.strictConvex' h.imp_on fun x hx y hy _ => ?_
  simp only [segment_eq_image_lineMap, ← self_sdiff_frontier]
  rintro ⟨_, ⟨⟨c, hc, rfl⟩, hcs⟩⟩
  refine ⟨c, hs.segment_subset hx.1 hy.1 ?_, hcs⟩
  exact lineMap_mem_segment 𝕜 x y hc

中文:
定理 凸.strictConvex
  结论: {s : 集合 E} (hs : 凸 𝕜 s)
  证明: by
refine hs.strictConvex' h.imp_on fun x hx y hy _ => ?_
  simp only [segment_eq_image_lineMap, ← self_sdiff_frontier]
  rintro ⟨_, ⟨⟨c, hc, rfl⟩, hcs⟩⟩
  refine ⟨c, hs.segment_subset hx.1 hy.1 ?_, hcs⟩
  exact lineMap_mem_segment 𝕜 x y hc
-/
protected theorem Convex.strictConvex {s : Set E} (hs : Convex 𝕜 s)
    (h : (s \ interior s).Pairwise fun x y => ([x -[𝕜] y] \ frontier s).Nonempty) :
    StrictConvex 𝕜 s := by
refine hs.strictConvex' h.imp_on fun x hx y hy _ => ?_
  simp only [segment_eq_image_lineMap, ← self_sdiff_frontier]
  rintro ⟨_, ⟨⟨c, hc, rfl⟩, hcs⟩⟩
  refine ⟨c, hs.segment_subset hx.1 hy.1 ?_, hcs⟩
  exact lineMap_mem_segment 𝕜 x y hc

end ContinuousConstSMul

section ContinuousSMul

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [ContinuousSMul 𝕜 E]

/--
theorem `Convex.closure_interior_eq_closure_of_nonempty_interior` / 定理 `Convex.closure_interior_eq_closure_of_nonempty_interior`

English:
theorem Convex.closure_interior_eq_closure_of_nonempty_interior
  statement: {s : Set E} (hs : Convex 𝕜 s)
  proof: subset_antisymm (closure_mono interior_subset)
    fun _ h => closure_mono (hs.openSegment_interior_closure_subset_interior hs'.choose_spec h)
      (segment_subset_closure_openSegment (right_mem_segment ..))

中文:
定理 凸.closure_interior_eq_closure_of_nonempty_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s)
  证明: subset_antisymm (closure_mono interior_subset)
    fun _ h => closure_mono (hs.openSegment_interior_closure_subset_interior hs'.choose_spec h)
      (segment_subset_closure_openSegment (right_mem_segment ..))

Depends on / 依赖: choose_spec, closure_mono, hs.openSegment_interior_closure_subset_interior, interior_subset, openSegment_interior_closure_subset_interior, right_mem_segment, segment_subset_closure_openSegment, subset_antisymm
-/
theorem Convex.closure_interior_eq_closure_of_nonempty_interior {s : Set E} (hs : Convex 𝕜 s)
    (hs' : (interior s).Nonempty) : closure (interior s) = closure s :=
  subset_antisymm (closure_mono interior_subset)
    fun _ h => closure_mono (hs.openSegment_interior_closure_subset_interior hs'.choose_spec h)
      (segment_subset_closure_openSegment (right_mem_segment ..))

/--
theorem `Convex.interior_closure_eq_interior_of_nonempty_interior` / 定理 `Convex.interior_closure_eq_interior_of_nonempty_interior`

English:
theorem Convex.interior_closure_eq_interior_of_nonempty_interior
  statement: {s : Set E} (hs : Convex 𝕜 s)
  proof: by
  refine subset_antisymm ?_ (interior_mono subset_closure)
  intro y hy
  rcases hs' with ⟨x, hx⟩
  have h := AffineMap.lineMap_apply_one (k := 𝕜) x y
.eventually_mem obtain ⟨t, ht1, ht⟩ := AffineMap.lineMap_continuous.tendsto' _ _ h
.exists_gt (mem_interior_iff_mem_nhds.1 hy)
  apply hs.openSegment_interior_closure_subset_interior hx ht
  nth_rw 1 [← AffineMap.lineMap_apply_zero (k := 𝕜) x y, ← image_openSegment]
  exact ⟨1, Ioo_subset_openSegment ⟨zero_lt_one, ht1⟩, h⟩

中文:
定理 凸.interior_closure_eq_interior_of_nonempty_interior
  结论: {s : 集合 E} (hs : 凸 𝕜 s)
  证明: by
  refine subset_antisymm ?_ (interior_mono subset_closure)
  intro y hy
  rcases hs' with ⟨x, hx⟩
  have h := AffineMap.lineMap_apply_one (k := 𝕜) x y
.eventually_mem obtain ⟨t, ht1, ht⟩ := AffineMap.lineMap_continuous.tendsto' _ _ h
.exists_gt (mem_interior_iff_mem_nhds.1 hy)
  apply hs.openSegment_interior_closure_subset_interior hx ht
  nth_rw 1 [← AffineMap.lineMap_apply_zero (k := 𝕜) x y, ← image_openSegment]
  exact ⟨1, Ioo_subset_openSegment ⟨zero_lt_one, ht1⟩, h⟩

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, AffineMap.lineMap_continuous.tendsto, Ioo_subset_openSegment, eventually_mem, exists_gt, hs.openSegment_interior_closure_subset_interior, image_openSegment, interior_mono, lineMap_apply_one, lineMap_apply_zero, lineMap_continuous, mem_interior_iff_mem_nhds, nth_rw, openSegment_interior_closure_subset_interior, subset_antisymm, subset_closure, tendsto, zero_lt_one
-/
theorem Convex.interior_closure_eq_interior_of_nonempty_interior {s : Set E} (hs : Convex 𝕜 s)
    (hs' : (interior s).Nonempty) : interior (closure s) = interior s := by
  refine subset_antisymm ?_ (interior_mono subset_closure)
  intro y hy
  rcases hs' with ⟨x, hx⟩
  have h := AffineMap.lineMap_apply_one (k := 𝕜) x y
.eventually_mem obtain ⟨t, ht1, ht⟩ := AffineMap.lineMap_continuous.tendsto' _ _ h
.exists_gt (mem_interior_iff_mem_nhds.1 hy)
  apply hs.openSegment_interior_closure_subset_interior hx ht
  nth_rw 1 [← AffineMap.lineMap_apply_zero (k := 𝕜) x y, ← image_openSegment]
  exact ⟨1, Ioo_subset_openSegment ⟨zero_lt_one, ht1⟩, h⟩

end ContinuousSMul

section TopologicalSpace

variable [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/--
theorem `convex_closed_sInter` / 定理 `convex_closed_sInter`

English:
theorem convex_closed_sInter
  given: {S : Set (Set E)} (h : forall s in S, Convex 𝕜 s ∧ IsClosed s)
  proof: ⟨fun _ hx => starConvex_sInter fun _ hs => (h _ hs).1 hx _ hs,
    isClosed_sInter fun _ hs => (h _ hs).2⟩

中文:
定理 convex_closed_s整数er
  条件: {S : 集合 (集合 E)} (h : 对任意 s in S, 凸 𝕜 s ∧ 是闭集 s)
  证明: ⟨fun _ hx => starConvex_sInter fun _ hs => (h _ hs).1 hx _ hs,
    isClosed_sInter fun _ hs => (h _ hs).2⟩

Depends on / 依赖: isClosed_sInter, starConvex_sInter
-/
theorem convex_closed_sInter {S : Set (Set E)} (h : forall s in S, Convex 𝕜 s ∧ IsClosed s) :
    Convex 𝕜 (⋂₀ S) ∧ IsClosed (⋂₀ S) :=
⟨fun _ hx => starConvex_sInter fun _ hs => (h _ hs).1 hx _ hs,
    isClosed_sInter fun _ hs => (h _ hs).2⟩

variable (𝕜) in
/-- The convex closed hull of a set `s` is the minimal convex closed set that includes `s`. -/
@[simps! isClosed]
/--
Definition of `closedConvexHull` / `closedConvexHull` 的定义

English:
definition closedConvexHull
  signature: : ClosureOperator (Set E)
  body: .ofCompletePred (fun s => Convex 𝕜 s ∧ IsClosed s)
  fun _ => convex_closed_sInter

中文:
定义 closedConvexHull
  签名: : 闭包算子 (集合 E)
  定义体: .ofCompletePred (fun s => Convex 𝕜 s ∧ IsClosed s)
  fun _ => convex_closed_sInter

Depends on / 依赖: Convex, IsClosed, ofCompletePred
-/
def closedConvexHull : ClosureOperator (Set E) := .ofCompletePred (fun s => Convex 𝕜 s ∧ IsClosed s)
  fun _ => convex_closed_sInter

/--
theorem `convex_closedConvexHull` / 定理 `convex_closedConvexHull`

English:
theorem convex_closedConvexHull
  given: {s : Set E}
  proof: ((closedConvexHull 𝕜).isClosed_closure s).1

中文:
定理 convex_closedConvexHull
  条件: {s : 集合 E}
  证明: ((closedConvexHull 𝕜).isClosed_closure s).1

Depends on / 依赖: closedConvexHull, isClosed_closure
-/
theorem convex_closedConvexHull {s : Set E} :
    Convex 𝕜 (closedConvexHull 𝕜 s) := ((closedConvexHull 𝕜).isClosed_closure s).1

/--
theorem `isClosed_closedConvexHull` / 定理 `isClosed_closedConvexHull`

English:
theorem isClosed_closedConvexHull
  given: {s : Set E}
  proof: ((closedConvexHull 𝕜).isClosed_closure s).2

中文:
定理 isClosed_closedConvexHull
  条件: {s : 集合 E}
  证明: ((closedConvexHull 𝕜).isClosed_closure s).2

Depends on / 依赖: closedConvexHull, isClosed_closure
-/
theorem isClosed_closedConvexHull {s : Set E} :
    IsClosed (closedConvexHull 𝕜 s) := ((closedConvexHull 𝕜).isClosed_closure s).2

/--
theorem `subset_closedConvexHull` / 定理 `subset_closedConvexHull`

English:
theorem subset_closedConvexHull
  given: {s : Set E}
  statement: s subseteq closedConvexHull 𝕜 s
  proof: (closedConvexHull 𝕜).le_closure s

中文:
定理 subset_closedConvexHull
  条件: {s : 集合 E}
  结论: s subseteq closedConvexHull 𝕜 s
  证明: (closedConvexHull 𝕜).le_closure s

Depends on / 依赖: closedConvexHull, le_closure
-/
theorem subset_closedConvexHull {s : Set E} : s subseteq closedConvexHull 𝕜 s :=
  (closedConvexHull 𝕜).le_closure s

/--
theorem `closure_subset_closedConvexHull` / 定理 `closure_subset_closedConvexHull`

English:
theorem closure_subset_closedConvexHull
  given: {s : Set E}
  statement: closure s subseteq closedConvexHull 𝕜 s
  proof: closure_minimal subset_closedConvexHull isClosed_closedConvexHull

中文:
定理 closure_subset_closedConvexHull
  条件: {s : 集合 E}
  结论: closure s subseteq closedConvexHull 𝕜 s
  证明: closure_minimal subset_closedConvexHull isClosed_closedConvexHull

Depends on / 依赖: closure_minimal, isClosed_closedConvexHull, subset_closedConvexHull
-/
theorem closure_subset_closedConvexHull {s : Set E} : closure s subseteq closedConvexHull 𝕜 s :=
  closure_minimal subset_closedConvexHull isClosed_closedConvexHull

/--
theorem `closedConvexHull_min` / 定理 `closedConvexHull_min`

English:
theorem closedConvexHull_min
  statement: {s t : Set E} (hst : s subseteq t) (h_conv : Convex 𝕜 t)
  proof: (closedConvexHull 𝕜).closure_min hst ⟨h_conv, h_closed⟩

中文:
定理 closedConvexHull_min
  结论: {s t : 集合 E} (hst : s subseteq t) (h_conv : 凸 𝕜 t)
  证明: (closedConvexHull 𝕜).closure_min hst ⟨h_conv, h_closed⟩

Depends on / 依赖: closedConvexHull, closure_min, h_closed, h_conv
-/
theorem closedConvexHull_min {s t : Set E} (hst : s subseteq t) (h_conv : Convex 𝕜 t)
    (h_closed : IsClosed t) : closedConvexHull 𝕜 s subseteq t :=
  (closedConvexHull 𝕜).closure_min hst ⟨h_conv, h_closed⟩

/--
theorem `convexHull_subset_closedConvexHull` / 定理 `convexHull_subset_closedConvexHull`

English:
theorem convexHull_subset_closedConvexHull
  given: {s : Set E}
  proof: convexHull_min subset_closedConvexHull convex_closedConvexHull

@[simp]

中文:
定理 convexHull_subset_closedConvexHull
  条件: {s : 集合 E}
  证明: convexHull_min subset_closedConvexHull convex_closedConvexHull

@[simp]

Depends on / 依赖: convexHull_min, convex_closedConvexHull, subset_closedConvexHull
-/
theorem convexHull_subset_closedConvexHull {s : Set E} :
    (convexHull 𝕜) s subseteq (closedConvexHull 𝕜) s :=
  convexHull_min subset_closedConvexHull convex_closedConvexHull

@[simp]
/--
theorem `closedConvexHull_closure_eq_closedConvexHull` / 定理 `closedConvexHull_closure_eq_closedConvexHull`

English:
theorem closedConvexHull_closure_eq_closedConvexHull
  given: {s : Set E}
  proof: subset_antisymm (by
    simpa using ((closedConvexHull 𝕜).monotone (closure_subset_closedConvexHull (𝕜 := 𝕜) (E := E))))
    ((closedConvexHull 𝕜).monotone subset_closure)

中文:
定理 closedConvexHull_closure_eq_closedConvexHull
  条件: {s : 集合 E}
  证明: subset_antisymm (by
    simpa using ((closedConvexHull 𝕜).monotone (closure_subset_closedConvexHull (𝕜 := 𝕜) (E := E))))
    ((closedConvexHull 𝕜).monotone subset_closure)

Depends on / 依赖: closedConvexHull, closure_subset_closedConvexHull, monotone, subset_antisymm, subset_closure
-/
theorem closedConvexHull_closure_eq_closedConvexHull {s : Set E} :
    closedConvexHull 𝕜 (closure s) = closedConvexHull 𝕜 s :=
  subset_antisymm (by
    simpa using ((closedConvexHull 𝕜).monotone (closure_subset_closedConvexHull (𝕜 := 𝕜) (E := E))))
    ((closedConvexHull 𝕜).monotone subset_closure)

end TopologicalSpace

section ContinuousConstSMul

variable [Field 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

/--
theorem `closedConvexHull_eq_closure_convexHull` / 定理 `closedConvexHull_eq_closure_convexHull`

English:
theorem closedConvexHull_eq_closure_convexHull
  given: {s : Set E}
  proof: subset_antisymm
  (closedConvexHull_min (subset_trans (subset_convexHull 𝕜 s) subset_closure)
    (Convex.closure (convex_convexHull 𝕜 s)) isClosed_closure)
  (closure_minimal convexHull_subset_closedConvexHull isClosed_closedConvexHull)

中文:
定理 closedConvexHull_eq_closure_convexHull
  条件: {s : 集合 E}
  证明: subset_antisymm
  (closedConvexHull_min (subset_trans (subset_convexHull 𝕜 s) subset_closure)
    (Convex.closure (convex_convexHull 𝕜 s)) isClosed_closure)
  (closure_minimal convexHull_subset_closedConvexHull isClosed_closedConvexHull)

Depends on / 依赖: subset_antisymm
-/
theorem closedConvexHull_eq_closure_convexHull {s : Set E} :
    closedConvexHull 𝕜 s = closure (convexHull 𝕜 s) := subset_antisymm
  (closedConvexHull_min (subset_trans (subset_convexHull 𝕜 s) subset_closure)
    (Convex.closure (convex_convexHull 𝕜 s)) isClosed_closure)
  (closure_minimal convexHull_subset_closedConvexHull isClosed_closedConvexHull)

end ContinuousConstSMul

section Compact
variable (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/--
theorem `Set.Finite.isCompact_convexHull` / 定理 `Set.Finite.isCompact_convexHull`

English:
theorem Set.Finite.isCompact_convexHull
  given: {s : Set E} (hs : s.Finite)
  proof: by
  rw [hs.convexHull_eq_image]
  let := hs.fintype
  exact (isCompact_stdSimplex 𝕜 s).image (LinearMap.continuous_on_pi _)

中文:
定理 集合.有限.isCompact_convexHull
  条件: {s : 集合 E} (hs : s.有限)
  证明: by
  rw [hs.convexHull_eq_image]
  let := hs.fintype
  exact (isCompact_stdSimplex 𝕜 s).image (LinearMap.continuous_on_pi _)

Depends on / 依赖: LinearMap, LinearMap.continuous_on_pi, LocallyConvexSpace, PolynormableSpace, continuous_on_pi, convexHull_eq_image, fintype, hs.convexHull_eq_image, hs.fintype, isCompact_stdSimplex
-/
theorem Set.Finite.isCompact_convexHull {s : Set E} (hs : s.Finite) :
    IsCompact (convexHull 𝕜 s) := by
  rw [hs.convexHull_eq_image]
  let := hs.fintype
  exact (isCompact_stdSimplex 𝕜 s).image (LinearMap.continuous_on_pi _)

/--
theorem `Set.Finite.isClosed_convexHull` / 定理 `Set.Finite.isClosed_convexHull`

English:
theorem Set.Finite.isClosed_convexHull
  given: [T2Space E] {s : Set E} (hs : s.Finite)
  proof: (hs.isCompact_convexHull 𝕜).isClosed

中文:
定理 集合.有限.isClosed_convexHull
  条件: [T2空间 E] {s : 集合 E} (hs : s.有限)
  证明: (hs.isCompact_convexHull 𝕜).isClosed

Depends on / 依赖: hs.isCompact_convexHull, isClosed, isCompact_convexHull
-/
theorem Set.Finite.isClosed_convexHull [T2Space E] {s : Set E} (hs : s.Finite) :
    IsClosed (convexHull 𝕜 s) :=
  (hs.isCompact_convexHull 𝕜).isClosed

end Compact

section ContinuousSMul
variable [AddCommGroup E] [Module Real E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul Real E]

open AffineMap

/--
theorem `Convex.closure_subset_image_homothety_interior_of_one_lt` / 定理 `Convex.closure_subset_image_homothety_interior_of_one_lt`

English:
theorem Convex.closure_subset_image_homothety_interior_of_one_lt
  statement: {s : Set E} (hs : Convex Real s)
  proof: by
  intro y hy
  have hne : t != 0 := (one_pos.trans ht).ne'
  refine
    ⟨homothety x t⁻¹ y, hs.openSegment_interior_closure_subset_interior hx hy ?_,
      (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t hne)).apply_symm_apply y⟩
  rw [openSegment_eq_image_lineMap]; rw [← inv_one]; rw [← inv_Ioi₀ (zero_lt_one' Real)]; rw [← image_inv_eq_inv]; rw [image_image]; rw [homothety_eq_lineMap]
  exact mem_image_of_mem _ ht

中文:
定理 凸.closure_subset_image_homothety_interior_of_one_lt
  结论: {s : 集合 E} (hs : 凸 实数 s)
  证明: by
  intro y hy
  have hne : t != 0 := (one_pos.trans ht).ne'
  refine
    ⟨homothety x t⁻¹ y, hs.openSegment_interior_closure_subset_interior hx hy ?_,
      (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t hne)).apply_symm_apply y⟩
  rw [openSegment_eq_image_lineMap]; rw [← inv_one]; rw [← inv_Ioi₀ (zero_lt_one' Real)]; rw [← image_inv_eq_inv]; rw [image_image]; rw [homothety_eq_lineMap]
  exact mem_image_of_mem _ ht

Depends on / 依赖: AffineEquiv, AffineEquiv.homothetyUnitsMulHom, Units.mk0, apply_symm_apply, homothety, homothetyUnitsMulHom, homothety_eq_lineMap, hs.openSegment_interior_closure_subset_interior, image_image, image_inv_eq_inv, inv_one, mem_image_of_mem, one_pos, one_pos.trans, openSegment_eq_image_lineMap, openSegment_interior_closure_subset_interior, zero_lt_one
-/
theorem Convex.closure_subset_image_homothety_interior_of_one_lt {s : Set E} (hs : Convex Real s)
    {x : E} (hx : x in interior s) (t : Real) (ht : 1 < t) :
    closure s subseteq homothety x t '' interior s := by
  intro y hy
  have hne : t != 0 := (one_pos.trans ht).ne'
  refine
    ⟨homothety x t⁻¹ y, hs.openSegment_interior_closure_subset_interior hx hy ?_,
      (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t hne)).apply_symm_apply y⟩
  rw [openSegment_eq_image_lineMap]; rw [← inv_one]; rw [← inv_Ioi₀ (zero_lt_one' Real)]; rw [← image_inv_eq_inv]; rw [image_image]; rw [homothety_eq_lineMap]
  exact mem_image_of_mem _ ht

/--
theorem `Convex.closure_subset_interior_image_homothety_of_one_lt` / 定理 `Convex.closure_subset_interior_image_homothety_of_one_lt`

English:
theorem Convex.closure_subset_interior_image_homothety_of_one_lt
  statement: {s : Set E} (hs : Convex Real s)
  proof: (hs.closure_subset_image_homothety_interior_of_one_lt hx t ht).trans
    (homothety_isOpenMap x t (one_pos.trans ht).ne').image_interior_subset _

中文:
定理 凸.closure_subset_interior_image_homothety_of_one_lt
  结论: {s : 集合 E} (hs : 凸 实数 s)
  证明: (hs.closure_subset_image_homothety_interior_of_one_lt hx t ht).trans
    (homothety_isOpenMap x t (one_pos.trans ht).ne').image_interior_subset _

Depends on / 依赖: closure_subset_image_homothety_interior_of_one_lt, homothety_isOpenMap, hs.closure_subset_image_homothety_interior_of_one_lt, image_interior_subset, one_pos, one_pos.trans
-/
theorem Convex.closure_subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex Real s)
    {x : E} (hx : x in interior s) (t : Real) (ht : 1 < t) :
    closure s subseteq interior (homothety x t '' s) :=
(hs.closure_subset_image_homothety_interior_of_one_lt hx t ht).trans
    (homothety_isOpenMap x t (one_pos.trans ht).ne').image_interior_subset _

/--
theorem `Convex.subset_interior_image_homothety_of_one_lt` / 定理 `Convex.subset_interior_image_homothety_of_one_lt`

English:
theorem Convex.subset_interior_image_homothety_of_one_lt
  statement: {s : Set E} (hs : Convex Real s) {x : E}
  proof: subset_closure.trans hs.closure_subset_interior_image_homothety_of_one_lt hx t ht

中文:
定理 凸.subset_interior_image_homothety_of_one_lt
  结论: {s : 集合 E} (hs : 凸 实数 s) {x : E}
  证明: subset_closure.trans hs.closure_subset_interior_image_homothety_of_one_lt hx t ht

Depends on / 依赖: closure_subset_interior_image_homothety_of_one_lt, hs.closure_subset_interior_image_homothety_of_one_lt, subset_closure, subset_closure.trans
-/
theorem Convex.subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex Real s) {x : E}
    (hx : x in interior s) (t : Real) (ht : 1 < t) : s subseteq interior (homothety x t '' s) :=
subset_closure.trans hs.closure_subset_interior_image_homothety_of_one_lt hx t ht

end ContinuousSMul

section LinearOrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]

open scoped Topology
open Filter

/--
theorem `Convex.nontrivial_iff_nonempty_interior` / 定理 `Convex.nontrivial_iff_nonempty_interior`

English:
theorem Convex.nontrivial_iff_nonempty_interior
  given: {s : Set 𝕜} (hs : Convex 𝕜 s)
  proof: by
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
have hs' := Nonempty.mono interior_mono hs.segment_subset hx hy
    rw [segment_eq_Icc']; rw [interior_Icc]; rw [nonempty_Ioo]; rw [inf_lt_sup] at hs'
    exact hs' h
  · rintro ⟨x, hx⟩
    rcases eq_singleton_or_nontrivial (interior_subset hx) with rfl | h
    · rw [interior_singleton] at hx
      exact hx.elim
    · exact h

中文:
定理 凸.nontrivial_iff_nonempty_interior
  条件: {s : 集合 𝕜} (hs : 凸 𝕜 s)
  证明: by
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
have hs' := Nonempty.mono interior_mono hs.segment_subset hx hy
    rw [segment_eq_Icc']; rw [interior_Icc]; rw [nonempty_Ioo]; rw [inf_lt_sup] at hs'
    exact hs' h
  · rintro ⟨x, hx⟩
    rcases eq_singleton_or_nontrivial (interior_subset hx) with rfl | h
    · rw [interior_singleton] at hx
      exact hx.elim
    · exact h

Depends on / 依赖: Nonempty, Nonempty.mono, eq_singleton_or_nontrivial, hs.segment_subset, hx.elim, inf_lt_sup, interior_Icc, interior_mono, interior_singleton, interior_subset, nonempty_Ioo, segment_eq_Icc, segment_subset
-/
theorem Convex.nontrivial_iff_nonempty_interior {s : Set 𝕜} (hs : Convex 𝕜 s) :
    s.Nontrivial ↔ (interior s).Nonempty := by
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
have hs' := Nonempty.mono interior_mono hs.segment_subset hx hy
    rw [segment_eq_Icc']; rw [interior_Icc]; rw [nonempty_Ioo]; rw [inf_lt_sup] at hs'
    exact hs' h
  · rintro ⟨x, hx⟩
    rcases eq_singleton_or_nontrivial (interior_subset hx) with rfl | h
    · rw [interior_singleton] at hx
      exact hx.elim
    · exact h

/--
lemma `Convex.Ioo_subset_of_mem_closure` / 引理 `Convex.Ioo_subset_of_mem_closure`

English:
lemma Convex.Ioo_subset_of_mem_closure
  statement: {s : Set 𝕜} (hs : Convex 𝕜 s) {a b : 𝕜}
  proof: by
  cases subsingleton_or_nontrivial s with
  | inl hs_sub =>
    simp only [subsingleton_coe] at hs_sub
    simp [hs_sub.closure has hbs]
  | inr h' =>
    simp only [nontrivial_coe_sort] at h'
    calc Ioo a b
    _ = interior (Ioo a b) := interior_Ioo.symm
_ subseteq interior (openSegment 𝕜 a b) := interior_mono Ioo_subset_openSegment
_ subseteq interior (closure s) := interior_mono hs.closure.openSegment_subset has hbs
_ = interior s := hs.interior_closure_eq_interior_of_nonempty_interior
      hs.nontrivial_iff_nonempty_interior.1 h'
    _ subseteq s := interior_subset

中文:
引理 凸.Ioo_subset_of_mem_closure
  结论: {s : 集合 𝕜} (hs : 凸 𝕜 s) {a b : 𝕜}
  证明: by
  cases subsingleton_or_nontrivial s with
  | inl hs_sub =>
    simp only [subsingleton_coe] at hs_sub
    simp [hs_sub.closure has hbs]
  | inr h' =>
    simp only [nontrivial_coe_sort] at h'
    calc Ioo a b
    _ = interior (Ioo a b) := interior_Ioo.symm
_ subseteq interior (openSegment 𝕜 a b) := interior_mono Ioo_subset_openSegment
_ subseteq interior (closure s) := interior_mono hs.closure.openSegment_subset has hbs
_ = interior s := hs.interior_closure_eq_interior_of_nonempty_interior
      hs.nontrivial_iff_nonempty_interior.1 h'
    _ subseteq s := interior_subset

Depends on / 依赖: Ioo_subset_openSegment, closure, hs.closure.openSegment_subset, hs.interior_closure_eq_interior_of_nonempty_interior, hs.nontrivial_iff_nonempty_, hs_sub, hs_sub.closure, interior, interior_Ioo, interior_Ioo.symm, interior_closure_eq_interior_of_nonempty_interior, interior_mono, nontrivial_coe_sort, nontrivial_iff_nonempty_, openSegment, openSegment_subset, subseteq, subsingleton_coe, subsingleton_or_nontrivial
-/
lemma Convex.Ioo_subset_of_mem_closure {s : Set 𝕜} (hs : Convex 𝕜 s) {a b : 𝕜}
    (has : a in closure s) (hbs : b in closure s) :
    Ioo a b subseteq s := by
  cases subsingleton_or_nontrivial s with
  | inl hs_sub =>
    simp only [subsingleton_coe] at hs_sub
    simp [hs_sub.closure has hbs]
  | inr h' =>
    simp only [nontrivial_coe_sort] at h'
    calc Ioo a b
    _ = interior (Ioo a b) := interior_Ioo.symm
_ subseteq interior (openSegment 𝕜 a b) := interior_mono Ioo_subset_openSegment
_ subseteq interior (closure s) := interior_mono hs.closure.openSegment_subset has hbs
_ = interior s := hs.interior_closure_eq_interior_of_nonempty_interior
      hs.nontrivial_iff_nonempty_interior.1 h'
    _ subseteq s := interior_subset

/--
lemma `Convex.nhdsWithin_inter_Iio_eq_nhdsLT` / 引理 `Convex.nhdsWithin_inter_Iio_eq_nhdsLT`

English:
lemma Convex.nhdsWithin_inter_Iio_eq_nhdsLT
  statement: {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
  proof: by
  obtain ⟨b, hbs, hba⟩ := h'
  refine nhdsWithin_inter_of_mem (mem_nhdsLT_iff_exists_Ioo_subset.2 ⟨b, hba, ?_⟩)
  exact hs.Ioo_subset_of_mem_closure (subset_closure hbs) has

中文:
引理 凸.nhdsWithin_inter_Iio_eq_nhdsLT
  结论: {s : 集合 𝕜} (hs : 凸 𝕜 s) {a : 𝕜}
  证明: by
  obtain ⟨b, hbs, hba⟩ := h'
  refine nhdsWithin_inter_of_mem (mem_nhdsLT_iff_exists_Ioo_subset.2 ⟨b, hba, ?_⟩)
  exact hs.Ioo_subset_of_mem_closure (subset_closure hbs) has

Depends on / 依赖: Ioo_subset_of_mem_closure, hs.Ioo_subset_of_mem_closure, mem_nhdsLT_iff_exists_Ioo_subset, nhdsWithin_inter_of_mem, subset_closure
-/
lemma Convex.nhdsWithin_inter_Iio_eq_nhdsLT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
    (has : a in closure s) (h' : (s inter Iio a).Nonempty) :
    𝓝[s inter Iio a] a = 𝓝[<] a := by
  obtain ⟨b, hbs, hba⟩ := h'
  refine nhdsWithin_inter_of_mem (mem_nhdsLT_iff_exists_Ioo_subset.2 ⟨b, hba, ?_⟩)
  exact hs.Ioo_subset_of_mem_closure (subset_closure hbs) has

/--
lemma `Convex.nhdsWithin_inter_Ioi_eq_nhdsGT` / 引理 `Convex.nhdsWithin_inter_Ioi_eq_nhdsGT`

English:
lemma Convex.nhdsWithin_inter_Ioi_eq_nhdsGT
  statement: {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
  proof: by
  obtain ⟨b, hbs, hba⟩ := h'
  refine nhdsWithin_inter_of_mem (mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨b, hba, ?_⟩)
  exact hs.Ioo_subset_of_mem_closure has (subset_closure hbs)

中文:
引理 凸.nhdsWithin_inter_Ioi_eq_nhdsGT
  结论: {s : 集合 𝕜} (hs : 凸 𝕜 s) {a : 𝕜}
  证明: by
  obtain ⟨b, hbs, hba⟩ := h'
  refine nhdsWithin_inter_of_mem (mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨b, hba, ?_⟩)
  exact hs.Ioo_subset_of_mem_closure has (subset_closure hbs)

Depends on / 依赖: Ioo_subset_of_mem_closure, hs.Ioo_subset_of_mem_closure, mem_nhdsGT_iff_exists_Ioo_subset, nhdsWithin_inter_of_mem, subset_closure
-/
lemma Convex.nhdsWithin_inter_Ioi_eq_nhdsGT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
    (has : a in closure s) (h' : (s inter Ioi a).Nonempty) :
    𝓝[s inter Ioi a] a = 𝓝[>] a := by
  obtain ⟨b, hbs, hba⟩ := h'
  refine nhdsWithin_inter_of_mem (mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨b, hba, ?_⟩)
  exact hs.Ioo_subset_of_mem_closure has (subset_closure hbs)

/--
lemma `Convex.nhdsWithin_sdiff_eq_nhdsNE` / 引理 `Convex.nhdsWithin_sdiff_eq_nhdsNE`

English:
lemma Convex.nhdsWithin_sdiff_eq_nhdsNE
  statement: {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
  proof: by
  rw [sdiff_eq]; rw [← Iio_union_Ioi]; rw [inter_union_distrib_left]; rw [nhdsWithin_union]; rw [nhdsWithin_union]
  simp [hs.nhdsWithin_inter_Ioi_eq_nhdsGT has h_Ioi, hs.nhdsWithin_inter_Iio_eq_nhdsLT has h_Iio]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsNE := Convex.nhdsWithin_sdiff_eq_nhdsNE

中文:
引理 凸.nhdsWithin_sdiff_eq_nhdsNE
  结论: {s : 集合 𝕜} (hs : 凸 𝕜 s) {a : 𝕜}
  证明: by
  rw [sdiff_eq]; rw [← Iio_union_Ioi]; rw [inter_union_distrib_left]; rw [nhdsWithin_union]; rw [nhdsWithin_union]
  simp [hs.nhdsWithin_inter_Ioi_eq_nhdsGT has h_Ioi, hs.nhdsWithin_inter_Iio_eq_nhdsLT has h_Iio]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsNE := Convex.nhdsWithin_sdiff_eq_nhdsNE

Depends on / 依赖: Iio_union_Ioi, h_Iio, h_Ioi, hs.nhdsWithin_inter_Iio_eq_nhdsLT, hs.nhdsWithin_inter_Ioi_eq_nhdsGT, inter_union_distrib_left, nhdsWithin_inter_Iio_eq_nhdsLT, nhdsWithin_inter_Ioi_eq_nhdsGT, nhdsWithin_union, sdiff_eq
-/
lemma Convex.nhdsWithin_sdiff_eq_nhdsNE {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
    (has : a in closure s) (h_Iio : (s inter Iio a).Nonempty) (h_Ioi : (s inter Ioi a).Nonempty) :
    𝓝[s \ {a}] a = 𝓝[!=] a := by
  rw [sdiff_eq]; rw [← Iio_union_Ioi]; rw [inter_union_distrib_left]; rw [nhdsWithin_union]; rw [nhdsWithin_union]
  simp [hs.nhdsWithin_inter_Ioi_eq_nhdsGT has h_Ioi, hs.nhdsWithin_inter_Iio_eq_nhdsLT has h_Iio]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsNE := Convex.nhdsWithin_sdiff_eq_nhdsNE

/--
lemma `Convex.nhdsWithin_sdiff_eq_nhdsLT` / 引理 `Convex.nhdsWithin_sdiff_eq_nhdsLT`

English:
lemma Convex.nhdsWithin_sdiff_eq_nhdsLT
  statement: {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
  proof: by
  rw [sdiff_eq]; rw [← Iio_union_Ioi]; rw [inter_union_distrib_left]; rw [nhdsWithin_union]
  simp [h_Ioi, hs.nhdsWithin_inter_Iio_eq_nhdsLT has h_Iio]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsLT := Convex.nhdsWithin_sdiff_eq_nhdsLT

中文:
引理 凸.nhdsWithin_sdiff_eq_nhdsLT
  结论: {s : 集合 𝕜} (hs : 凸 𝕜 s) {a : 𝕜}
  证明: by
  rw [sdiff_eq]; rw [← Iio_union_Ioi]; rw [inter_union_distrib_left]; rw [nhdsWithin_union]
  simp [h_Ioi, hs.nhdsWithin_inter_Iio_eq_nhdsLT has h_Iio]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsLT := Convex.nhdsWithin_sdiff_eq_nhdsLT

Depends on / 依赖: Iio_union_Ioi, h_Iio, h_Ioi, hs.nhdsWithin_inter_Iio_eq_nhdsLT, inter_union_distrib_left, nhdsWithin_inter_Iio_eq_nhdsLT, nhdsWithin_union, sdiff_eq
-/
lemma Convex.nhdsWithin_sdiff_eq_nhdsLT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
    (has : a in closure s) (h_Iio : (s inter Iio a).Nonempty) (h_Ioi : s inter Ioi a = ∅) :
    𝓝[s \ {a}] a = 𝓝[<] a := by
  rw [sdiff_eq]; rw [← Iio_union_Ioi]; rw [inter_union_distrib_left]; rw [nhdsWithin_union]
  simp [h_Ioi, hs.nhdsWithin_inter_Iio_eq_nhdsLT has h_Iio]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsLT := Convex.nhdsWithin_sdiff_eq_nhdsLT

/--
lemma `Convex.nhdsWithin_sdiff_eq_nhdsGT` / 引理 `Convex.nhdsWithin_sdiff_eq_nhdsGT`

English:
lemma Convex.nhdsWithin_sdiff_eq_nhdsGT
  statement: {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
  proof: by
  rw [sdiff_eq]; rw [← Iio_union_Ioi]; rw [inter_union_distrib_left]; rw [nhdsWithin_union]
  simp [h_Iio, hs.nhdsWithin_inter_Ioi_eq_nhdsGT has h_Ioi]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsGT := Convex.nhdsWithin_sdiff_eq_nhdsGT

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in

中文:
引理 凸.nhdsWithin_sdiff_eq_nhdsGT
  结论: {s : 集合 𝕜} (hs : 凸 𝕜 s) {a : 𝕜}
  证明: by
  rw [sdiff_eq]; rw [← Iio_union_Ioi]; rw [inter_union_distrib_left]; rw [nhdsWithin_union]
  simp [h_Iio, hs.nhdsWithin_inter_Ioi_eq_nhdsGT has h_Ioi]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsGT := Convex.nhdsWithin_sdiff_eq_nhdsGT

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in

Depends on / 依赖: Iio_union_Ioi, h_Iio, h_Ioi, hs.nhdsWithin_inter_Ioi_eq_nhdsGT, inter_union_distrib_left, nhdsWithin_inter_Ioi_eq_nhdsGT, nhdsWithin_union, sdiff_eq
-/
lemma Convex.nhdsWithin_sdiff_eq_nhdsGT {s : Set 𝕜} (hs : Convex 𝕜 s) {a : 𝕜}
    (has : a in closure s) (h_Iio : s inter Iio a = ∅) (h_Ioi : (s inter Ioi a).Nonempty) :
    𝓝[s \ {a}] a = 𝓝[>] a := by
  rw [sdiff_eq]; rw [← Iio_union_Ioi]; rw [inter_union_distrib_left]; rw [nhdsWithin_union]
  simp [h_Iio, hs.nhdsWithin_inter_Ioi_eq_nhdsGT has h_Ioi]

@[deprecated (since := "2026-06-03")]
alias Convex.nhdsWithin_diff_eq_nhdsGT := Convex.nhdsWithin_sdiff_eq_nhdsGT

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
/--
lemma `sdiff_singleton_eventually_mem_nhds_left` / 引理 `sdiff_singleton_eventually_mem_nhds_left`

English:
lemma sdiff_singleton_eventually_mem_nhds_left
  statement: {s : Set 𝕜} {a : 𝕜}
  proof: by
  rcases eq_empty_or_nonempty (s inter Iio a) with hs' | ⟨b, hbs, hba⟩
  · simp [hs']
  have : Ioo b a subseteq s := h b (subset_closure hbs)
  apply eventually_of_mem (U := Ioo b a) ?_ fun x hx => ?_
  · exact mem_nhdsWithin.2 ⟨Ioi b, isOpen_Ioi, hba, fun _ ⟨h₁, _, h₂⟩ => ⟨h₁, h₂⟩⟩
  · exact mem_nhds_iff.2 ⟨Ioo b a, subset_sdiff_singleton this right_notMem_Ioo, isOpen_Ioo, hx⟩

中文:
引理 sdiff_singleton_eventually_mem_nhds_left
  结论: {s : 集合 𝕜} {a : 𝕜}
  证明: by
  rcases eq_empty_or_nonempty (s inter Iio a) with hs' | ⟨b, hbs, hba⟩
  · simp [hs']
  have : Ioo b a subseteq s := h b (subset_closure hbs)
  apply eventually_of_mem (U := Ioo b a) ?_ fun x hx => ?_
  · exact mem_nhdsWithin.2 ⟨Ioi b, isOpen_Ioi, hba, fun _ ⟨h₁, _, h₂⟩ => ⟨h₁, h₂⟩⟩
  · exact mem_nhds_iff.2 ⟨Ioo b a, subset_sdiff_singleton this right_notMem_Ioo, isOpen_Ioo, hx⟩
-/
private lemma sdiff_singleton_eventually_mem_nhds_left {s : Set 𝕜} {a : 𝕜}
    (h : forall x in closure s, Ioo x a subseteq s) : forallᶠ (x : 𝕜) in 𝓝[s inter Iio a] a, s \ {a} in 𝓝 x := by
  rcases eq_empty_or_nonempty (s inter Iio a) with hs' | ⟨b, hbs, hba⟩
  · simp [hs']
  have : Ioo b a subseteq s := h b (subset_closure hbs)
  apply eventually_of_mem (U := Ioo b a) ?_ fun x hx => ?_
  · exact mem_nhdsWithin.2 ⟨Ioi b, isOpen_Ioi, hba, fun _ ⟨h₁, _, h₂⟩ => ⟨h₁, h₂⟩⟩
  · exact mem_nhds_iff.2 ⟨Ioo b a, subset_sdiff_singleton this right_notMem_Ioo, isOpen_Ioo, hx⟩

/--
theorem `Convex.sdiff_singleton_eventually_mem_nhds` / 定理 `Convex.sdiff_singleton_eventually_mem_nhds`

English:
theorem Convex.sdiff_singleton_eventually_mem_nhds
  given: {s : Set 𝕜} (hs : Convex 𝕜 s) (a : 𝕜)
  proof: by
  rcases eq_or_neBot (𝓝[s \ {a}] a) with h | has
  · rw [h]
    exact eventually_bot
  replace has := closure_mono sdiff_subset (mem_closure_iff_nhdsWithin_neBot.2 has)
  conv in 𝓝[s \ {a}] a => rw [sdiff_eq, ← Iio_union_Ioi, inter_union_distrib_left]
  rw [nhdsWithin_union]; rw [eventually_sup]
  exact ⟨sdiff_singleton_eventually_mem_nhds_left fun x hx => hs.Ioo_subset_of_mem_closure hx has,
    sdiff_singleton_eventually_mem_nhds_left (𝕜 := 𝕜ᵒᵈ) fun x hx z hz =>
      hs.Ioo_subset_of_mem_closure has hx hz.symm⟩

@[deprecated (since := "2026-06-03")]
alias Convex.diff_singleton_eventually_mem_nhds := Convex.sdiff_singleton_eventually_mem_nhds

中文:
定理 凸.sdiff_singleton_eventually_mem_nhds
  条件: {s : 集合 𝕜} (hs : 凸 𝕜 s) (a : 𝕜)
  证明: by
  rcases eq_or_neBot (𝓝[s \ {a}] a) with h | has
  · rw [h]
    exact eventually_bot
  replace has := closure_mono sdiff_subset (mem_closure_iff_nhdsWithin_neBot.2 has)
  conv in 𝓝[s \ {a}] a => rw [sdiff_eq, ← Iio_union_Ioi, inter_union_distrib_left]
  rw [nhdsWithin_union]; rw [eventually_sup]
  exact ⟨sdiff_singleton_eventually_mem_nhds_left fun x hx => hs.Ioo_subset_of_mem_closure hx has,
    sdiff_singleton_eventually_mem_nhds_left (𝕜 := 𝕜ᵒᵈ) fun x hx z hz =>
      hs.Ioo_subset_of_mem_closure has hx hz.symm⟩

@[deprecated (since := "2026-06-03")]
alias Convex.diff_singleton_eventually_mem_nhds := Convex.sdiff_singleton_eventually_mem_nhds

Depends on / 依赖: Iio_union_Ioi, Ioo_subset_of_mem_closure, closure_mono, eq_or_neBot, eventually_bot, eventually_sup, hs.Ioo_subset_of_mem_closure, hz.symm, inter_union_distrib_left, mem_closure_iff_nhdsWithin_neBot, nhdsWithin_union, replace, sdiff_eq, sdiff_singleton_eventually_mem_nhds_left, sdiff_subset
-/
theorem Convex.sdiff_singleton_eventually_mem_nhds {s : Set 𝕜} (hs : Convex 𝕜 s) (a : 𝕜) :
    forallᶠ x in 𝓝[s \ {a}] a, s \ {a} in 𝓝 x := by
  rcases eq_or_neBot (𝓝[s \ {a}] a) with h | has
  · rw [h]
    exact eventually_bot
  replace has := closure_mono sdiff_subset (mem_closure_iff_nhdsWithin_neBot.2 has)
  conv in 𝓝[s \ {a}] a => rw [sdiff_eq, ← Iio_union_Ioi, inter_union_distrib_left]
  rw [nhdsWithin_union]; rw [eventually_sup]
  exact ⟨sdiff_singleton_eventually_mem_nhds_left fun x hx => hs.Ioo_subset_of_mem_closure hx has,
    sdiff_singleton_eventually_mem_nhds_left (𝕜 := 𝕜ᵒᵈ) fun x hx z hz =>
      hs.Ioo_subset_of_mem_closure has hx hz.symm⟩

@[deprecated (since := "2026-06-03")]
alias Convex.diff_singleton_eventually_mem_nhds := Convex.sdiff_singleton_eventually_mem_nhds

end LinearOrderedField

namespace Affine.Simplex

variable {𝕜 V P : Type*}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [Module 𝕜 V] [ContinuousSMul 𝕜 V] [AddTorsor V P]
  [TopologicalSpace P] [IsTopologicalAddTorsor P]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isCompact_closedInterior` / 定理 `isCompact_closedInterior`

English:
theorem isCompact_closedInterior
  given: {n : Nat} (s : Simplex 𝕜 P n)
  statement: IsCompact s.closedInterior
  proof: by
  suffices IsCompact ((AffineEquiv.vaddConst 𝕜 (s.points 0)).symm.toAffineMap ''
      s.closedInterior) by
    apply (Homeomorph.vaddConst (s.points 0)).symm.isCompact_image.mp
    simpa
  rw [← s.closedInterior_map (AffineEquiv.injective _)]; rw [← convexHull_eq_closedInterior]
  exact (Set.finite_range _).isCompact_convexHull 𝕜

中文:
定理 isCompact_closed整数erior
  条件: {n : 自然数} (s : 单纯形 𝕜 P n)
  结论: 是紧集 s.closed整数erior
  证明: by
  suffices IsCompact ((AffineEquiv.vaddConst 𝕜 (s.points 0)).symm.toAffineMap ''
      s.closedInterior) by
    apply (Homeomorph.vaddConst (s.points 0)).symm.isCompact_image.mp
    simpa
  rw [← s.closedInterior_map (AffineEquiv.injective _)]; rw [← convexHull_eq_closedInterior]
  exact (Set.finite_range _).isCompact_convexHull 𝕜

Depends on / 依赖: AffineEquiv, AffineEquiv.injective, AffineEquiv.vaddConst, Homeomorph, Homeomorph.vaddConst, IsCompact, Set.finite_range, closedInterior, closedInterior_map, convexHull_eq_closedInterior, finite_range, injective, isCompact_convexHull, isCompact_image, points, s.closedInterior, s.closedInterior_map, s.points, symm.isCompact_image.mp, symm.toAffineMap
-/
theorem isCompact_closedInterior {n : Nat} (s : Simplex 𝕜 P n) : IsCompact s.closedInterior := by
  suffices IsCompact ((AffineEquiv.vaddConst 𝕜 (s.points 0)).symm.toAffineMap ''
      s.closedInterior) by
    apply (Homeomorph.vaddConst (s.points 0)).symm.isCompact_image.mp
    simpa
  rw [← s.closedInterior_map (AffineEquiv.injective _)]; rw [← convexHull_eq_closedInterior]
  exact (Set.finite_range _).isCompact_convexHull 𝕜

/--
theorem `isClosed_closedInterior` / 定理 `isClosed_closedInterior`

English:
theorem isClosed_closedInterior
  given: [T2Space P] {n : Nat} (s : Simplex 𝕜 P n)
  proof: s.isCompact_closedInterior.isClosed

中文:
定理 isClosed_closed整数erior
  条件: [T2空间 P] {n : 自然数} (s : 单纯形 𝕜 P n)
  证明: s.isCompact_closedInterior.isClosed

Depends on / 依赖: isClosed, isCompact_closedInterior, s.isCompact_closedInterior.isClosed
-/
theorem isClosed_closedInterior [T2Space P] {n : Nat} (s : Simplex 𝕜 P n) :
    IsClosed s.closedInterior :=
  s.isCompact_closedInterior.isClosed

end Affine.Simplex
