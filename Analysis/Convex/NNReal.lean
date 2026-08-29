/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.NNReal.Defs

/-!
# Specific lemmas about convexity over `ℝ≥0`

This file collects some specific results about convexity over the ring `ℝ≥0`.
Expand as needed.
-/

public section

open Set
open scoped NNReal

namespace NNReal

/--
lemma `Icc_subset_segment` / 引理 `Icc_subset_segment`

English:
lemma Icc_subset_segment
  given: {x y : Real>=0}
  proof: Nonneg.Icc_subset_segment

中文:
引理 Icc_subset_segment
  条件: {x y : 实数>=0}
  证明: Nonneg.Icc_subset_segment
-/
protected lemma Icc_subset_segment {x y : Real>=0} :
    Icc x y subseteq segment Real>=0 x y :=
  Nonneg.Icc_subset_segment

/--
lemma `segment_eq_Icc` / 引理 `segment_eq_Icc`

English:
lemma segment_eq_Icc
  given: {x y : Real>=0} (hxy : x <= y)
  proof: Nonneg.segment_eq_Icc hxy

中文:
引理 segment_eq_Icc
  条件: {x y : 实数>=0} (hxy : x <= y)
  证明: Nonneg.segment_eq_Icc hxy
-/
protected lemma segment_eq_Icc {x y : Real>=0} (hxy : x <= y) :
    segment Real>=0 x y = Icc x y :=
  Nonneg.segment_eq_Icc hxy

/--
lemma `segment_eq_uIcc` / 引理 `segment_eq_uIcc`

English:
lemma segment_eq_uIcc
  given: {x y : Real>=0}
  proof: Nonneg.segment_eq_uIcc

中文:
引理 segment_eq_uIcc
  条件: {x y : 实数>=0}
  证明: Nonneg.segment_eq_uIcc
-/
protected lemma segment_eq_uIcc {x y : Real>=0} :
    segment Real>=0 x y = uIcc x y :=
  Nonneg.segment_eq_uIcc

set_option backward.isDefEq.respectTransparency false in
/--
lemma `convex_iff` / 引理 `convex_iff`

English:
lemma convex_iff
  given: {M : Type*} [AddCommMonoid M] [Module Real M] {s : Set M}
  proof: by
  refine ⟨fun H => ?_, Convex.lift Real>=0⟩
  intro _ hx _ hy a b ha hb hab
  exact H hx hy (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) zero_le zero_le (by ext; simpa)

中文:
引理 convex_iff
  条件: {M : 类型} [加法交换幺半群 M] [模 实数 M] {s : 集合 M}
  证明: by
  refine ⟨fun H => ?_, Convex.lift Real>=0⟩
  intro _ hx _ hy a b ha hb hab
  exact H hx hy (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) zero_le zero_le (by ext; simpa)
-/
protected lemma convex_iff {M : Type*} [AddCommMonoid M] [Module Real M] {s : Set M} :
    Convex Real>=0 s ↔ Convex Real s := by
  refine ⟨fun H => ?_, Convex.lift Real>=0⟩
  intro _ hx _ hy a b ha hb hab
  exact H hx hy (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) zero_le zero_le (by ext; simpa)

end NNReal
