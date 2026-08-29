/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.EMetricSpace.Pi

/-!
# Diameters of sets in extended metric spaces

In this file we define the diameter of a set in the extended metric space
as an extended nonnegative real number.
-/

@[expose] public section

open Set Filter

open scoped Uniformity Topology Filter NNReal ENNReal Pointwise

variable {α X : Type*} {s t : Set X} {x y z : X}

namespace Metric

section PseudoEMetricSpace

variable [PseudoEMetricSpace X]

/--
Definition of `ediam` / `ediam` 的定义

English:
definition ediam
  signature: (s : Set X)
  body: ⨆ (x in s) (y in s), edist x y

中文:
定义 ediam
  签名: (s : 集合 X)
  定义体: ⨆ (x in s) (y in s), edist x y
-/
noncomputable def ediam (s : Set X) :=
  ⨆ (x in s) (y in s), edist x y

/--
theorem `ediam_eq_sSup` / 定理 `ediam_eq_sSup`

English:
theorem ediam_eq_sSup
  given: (s : Set X)
  statement: ediam s = sSup (image2 edist s s)
  proof: sSup_image2.symm

中文:
定理 ediam_eq_sSup
  条件: (s : 集合 X)
  结论: ediam s = sSup (image2 edist s s)
  证明: sSup_image2.symm

Depends on / 依赖: sSup_image2, sSup_image2.symm
-/
theorem ediam_eq_sSup (s : Set X) : ediam s = sSup (image2 edist s s) := sSup_image2.symm

/--
theorem `ediam_le_iff` / 定理 `ediam_le_iff`

English:
theorem ediam_le_iff
  given: {d : Real>=0∞}
  statement: ediam s <= d ↔ forall x in s, forall y in s, edist x y <= d
  proof: by
  simp only [ediam, iSup_le_iff]

中文:
定理 ediam_le_iff
  条件: {d : 实数>=0∞}
  结论: ediam s <= d ↔ 对任意 x in s, 对任意 y in s, edist x y <= d
  证明: by
  simp only [ediam, iSup_le_iff]

Depends on / 依赖: iSup_le_iff
-/
theorem ediam_le_iff {d : Real>=0∞} : ediam s <= d ↔ forall x in s, forall y in s, edist x y <= d := by
  simp only [ediam, iSup_le_iff]

/--
theorem `ediam_image_le_iff` / 定理 `ediam_image_le_iff`

English:
theorem ediam_image_le_iff
  given: {d : Real>=0∞} {f : α -> X} {s : Set α}
  proof: by
  simp only [ediam_le_iff, forall_mem_image]

中文:
定理 ediam_image_le_iff
  条件: {d : 实数>=0∞} {f : α -> X} {s : 集合 α}
  证明: by
  simp only [ediam_le_iff, forall_mem_image]

Depends on / 依赖: ediam_le_iff, forall_mem_image
-/
theorem ediam_image_le_iff {d : Real>=0∞} {f : α -> X} {s : Set α} :
    ediam (f '' s) <= d ↔ forall x in s, forall y in s, edist (f x) (f y) <= d := by
  simp only [ediam_le_iff, forall_mem_image]

/--
theorem `edist_le_of_ediam_le` / 定理 `edist_le_of_ediam_le`

English:
theorem edist_le_of_ediam_le
  given: {d} (hx : x in s) (hy : y in s) (hd : ediam s <= d)
  statement: edist x y <= d
  proof: ediam_le_iff.1 hd x hx y hy

中文:
定理 edist_le_of_ediam_le
  条件: {d} (hx : x in s) (hy : y in s) (hd : ediam s <= d)
  结论: edist x y <= d
  证明: ediam_le_iff.1 hd x hx y hy

Depends on / 依赖: ediam_le_iff
-/
theorem edist_le_of_ediam_le {d} (hx : x in s) (hy : y in s) (hd : ediam s <= d) : edist x y <= d :=
  ediam_le_iff.1 hd x hx y hy

/--
theorem `edist_le_ediam_of_mem` / 定理 `edist_le_ediam_of_mem`

English:
theorem edist_le_ediam_of_mem
  given: (hx : x in s) (hy : y in s)
  statement: edist x y <= ediam s
  proof: edist_le_of_ediam_le hx hy le_rfl

中文:
定理 edist_le_ediam_of_mem
  条件: (hx : x in s) (hy : y in s)
  结论: edist x y <= ediam s
  证明: edist_le_of_ediam_le hx hy le_rfl

Depends on / 依赖: edist_le_of_ediam_le, le_rfl
-/
theorem edist_le_ediam_of_mem (hx : x in s) (hy : y in s) : edist x y <= ediam s :=
  edist_le_of_ediam_le hx hy le_rfl

/--
theorem `ediam_le` / 定理 `ediam_le`

English:
theorem ediam_le
  given: {d : Real>=0∞} (h : forall x in s, forall y in s, edist x y <= d)
  statement: ediam s <= d
  proof: ediam_le_iff.2 h

中文:
定理 ediam_le
  条件: {d : 实数>=0∞} (h : 对任意 x in s, 对任意 y in s, edist x y <= d)
  结论: ediam s <= d
  证明: ediam_le_iff.2 h

Depends on / 依赖: ediam_le_iff
-/
theorem ediam_le {d : Real>=0∞} (h : forall x in s, forall y in s, edist x y <= d) : ediam s <= d :=
  ediam_le_iff.2 h

/--
theorem `ediam_subsingleton` / 定理 `ediam_subsingleton`

English:
theorem ediam_subsingleton
  given: (hs : s.Subsingleton)
  statement: ediam s = 0
  proof: nonpos_iff_eq_zero.1 ediam_le fun _x hx y hy => (hs hx hy).symm ▸ edist_self y ▸ le_rfl

alias _root_.Set.Subsingleton.ediam_eq := ediam_subsingleton

中文:
定理 ediam_subsingleton
  条件: (hs : s.子单例)
  结论: ediam s = 0
  证明: nonpos_iff_eq_zero.1 ediam_le fun _x hx y hy => (hs hx hy).symm ▸ edist_self y ▸ le_rfl

alias _root_.Set.Subsingleton.ediam_eq := ediam_subsingleton

Depends on / 依赖: ediam_le, edist_self, le_rfl, nonpos_iff_eq_zero
-/
theorem ediam_subsingleton (hs : s.Subsingleton) : ediam s = 0 :=
nonpos_iff_eq_zero.1 ediam_le fun _x hx y hy => (hs hx hy).symm ▸ edist_self y ▸ le_rfl

alias _root_.Set.Subsingleton.ediam_eq := ediam_subsingleton

/-- The diameter of the empty set vanishes -/
@[simp]
/--
theorem `ediam_empty` / 定理 `ediam_empty`

English:
theorem ediam_empty
  statement: ediam (∅ : Set X) = 0
  proof: ediam_subsingleton subsingleton_empty

中文:
定理 ediam_empty
  结论: ediam (∅ : 集合 X) = 0
  证明: ediam_subsingleton subsingleton_empty

Depends on / 依赖: ediam_subsingleton, subsingleton_empty
-/
theorem ediam_empty : ediam (∅ : Set X) = 0 :=
  ediam_subsingleton subsingleton_empty

/-- The extended diameter of a singleton vanishes -/
@[simp]
/--
theorem `ediam_singleton` / 定理 `ediam_singleton`

English:
theorem ediam_singleton
  statement: ediam ({x} : Set X) = 0
  proof: ediam_subsingleton subsingleton_singleton

@[to_additive (attr := simp)]

中文:
定理 ediam_singleton
  结论: ediam ({x} : 集合 X) = 0
  证明: ediam_subsingleton subsingleton_singleton

@[to_additive (attr := simp)]

Depends on / 依赖: ediam_subsingleton, subsingleton_singleton
-/
theorem ediam_singleton : ediam ({x} : Set X) = 0 :=
  ediam_subsingleton subsingleton_singleton

@[to_additive (attr := simp)]
/--
theorem `ediam_one` / 定理 `ediam_one`

English:
theorem ediam_one
  given: [One X]
  statement: ediam (1 : Set X) = 0
  proof: ediam_singleton

中文:
定理 ediam_one
  条件: [幺 X]
  结论: ediam (1 : 集合 X) = 0
  证明: ediam_singleton

Depends on / 依赖: ediam_singleton
-/
theorem ediam_one [One X] : ediam (1 : Set X) = 0 :=
  ediam_singleton

/--
theorem `ediam_iUnion_mem_option` / 定理 `ediam_iUnion_mem_option`

English:
theorem ediam_iUnion_mem_option
  given: {ι : Type*} (o : Option ι) (s : ι -> Set X)
  proof: by cases o <;> simp

中文:
定理 ediam_iUnion_mem_option
  条件: {ι : 类型} (o : 选项类型 ι) (s : ι -> 集合 X)
  证明: by cases o <;> simp
-/
theorem ediam_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι -> Set X) :
    ediam (⋃ i in o, s i) = ⨆ i in o, ediam (s i) := by cases o <;> simp

/--
theorem `ediam_insert` / 定理 `ediam_insert`

English:
theorem ediam_insert
  statement: ediam (insert x s) = max (⨆ y in s, edist x y) (ediam s)
  proof: eq_of_forall_ge_iff fun d => by simp +contextual [ediam_le_iff, edist_comm]

中文:
定理 ediam_insert
  结论: ediam (insert x s) = 最大值 (⨆ y in s, edist x y) (ediam s)
  证明: eq_of_forall_ge_iff fun d => by simp +contextual [ediam_le_iff, edist_comm]

Depends on / 依赖: contextual, ediam_le_iff, edist_comm, eq_of_forall_ge_iff
-/
theorem ediam_insert : ediam (insert x s) = max (⨆ y in s, edist x y) (ediam s) :=
  eq_of_forall_ge_iff fun d => by simp +contextual [ediam_le_iff, edist_comm]

/--
theorem `ediam_pair` / 定理 `ediam_pair`

English:
theorem ediam_pair
  statement: ediam {x, y} = edist x y
  proof: by simp [ediam_insert]

中文:
定理 ediam_pair
  结论: ediam {x, y} = edist x y
  证明: by simp [ediam_insert]

Depends on / 依赖: ediam_insert
-/
theorem ediam_pair : ediam {x, y} = edist x y := by simp [ediam_insert]

/--
theorem `ediam_triple` / 定理 `ediam_triple`

English:
theorem ediam_triple
  statement: ediam {x, y, z} = max (max (edist x y) (edist x z)) (edist y z)
  proof: by
  simp only [ediam_insert, iSup_insert, iSup_singleton, ediam_singleton, max_zero]

中文:
定理 ediam_triple
  结论: ediam {x, y, z} = 最大值 (最大值 (edist x y) (edist x z)) (edist y z)
  证明: by
  simp only [ediam_insert, iSup_insert, iSup_singleton, ediam_singleton, max_zero]

Depends on / 依赖: ediam_insert, ediam_singleton, iSup_insert, iSup_singleton, max_zero
-/
theorem ediam_triple : ediam {x, y, z} = max (max (edist x y) (edist x z)) (edist y z) := by
  simp only [ediam_insert, iSup_insert, iSup_singleton, ediam_singleton, max_zero]

/-- The extended diameter is monotonous with respect to inclusion -/
@[gcongr]
/--
theorem `ediam_mono` / 定理 `ediam_mono`

English:
theorem ediam_mono
  given: (h : s subseteq t)
  statement: ediam s <= ediam t
  proof: ediam_le fun _x hx _y hy => edist_le_ediam_of_mem (h hx) (h hy)

中文:
定理 ediam_mono
  条件: (h : s subseteq t)
  结论: ediam s <= ediam t
  证明: ediam_le fun _x hx _y hy => edist_le_ediam_of_mem (h hx) (h hy)

Depends on / 依赖: ediam_le, edist_le_ediam_of_mem
-/
theorem ediam_mono (h : s subseteq t) : ediam s <= ediam t :=
  ediam_le fun _x hx _y hy => edist_le_ediam_of_mem (h hx) (h hy)

/--
theorem `ediam_union_le_add_edist` / 定理 `ediam_union_le_add_edist`

English:
theorem ediam_union_le_add_edist
  given: (xs : x in s) (yt : y in t)
  proof: by
  have A : forall a in s, forall b in t, edist a b <= ediam s + edist x y + ediam t := fun a ha b hb =>
    calc
      edist a b <= edist a x + edist x y + edist y b := edist_triangle4 _ _ _ _
      _ <= ediam s + edist x y + ediam t := by
        gcongr
        exacts [edist_le_ediam_of_mem ha x

中文:
定理 ediam_union_le_add_edist
  条件: (xs : x in s) (yt : y in t)
  证明: by
  have A : forall a in s, forall b in t, edist a b <= ediam s + edist x y + ediam t := fun a ha b hb =>
    calc
      edist a b <= edist a x + edist x y + edist y b := edist_triangle4 _ _ _ _
      _ <= ediam s + edist x y + ediam t := by
        gcongr
        exacts [edist_le_ediam_of_mem ha x

Depends on / 依赖: ediam_le, edist_le_ediam_of_mem, edist_triangle4, exacts, mem_union
-/
theorem ediam_union_le_add_edist (xs : x in s) (yt : y in t) :
    ediam (s union t) <= ediam s + edist x y + ediam t := by
  have A : forall a in s, forall b in t, edist a b <= ediam s + edist x y + ediam t := fun a ha b hb =>
    calc
      edist a b <= edist a x + edist x y + edist y b := edist_triangle4 _ _ _ _
      _ <= ediam s + edist x y + ediam t := by
        gcongr
        exacts [edist_le_ediam_of_mem ha xs, edist_le_ediam_of_mem yt hb]
  refine ediam_le fun a ha b hb => ?_
  rw [mem_union] at ha hb
  rcases ha with h'a | h'a <;> rcases hb with h'b | h'b
  · calc
      edist a b <= ediam s := edist_le_ediam_of_mem h'a h'b
      _ <= ediam s + (edist x y + ediam t) := le_self_add
      _ = ediam s + edist x y + ediam t := (add_assoc _ _ _).symm
  · exact A a h'a b h'b
  · have Z := A b h'b a h'a
    rwa [edist_comm] at Z
  · calc
      edist a b <= ediam t := edist_le_ediam_of_mem h'a h'b
      _ <= ediam s + edist x y + ediam t := le_add_self

/--
theorem `ediam_union_le` / 定理 `ediam_union_le`

English:
theorem ediam_union_le
  given: (h : (s inter t).Nonempty)
  statement: ediam (s union t) <= ediam s + ediam t
  proof: by
  let ⟨x, ⟨xs, xt⟩⟩ := h
  simpa using ediam_union_le_add_edist xs xt

中文:
定理 ediam_union_le
  条件: (h : (s inter t).非空)
  结论: ediam (s union t) <= ediam s + ediam t
  证明: by
  let ⟨x, ⟨xs, xt⟩⟩ := h
  simpa using ediam_union_le_add_edist xs xt

Depends on / 依赖: ediam_union_le_add_edist
-/
theorem ediam_union_le (h : (s inter t).Nonempty) : ediam (s union t) <= ediam s + ediam t := by
  let ⟨x, ⟨xs, xt⟩⟩ := h
  simpa using ediam_union_le_add_edist xs xt

/--
theorem `ediam_closedEBall_le` / 定理 `ediam_closedEBall_le`

English:
theorem ediam_closedEBall_le
  given: {r : Real>=0∞}
  statement: ediam (closedEBall x r) <= 2 * r
  proof: ediam_le fun a ha b hb =>
    calc
      edist a b <= edist a x + edist b x := edist_triangle_right _ _ _
      _ <= r + r := add_le_add ha hb
      _ = 2 * r := (two_mul r).symm

中文:
定理 ediam_closedEBall_le
  条件: {r : 实数>=0∞}
  结论: ediam (closedEBall x r) <= 2 * r
  证明: ediam_le fun a ha b hb =>
    calc
      edist a b <= edist a x + edist b x := edist_triangle_right _ _ _
      _ <= r + r := add_le_add ha hb
      _ = 2 * r := (two_mul r).symm

Depends on / 依赖: add_le_add, ediam_le, edist_triangle_right, two_mul
-/
theorem ediam_closedEBall_le {r : Real>=0∞} : ediam (closedEBall x r) <= 2 * r :=
  ediam_le fun a ha b hb =>
    calc
      edist a b <= edist a x + edist b x := edist_triangle_right _ _ _
      _ <= r + r := add_le_add ha hb
      _ = 2 * r := (two_mul r).symm

/--
theorem `ediam_eball_le` / 定理 `ediam_eball_le`

English:
theorem ediam_eball_le
  given: {r : Real>=0∞}
  statement: ediam (eball x r) <= 2 * r
  proof: le_trans (ediam_mono eball_subset_closedEBall) ediam_closedEBall_le

中文:
定理 ediam_eball_le
  条件: {r : 实数>=0∞}
  结论: ediam (eball x r) <= 2 * r
  证明: le_trans (ediam_mono eball_subset_closedEBall) ediam_closedEBall_le

Depends on / 依赖: eball_subset_closedEBall, ediam_closedEBall_le, ediam_mono, le_trans
-/
theorem ediam_eball_le {r : Real>=0∞} : ediam (eball x r) <= 2 * r :=
  le_trans (ediam_mono eball_subset_closedEBall) ediam_closedEBall_le

/--
theorem `ediam_pi_le_of_le` / 定理 `ediam_pi_le_of_le`

English:
theorem ediam_pi_le_of_le
  statement: {ι : Type*} {X : ι -> Type*} [Fintype ι] [forall i, PseudoEMetricSpace (X i)]
  proof: by
  refine ediam_le fun x hx y hy => edist_pi_le_iff.mpr ?_
  rw [mem_univ_pi] at hx hy
  exact fun b => ediam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b)

中文:
定理 ediam_pi_le_of_le
  结论: {ι : 类型} {X : ι -> 类型} [有限类型 ι] [对任意 i, PseudoEMetric空间 (X i)]
  证明: by
  refine ediam_le fun x hx y hy => edist_pi_le_iff.mpr ?_
  rw [mem_univ_pi] at hx hy
  exact fun b => ediam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b)

Depends on / 依赖: ediam_le, ediam_le_iff, edist_pi_le_iff, edist_pi_le_iff.mpr, mem_univ_pi
-/
theorem ediam_pi_le_of_le {ι : Type*} {X : ι -> Type*} [Fintype ι] [forall i, PseudoEMetricSpace (X i)]
    {s : forall i : ι, Set (X i)} {c : Real>=0∞} (h : forall b, ediam (s b) <= c) : ediam (Set.pi univ s) <= c := by
  refine ediam_le fun x hx y hy => edist_pi_le_iff.mpr ?_
  rw [mem_univ_pi] at hx hy
  exact fun b => ediam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b)

end PseudoEMetricSpace

section EMetricSpace

variable [EMetricSpace X]

/--
theorem `ediam_eq_zero_iff` / 定理 `ediam_eq_zero_iff`

English:
theorem ediam_eq_zero_iff
  statement: ediam s = 0 ↔ s.Subsingleton
  proof: ⟨fun h _x hx _y hy => edist_le_zero.1 h ▸ edist_le_ediam_of_mem hx hy, ediam_subsingleton⟩

中文:
定理 ediam_eq_zero_iff
  结论: ediam s = 0 ↔ s.子单例
  证明: ⟨fun h _x hx _y hy => edist_le_zero.1 h ▸ edist_le_ediam_of_mem hx hy, ediam_subsingleton⟩

Depends on / 依赖: ediam_subsingleton, edist_le_ediam_of_mem, edist_le_zero
-/
theorem ediam_eq_zero_iff : ediam s = 0 ↔ s.Subsingleton :=
⟨fun h _x hx _y hy => edist_le_zero.1 h ▸ edist_le_ediam_of_mem hx hy, ediam_subsingleton⟩

/--
theorem `ediam_pos_iff` / 定理 `ediam_pos_iff`

English:
theorem ediam_pos_iff
  statement: 0 < ediam s ↔ s.Nontrivial
  proof: by
  simp only [pos_iff_ne_zero, Ne, ediam_eq_zero_iff, Set.not_subsingleton_iff]

中文:
定理 ediam_pos_iff
  结论: 0 < ediam s ↔ s.非平凡
  证明: by
  simp only [pos_iff_ne_zero, Ne, ediam_eq_zero_iff, Set.not_subsingleton_iff]

Depends on / 依赖: Set.not_subsingleton_iff, ediam_eq_zero_iff, not_subsingleton_iff, pos_iff_ne_zero
-/
theorem ediam_pos_iff : 0 < ediam s ↔ s.Nontrivial := by
  simp only [pos_iff_ne_zero, Ne, ediam_eq_zero_iff, Set.not_subsingleton_iff]

/--
theorem `ediam_pos_iff'` / 定理 `ediam_pos_iff'`

English:
theorem ediam_pos_iff'
  statement: 0 < ediam s ↔ exists x in s, exists y in s, x != y
  proof: by
  simp only [ediam_pos_iff, Set.Nontrivial]

中文:
定理 ediam_pos_iff'
  结论: 0 < ediam s ↔ 存在 x in s, 存在 y in s, x != y
  证明: by
  simp only [ediam_pos_iff, Set.Nontrivial]

Depends on / 依赖: Nontrivial, Set.Nontrivial, ediam_pos_iff
-/
theorem ediam_pos_iff' : 0 < ediam s ↔ exists x in s, exists y in s, x != y := by
  simp only [ediam_pos_iff, Set.Nontrivial]

end EMetricSpace

end Metric

namespace EMetric

open Metric

@[deprecated (since := "2026-01-04")] alias diam := Metric.ediam
@[deprecated (since := "2026-01-04")] alias diam_eq_sSup := ediam_eq_sSup
@[deprecated (since := "2026-01-04")] alias diam_le_iff := ediam_le_iff
@[deprecated (since := "2026-01-04")] alias diam_image_le_iff := ediam_image_le_iff
@[deprecated (since := "2026-01-04")] alias edist_le_of_diam_le := edist_le_of_ediam_le
@[deprecated (since := "2026-01-04")] alias edist_le_diam_of_mem := edist_le_ediam_of_mem
@[deprecated (since := "2026-01-04")] alias diam_le := ediam_le
@[deprecated (since := "2026-01-04")] alias diam_subsingleton := ediam_subsingleton
@[deprecated (since := "2026-01-04")] alias diam_empty := ediam_empty
@[deprecated (since := "2026-01-04")] alias diam_singleton := ediam_singleton
@[deprecated (since := "2026-01-04")] alias diam_zero := ediam_zero
@[to_additive existing, deprecated (since := "2026-01-04")] alias diam_one := ediam_one
@[deprecated (since := "2026-01-04")] alias diam_iUnion_mem_option := ediam_iUnion_mem_option
@[deprecated (since := "2026-01-04")] alias diam_insert := ediam_insert
@[deprecated (since := "2026-01-04")] alias diam_pair := ediam_pair
@[deprecated (since := "2026-01-04")] alias diam_triple := ediam_triple
@[deprecated (since := "2026-01-04")] alias diam_mono := ediam_mono
@[deprecated (since := "2026-01-04")] alias diam_union := ediam_union_le_add_edist
@[deprecated (since := "2026-01-04")] alias diam_union' := ediam_union_le
@[deprecated (since := "2026-01-04")] alias diam_closedBall := ediam_closedEBall_le
@[deprecated (since := "2026-01-04")] alias diam_ball := ediam_eball_le
@[deprecated (since := "2026-01-04")] alias diam_pi_le_of_le := ediam_pi_le_of_le
@[deprecated (since := "2026-01-04")] alias diam_eq_zero_iff := ediam_eq_zero_iff
@[deprecated (since := "2026-01-04")] alias diam_pos_iff := ediam_pos_iff
@[deprecated (since := "2026-01-04")] alias diam_pos_iff' := ediam_pos_iff'

end EMetric
