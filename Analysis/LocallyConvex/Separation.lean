/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.RCLike.Extend
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Separation Hahn-Banach theorem

In this file we prove the geometric Hahn-Banach theorem. For any two disjoint convex sets, there
exists a continuous linear functional separating them, geometrically meaning that we can intercalate
a plane between them.

We provide many variations to stricten the result under more assumptions on the convex sets:
* `geometric_hahn_banach_open`: One set is open. Weak separation.
* `geometric_hahn_banach_open_point`, `geometric_hahn_banach_point_open`: One set is open, the
  other is a singleton. Weak separation.
* `geometric_hahn_banach_open_open`: Both sets are open. Semistrict separation.
* `geometric_hahn_banach_of_nonempty_interior'`: One set has nonempty interior. Nonstrict
  separation.
* `geometric_hahn_banach_of_nonempty_interior`: One set has nonempty interior, the other one is
  nonempty. Nonstrict separation by a nonzero functional.
* `geometric_hahn_banach_of_nonempty_interior_point`: One set has nonempty interior, the other one
  is a singleton outside this interior. Nonstrict separation, with the maximum attained at the
  singleton.
* `geometric_hahn_banach_compact_closed`, `geometric_hahn_banach_closed_compact`: One set is closed,
  the other one is compact. Strict separation.
* `geometric_hahn_banach_point_closed`, `geometric_hahn_banach_closed_point`: One set is closed, the
  other one is a singleton. Strict separation.
* `geometric_hahn_banach_point_point`: Both sets are singletons. Strict separation.
-/

public section

assert_not_exists ContinuousLinearMap.hasOpNorm

open Set

open scoped Pointwise

variable {𝕜 E : Type*}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `separate_convex_open_set` / 定理 `separate_convex_open_set`

English:
theorem separate_convex_open_set
  statement: [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  proof: by
  let f : E ->ₗ.[Real] Real := LinearPMap.mkSpanSingleton x₀ 1 (ne_of_mem_of_not_mem hs₀ hx₀).symm
  have := exists_extension_of_le_sublinear f (gauge s) (fun c hc => gauge_smul_of_nonneg hc.le)
    (gauge_add_le hs₁ <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀) ?_
  · obtain ⟨φ, hφ₁, hφ₂⟩ := this
    have hφ₃ : φ x₀ = 1 := by
      rw [← f.domain.coe_mk x₀ (Submodule.mem_span_singleton_self _)]; rw [hφ₁]; rw [LinearPMap.mkSpanSingleton'_apply_self]
    have hφ₄ : forall x in s, φ x < 1 := fun x hx =>
      (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_isOpen hs₂ hx)
    refine ⟨⟨φ, ?_⟩, hφ₃, hφ₄⟩
    refine
      φ.continuous_of_nonzero_on_open _ (hs₂.vadd (-x₀)) (Nonempty.vadd_set ⟨0, hs₀⟩)
        (vadd_set_subset_iff.mpr fun x hx => ?_)
    change φ (-x₀ + x) != 0
    rw [map_add]; rw [map_neg]
    specialize hφ₄ x hx
    linarith
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [LinearPMap.mkSpanSingleton'_apply]
  simp only [mul_one, smul_eq_mul]
  obtain h | h := le_or_gt y 0
  · exact h.trans (gauge_nonneg _)
  · rw [gauge_smul_of_nonneg h.le, smul_eq_mul, RingHom.id_apply, le_mul_iff_one_le_right h]
    exact
      one_le_gauge_of_notMem (hs₁.starConvex hs₀)
        (absorbent_nhds_zero <| hs₂.mem_nhds hs₀).absorbs hx₀

中文:
定理 separate_convex_open_set
  结论: [拓扑空间 E] [加法交换群 E] [是拓扑加群 E]
  证明: by
  let f : E ->ₗ.[Real] Real := LinearPMap.mkSpanSingleton x₀ 1 (ne_of_mem_of_not_mem hs₀ hx₀).symm
  have := exists_extension_of_le_sublinear f (gauge s) (fun c hc => gauge_smul_of_nonneg hc.le)
    (gauge_add_le hs₁ <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀) ?_
  · obtain ⟨φ, hφ₁, hφ₂⟩ := this
    have hφ₃ : φ x₀ = 1 := by
      rw [← f.domain.coe_mk x₀ (Submodule.mem_span_singleton_self _)]; rw [hφ₁]; rw [LinearPMap.mkSpanSingleton'_apply_self]
    have hφ₄ : forall x in s, φ x < 1 := fun x hx =>
      (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_isOpen hs₂ hx)
    refine ⟨⟨φ, ?_⟩, hφ₃, hφ₄⟩
    refine
      φ.continuous_of_nonzero_on_open _ (hs₂.vadd (-x₀)) (Nonempty.vadd_set ⟨0, hs₀⟩)
        (vadd_set_subset_iff.mpr fun x hx => ?_)
    change φ (-x₀ + x) != 0
    rw [map_add]; rw [map_neg]
    specialize hφ₄ x hx
    linarith
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [LinearPMap.mkSpanSingleton'_apply]
  simp only [mul_one, smul_eq_mul]
  obtain h | h := le_or_gt y 0
  · exact h.trans (gauge_nonneg _)
  · rw [gauge_smul_of_nonneg h.le, smul_eq_mul, RingHom.id_apply, le_mul_iff_one_le_right h]
    exact
      one_le_gauge_of_notMem (hs₁.starConvex hs₀)
        (absorbent_nhds_zero <| hs₂.mem_nhds hs₀).absorbs hx₀

Depends on / 依赖: LinearPMap, LinearPMap.mkSpanSingleton, Submodule, Submodule.mem_span_singleton_self, _apply_self, absorbent_nhds_zero, coe_mk, domain, exists_extension_of_le_sublinear, f.domain.coe_mk, gauge_add_le, gauge_smul_of_nonneg, hc.le, mem_nhds, mem_span_singleton_self, mkSpanSingleton, ne_of_mem_of_not_mem, trans_lt
-/
theorem separate_convex_open_set [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
    [Module Real E] [ContinuousSMul Real E] {s : Set E} (hs₀ : (0 : E) in s) (hs₁ : Convex Real s)
    (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) :
    exists f : StrongDual Real E, f x₀ = 1 ∧ forall x in s, f x < 1 := by
  let f : E ->ₗ.[Real] Real := LinearPMap.mkSpanSingleton x₀ 1 (ne_of_mem_of_not_mem hs₀ hx₀).symm
  have := exists_extension_of_le_sublinear f (gauge s) (fun c hc => gauge_smul_of_nonneg hc.le)
    (gauge_add_le hs₁ <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀) ?_
  · obtain ⟨φ, hφ₁, hφ₂⟩ := this
    have hφ₃ : φ x₀ = 1 := by
      rw [← f.domain.coe_mk x₀ (Submodule.mem_span_singleton_self _)]; rw [hφ₁]; rw [LinearPMap.mkSpanSingleton'_apply_self]
    have hφ₄ : forall x in s, φ x < 1 := fun x hx =>
      (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_isOpen hs₂ hx)
    refine ⟨⟨φ, ?_⟩, hφ₃, hφ₄⟩
    refine
      φ.continuous_of_nonzero_on_open _ (hs₂.vadd (-x₀)) (Nonempty.vadd_set ⟨0, hs₀⟩)
        (vadd_set_subset_iff.mpr fun x hx => ?_)
    change φ (-x₀ + x) != 0
    rw [map_add]; rw [map_neg]
    specialize hφ₄ x hx
    linarith
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [LinearPMap.mkSpanSingleton'_apply]
  simp only [mul_one, smul_eq_mul]
  obtain h | h := le_or_gt y 0
  · exact h.trans (gauge_nonneg _)
  · rw [gauge_smul_of_nonneg h.le, smul_eq_mul, RingHom.id_apply, le_mul_iff_one_le_right h]
    exact
      one_le_gauge_of_notMem (hs₁.starConvex hs₀)
        (absorbent_nhds_zero <| hs₂.mem_nhds hs₀).absorbs hx₀

variable [TopologicalSpace E] [AddCommGroup E] [Module Real E]
  {s t : Set E} {x y : E}
section

variable [IsTopologicalAddGroup E] [ContinuousSMul Real E]

/--
theorem `geometric_hahn_banach_open` / 定理 `geometric_hahn_banach_open`

English:
theorem geometric_hahn_banach_open
  statement: (hs₁ : Convex Real s) (hs₂ : IsOpen s) (ht : Convex Real t)
  proof: by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, 0, by simp, fun b _hb => le_rfl⟩
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact ⟨0, 1, fun a _ha => zero_lt_one, by simp⟩
  let x₀ := b₀ - a₀
  let C := x₀ +ᵥ (s - t)
  have : (0 : E) in C :=
    ⟨a₀ - b₀, sub_mem_sub ha₀ hb₀, by simp_rw [x₀, vadd_eq_add, sub_add_sub_cancel', sub_self]⟩
  have : Convex Real C := (hs₁.sub ht).vadd _
  have : x₀ ∉ C := by
    intro hx₀
    rw [← add_zero x₀] at hx₀
    exact disj.zero_notMem_sub_set (vadd_mem_vadd_set_iff.1 hx₀)
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 in C› ‹_› (hs₂.sub_right.vadd _) ‹x₀ ∉ C›
  have forall_le : forall a in s, forall b in t, f a <= f b := by
    intro a ha b hb
    have := hf₂ (x₀ + (a - b)) (vadd_mem_vadd_set <| sub_mem_sub ha hb)
    simp only [f.map_add, f.map_sub, hf₁] at this
    linarith
  refine ⟨f, sInf (f '' t), image_subset_iff.1 (?_ : f '' s subseteq Iio (sInf (f '' t))), fun b hb => ?_⟩
  · rw [← interior_Iic]
    refine interior_maximal (image_subset_iff.2 fun a ha => ?_) (f.isOpenMap_of_ne_zero ?_ _ hs₂)
    · exact le_csInf (Nonempty.image _ ⟨_, hb₀⟩) (forall_mem_image.2 <| forall_le _ ha)
    · rintro rfl
      simp at hf₁
· exact csInf_le ⟨f a₀, forall_mem_image.2 forall_le _ ha₀⟩ (mem_image_of_mem _ hb)

中文:
定理 geometric_hahn_banach_open
  结论: (hs₁ : 凸 实数 s) (hs₂ : 是开集 s) (ht : 凸 实数 t)
  证明: by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, 0, by simp, fun b _hb => le_rfl⟩
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact ⟨0, 1, fun a _ha => zero_lt_one, by simp⟩
  let x₀ := b₀ - a₀
  let C := x₀ +ᵥ (s - t)
  have : (0 : E) in C :=
    ⟨a₀ - b₀, sub_mem_sub ha₀ hb₀, by simp_rw [x₀, vadd_eq_add, sub_add_sub_cancel', sub_self]⟩
  have : Convex Real C := (hs₁.sub ht).vadd _
  have : x₀ ∉ C := by
    intro hx₀
    rw [← add_zero x₀] at hx₀
    exact disj.zero_notMem_sub_set (vadd_mem_vadd_set_iff.1 hx₀)
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 in C› ‹_› (hs₂.sub_right.vadd _) ‹x₀ ∉ C›
  have forall_le : forall a in s, forall b in t, f a <= f b := by
    intro a ha b hb
    have := hf₂ (x₀ + (a - b)) (vadd_mem_vadd_set <| sub_mem_sub ha hb)
    simp only [f.map_add, f.map_sub, hf₁] at this
    linarith
  refine ⟨f, sInf (f '' t), image_subset_iff.1 (?_ : f '' s subseteq Iio (sInf (f '' t))), fun b hb => ?_⟩
  · rw [← interior_Iic]
    refine interior_maximal (image_subset_iff.2 fun a ha => ?_) (f.isOpenMap_of_ne_zero ?_ _ hs₂)
    · exact le_csInf (Nonempty.image _ ⟨_, hb₀⟩) (forall_mem_image.2 <| forall_le _ ha)
    · rintro rfl
      simp at hf₁
· exact csInf_le ⟨f a₀, forall_mem_image.2 forall_le _ ha₀⟩ (mem_image_of_mem _ hb)

Depends on / 依赖: Convex, add_zero, disj.zero_notMem_sub_set, eq_empty_or_nonempty, le_rfl, s.eq_empty_or_nonempty, simp_rw, sub_add_sub_cancel, sub_mem_sub, sub_self, t.eq_empty_or_nonempty, vadd_eq_add, vadd_mem_vadd_se, zero_lt_one, zero_notMem_sub_set
-/
theorem geometric_hahn_banach_open (hs₁ : Convex Real s) (hs₂ : IsOpen s) (ht : Convex Real t)
    (disj : Disjoint s t) :
    exists (f : StrongDual Real E) (u : Real), (forall a in s, f a < u) ∧ forall b in t, u <= f b := by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, 0, by simp, fun b _hb => le_rfl⟩
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact ⟨0, 1, fun a _ha => zero_lt_one, by simp⟩
  let x₀ := b₀ - a₀
  let C := x₀ +ᵥ (s - t)
  have : (0 : E) in C :=
    ⟨a₀ - b₀, sub_mem_sub ha₀ hb₀, by simp_rw [x₀, vadd_eq_add, sub_add_sub_cancel', sub_self]⟩
  have : Convex Real C := (hs₁.sub ht).vadd _
  have : x₀ ∉ C := by
    intro hx₀
    rw [← add_zero x₀] at hx₀
    exact disj.zero_notMem_sub_set (vadd_mem_vadd_set_iff.1 hx₀)
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 in C› ‹_› (hs₂.sub_right.vadd _) ‹x₀ ∉ C›
  have forall_le : forall a in s, forall b in t, f a <= f b := by
    intro a ha b hb
    have := hf₂ (x₀ + (a - b)) (vadd_mem_vadd_set <| sub_mem_sub ha hb)
    simp only [f.map_add, f.map_sub, hf₁] at this
    linarith
  refine ⟨f, sInf (f '' t), image_subset_iff.1 (?_ : f '' s subseteq Iio (sInf (f '' t))), fun b hb => ?_⟩
  · rw [← interior_Iic]
    refine interior_maximal (image_subset_iff.2 fun a ha => ?_) (f.isOpenMap_of_ne_zero ?_ _ hs₂)
    · exact le_csInf (Nonempty.image _ ⟨_, hb₀⟩) (forall_mem_image.2 <| forall_le _ ha)
    · rintro rfl
      simp at hf₁
· exact csInf_le ⟨f a₀, forall_mem_image.2 forall_le _ ha₀⟩ (mem_image_of_mem _ hb)

/--
theorem `geometric_hahn_banach_open_point` / 定理 `geometric_hahn_banach_open_point`

English:
theorem geometric_hahn_banach_open_point
  given: (hs₁ : Convex Real s) (hs₂ : IsOpen s) (disj : x ∉ s)
  proof: let ⟨f, _s, hs, hx⟩ :=
    geometric_hahn_banach_open hs₁ hs₂ (convex_singleton x) (disjoint_singleton_right.2 disj)
  ⟨f, fun a ha => lt_of_lt_of_le (hs a ha) (hx x (mem_singleton _))⟩

中文:
定理 geometric_hahn_banach_open_point
  条件: (hs₁ : 凸 实数 s) (hs₂ : 是开集 s) (disj : x ∉ s)
  证明: let ⟨f, _s, hs, hx⟩ :=
    geometric_hahn_banach_open hs₁ hs₂ (convex_singleton x) (disjoint_singleton_right.2 disj)
  ⟨f, fun a ha => lt_of_lt_of_le (hs a ha) (hx x (mem_singleton _))⟩

Depends on / 依赖: convex_singleton, disjoint_singleton_right, geometric_hahn_banach_open, lt_of_lt_of_le, mem_singleton
-/
theorem geometric_hahn_banach_open_point (hs₁ : Convex Real s) (hs₂ : IsOpen s) (disj : x ∉ s) :
    exists f : StrongDual Real E, forall a in s, f a < f x :=
  let ⟨f, _s, hs, hx⟩ :=
    geometric_hahn_banach_open hs₁ hs₂ (convex_singleton x) (disjoint_singleton_right.2 disj)
  ⟨f, fun a ha => lt_of_lt_of_le (hs a ha) (hx x (mem_singleton _))⟩

/--
theorem `geometric_hahn_banach_point_open` / 定理 `geometric_hahn_banach_point_open`

English:
theorem geometric_hahn_banach_point_open
  given: (ht₁ : Convex Real t) (ht₂ : IsOpen t) (disj : x ∉ t)
  proof: let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩

中文:
定理 geometric_hahn_banach_point_open
  条件: (ht₁ : 凸 实数 t) (ht₂ : 是开集 t) (disj : x ∉ t)
  证明: let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩

Depends on / 依赖: geometric_hahn_banach_open_point
-/
theorem geometric_hahn_banach_point_open (ht₁ : Convex Real t) (ht₂ : IsOpen t) (disj : x ∉ t) :
    exists f : StrongDual Real E, forall b in t, f x < f b :=
  let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩

/--
theorem `geometric_hahn_banach_open_open` / 定理 `geometric_hahn_banach_open_open`

English:
theorem geometric_hahn_banach_open_open
  statement: (hs₁ : Convex Real s) (hs₂ : IsOpen s) (ht₁ : Convex Real t)
  proof: by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, -1, by simp, fun b _hb => by simp⟩
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact ⟨0, 1, fun a _ha => by simp, by simp⟩
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open hs₁ hs₂ ht₁ disj
  refine ⟨f, s, hf₁, image_subset_iff.1 (?_ : f '' t subseteq Ioi s)⟩
  rw [← interior_Ici]
  refine interior_maximal (image_subset_iff.2 hf₂) (f.isOpenMap_of_ne_zero ?_ _ ht₃)
  rintro rfl
  simp_rw [zero_apply] at hf₁ hf₂
  exact (hf₁ _ ha₀).not_ge (hf₂ _ hb₀)

中文:
定理 geometric_hahn_banach_open_open
  结论: (hs₁ : 凸 实数 s) (hs₂ : 是开集 s) (ht₁ : 凸 实数 t)
  证明: by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, -1, by simp, fun b _hb => by simp⟩
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact ⟨0, 1, fun a _ha => by simp, by simp⟩
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open hs₁ hs₂ ht₁ disj
  refine ⟨f, s, hf₁, image_subset_iff.1 (?_ : f '' t subseteq Ioi s)⟩
  rw [← interior_Ici]
  refine interior_maximal (image_subset_iff.2 hf₂) (f.isOpenMap_of_ne_zero ?_ _ ht₃)
  rintro rfl
  simp_rw [zero_apply] at hf₁ hf₂
  exact (hf₁ _ ha₀).not_ge (hf₂ _ hb₀)

Depends on / 依赖: eq_empty_or_nonempty, f.isOpenMap_of_ne_zero, geometric_hahn_banach_open, image_subset_iff, interior_Ici, interior_maximal, isOpenMap_of_ne_zero, s.eq_empty_or_nonempty, simp_rw, subseteq, t.eq_empty_or_nonempty, zero_apply
-/
theorem geometric_hahn_banach_open_open (hs₁ : Convex Real s) (hs₂ : IsOpen s) (ht₁ : Convex Real t)
    (ht₃ : IsOpen t) (disj : Disjoint s t) :
    exists (f : StrongDual Real E) (u : Real), (forall a in s, f a < u) ∧ forall b in t, u < f b := by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, -1, by simp, fun b _hb => by simp⟩
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact ⟨0, 1, fun a _ha => by simp, by simp⟩
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open hs₁ hs₂ ht₁ disj
  refine ⟨f, s, hf₁, image_subset_iff.1 (?_ : f '' t subseteq Ioi s)⟩
  rw [← interior_Ici]
  refine interior_maximal (image_subset_iff.2 hf₂) (f.isOpenMap_of_ne_zero ?_ _ ht₃)
  rintro rfl
  simp_rw [zero_apply] at hf₁ hf₂
  exact (hf₁ _ ha₀).not_ge (hf₂ _ hb₀)

/--
theorem `geometric_hahn_banach_of_nonempty_interior` / 定理 `geometric_hahn_banach_of_nonempty_interior`

English:
theorem geometric_hahn_banach_of_nonempty_interior
  proof: by
  obtain ⟨f, u, hfA, hfB⟩ :=
    geometric_hahn_banach_open hs.interior isOpen_interior ht hst
  refine ⟨f, u, ?_, fun a ha => ?_, hfB⟩
  · obtain ⟨a, ha⟩ := hsint
    obtain ⟨b, hb⟩ := htne
    intro hzero
    have ha' : (0 : Real) < u := by simpa [hzero] using hfA a ha
    have hb' : u <= (0 : Real) := by simpa [hzero] using hfB b hb
    linarith
· apply closure_minimal (fun x hx => le_of_lt (hfA x hx)) isClosed_Iic.preimage f.continuous
    simpa [hs.closure_interior_eq_closure_of_nonempty_interior hsint] using subset_closure ha

中文:
定理 geometric_hahn_banach_of_nonempty_interior
  证明: by
  obtain ⟨f, u, hfA, hfB⟩ :=
    geometric_hahn_banach_open hs.interior isOpen_interior ht hst
  refine ⟨f, u, ?_, fun a ha => ?_, hfB⟩
  · obtain ⟨a, ha⟩ := hsint
    obtain ⟨b, hb⟩ := htne
    intro hzero
    have ha' : (0 : Real) < u := by simpa [hzero] using hfA a ha
    have hb' : u <= (0 : Real) := by simpa [hzero] using hfB b hb
    linarith
· apply closure_minimal (fun x hx => le_of_lt (hfA x hx)) isClosed_Iic.preimage f.continuous
    simpa [hs.closure_interior_eq_closure_of_nonempty_interior hsint] using subset_closure ha

Depends on / 依赖: closure_interior_eq_closure_of_nonempty_interior, closure_minimal, continuous, f.continuous, geometric_hahn_banach_open, hs.closure_interior_eq_closure_of_nonempty_interior, hs.interior, interior, isClosed_Iic, isClosed_Iic.preimage, isOpen_interior, le_of_lt, preimage, subset_clos
-/
theorem geometric_hahn_banach_of_nonempty_interior
  (hs : Convex Real s) (ht : Convex Real t) (hst : Disjoint (interior s) t)
    (hsint : (interior s).Nonempty) (htne : t.Nonempty) :
    exists (f : StrongDual Real E) (u : Real), f != 0 ∧ (forall a in s, f a <= u) ∧ forall b in t, u <= f b := by
  obtain ⟨f, u, hfA, hfB⟩ :=
    geometric_hahn_banach_open hs.interior isOpen_interior ht hst
  refine ⟨f, u, ?_, fun a ha => ?_, hfB⟩
  · obtain ⟨a, ha⟩ := hsint
    obtain ⟨b, hb⟩ := htne
    intro hzero
    have ha' : (0 : Real) < u := by simpa [hzero] using hfA a ha
    have hb' : u <= (0 : Real) := by simpa [hzero] using hfB b hb
    linarith
· apply closure_minimal (fun x hx => le_of_lt (hfA x hx)) isClosed_Iic.preimage f.continuous
    simpa [hs.closure_interior_eq_closure_of_nonempty_interior hsint] using subset_closure ha

/--
theorem `geometric_hahn_banach_of_nonempty_interior'` / 定理 `geometric_hahn_banach_of_nonempty_interior'`

English:
theorem geometric_hahn_banach_of_nonempty_interior'
  proof: by
  by_cases htne : t.Nonempty
  · obtain ⟨f, u, -, hs', ht'⟩ :=
      geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
    exact ⟨f, u, hs', ht'⟩
  · exact ⟨0, 0, by simp⟩

中文:
定理 geometric_hahn_banach_of_nonempty_interior'
  证明: by
  by_cases htne : t.Nonempty
  · obtain ⟨f, u, -, hs', ht'⟩ :=
      geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
    exact ⟨f, u, hs', ht'⟩
  · exact ⟨0, 0, by simp⟩

Depends on / 依赖: Nonempty, geometric_hahn_banach_of_nonempty_interior, t.Nonempty
-/
theorem geometric_hahn_banach_of_nonempty_interior'
  (hs : Convex Real s) (ht : Convex Real t) (hst : Disjoint (interior s) t)
    (hsint : (interior s).Nonempty) :
    exists (f : StrongDual Real E) (u : Real), (forall a in s, f a <= u) ∧ forall b in t, u <= f b := by
  by_cases htne : t.Nonempty
  · obtain ⟨f, u, -, hs', ht'⟩ :=
      geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
    exact ⟨f, u, hs', ht'⟩
  · exact ⟨0, 0, by simp⟩

/--
theorem `geometric_hahn_banach_of_nonempty_interior_point` / 定理 `geometric_hahn_banach_of_nonempty_interior_point`

English:
theorem geometric_hahn_banach_of_nonempty_interior_point
  proof: by
  obtain ⟨f, u, hfne, hA', hx'⟩ :=
    geometric_hahn_banach_of_nonempty_interior hA (convex_singleton x)
      (disjoint_singleton_right.2 hxA) hAint (singleton_nonempty x)
  exact ⟨f, hfne, fun a ha => (hA' a ha).trans (hx' x (mem_singleton _))⟩

中文:
定理 geometric_hahn_banach_of_nonempty_interior_point
  证明: by
  obtain ⟨f, u, hfne, hA', hx'⟩ :=
    geometric_hahn_banach_of_nonempty_interior hA (convex_singleton x)
      (disjoint_singleton_right.2 hxA) hAint (singleton_nonempty x)
  exact ⟨f, hfne, fun a ha => (hA' a ha).trans (hx' x (mem_singleton _))⟩

Depends on / 依赖: convex_singleton, disjoint_singleton_right, geometric_hahn_banach_of_nonempty_interior, mem_singleton, singleton_nonempty
-/
theorem geometric_hahn_banach_of_nonempty_interior_point
    {A : Set E} (hA : Convex Real A) (hxA : x ∉ interior A) (hAint : (interior A).Nonempty) :
    exists f : StrongDual Real E, f != 0 ∧ forall a in A, f a <= f x := by
  obtain ⟨f, u, hfne, hA', hx'⟩ :=
    geometric_hahn_banach_of_nonempty_interior hA (convex_singleton x)
      (disjoint_singleton_right.2 hxA) hAint (singleton_nonempty x)
  exact ⟨f, hfne, fun a ha => (hA' a ha).trans (hx' x (mem_singleton _))⟩

variable [LocallyConvexSpace Real E]

/--
theorem `geometric_hahn_banach_compact_closed` / 定理 `geometric_hahn_banach_compact_closed`

English:
theorem geometric_hahn_banach_compact_closed
  statement: (hs₁ : Convex Real s) (hs₂ : IsCompact s)
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨0, -2, -1, by simp⟩
  obtain rfl | _ht := t.eq_empty_or_nonempty
  · exact ⟨0, 1, 2, by simp⟩
  obtain ⟨U, V, hU, hV, hU₁, hV₁, sU, tV, disj'⟩ := disj.exists_open_convexes hs₁ hs₂ ht₁ ht₂
  obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj'
  obtain ⟨x, hx₁, hx₂⟩ := hs₂.exists_isMaxOn hs f.continuous.continuousOn
  have : f x < u := hf₁ x (sU hx₁)
  exact
    ⟨f, (f x + u) / 2, u,
      fun a ha => by have := hx₂ ha; dsimp at this; linarith,
      by linarith,
      fun b hb => hf₂ b (tV hb)⟩

中文:
定理 geometric_hahn_banach_compact_closed
  结论: (hs₁ : 凸 实数 s) (hs₂ : 是紧集 s)
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨0, -2, -1, by simp⟩
  obtain rfl | _ht := t.eq_empty_or_nonempty
  · exact ⟨0, 1, 2, by simp⟩
  obtain ⟨U, V, hU, hV, hU₁, hV₁, sU, tV, disj'⟩ := disj.exists_open_convexes hs₁ hs₂ ht₁ ht₂
  obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj'
  obtain ⟨x, hx₁, hx₂⟩ := hs₂.exists_isMaxOn hs f.continuous.continuousOn
  have : f x < u := hf₁ x (sU hx₁)
  exact
    ⟨f, (f x + u) / 2, u,
      fun a ha => by have := hx₂ ha; dsimp at this; linarith,
      by linarith,
      fun b hb => hf₂ b (tV hb)⟩

Depends on / 依赖: continuous, continuousOn, disj.exists_open_convexes, eq_empty_or_nonempty, exists_isMaxOn, exists_open_convexes, f.continuous.continuousOn, geometric_hahn_banach_open_open, linari, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty
-/
theorem geometric_hahn_banach_compact_closed (hs₁ : Convex Real s) (hs₂ : IsCompact s)
    (ht₁ : Convex Real t) (ht₂ : IsClosed t) (disj : Disjoint s t) :
    exists (f : StrongDual Real E) (u v : Real), (forall a in s, f a < u) ∧ u < v ∧ forall b in t, v < f b := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨0, -2, -1, by simp⟩
  obtain rfl | _ht := t.eq_empty_or_nonempty
  · exact ⟨0, 1, 2, by simp⟩
  obtain ⟨U, V, hU, hV, hU₁, hV₁, sU, tV, disj'⟩ := disj.exists_open_convexes hs₁ hs₂ ht₁ ht₂
  obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj'
  obtain ⟨x, hx₁, hx₂⟩ := hs₂.exists_isMaxOn hs f.continuous.continuousOn
  have : f x < u := hf₁ x (sU hx₁)
  exact
    ⟨f, (f x + u) / 2, u,
      fun a ha => by have := hx₂ ha; dsimp at this; linarith,
      by linarith,
      fun b hb => hf₂ b (tV hb)⟩

/--
theorem `geometric_hahn_banach_closed_compact` / 定理 `geometric_hahn_banach_closed_compact`

English:
theorem geometric_hahn_banach_closed_compact
  statement: (hs₁ : Convex Real s) (hs₂ : IsClosed s)
  proof: let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

中文:
定理 geometric_hahn_banach_closed_compact
  结论: (hs₁ : 凸 实数 s) (hs₂ : 是闭集 s)
  证明: let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

Depends on / 依赖: disj.symm, geometric_hahn_banach_compact_closed
-/
theorem geometric_hahn_banach_closed_compact (hs₁ : Convex Real s) (hs₂ : IsClosed s)
    (ht₁ : Convex Real t) (ht₂ : IsCompact t) (disj : Disjoint s t) :
    exists (f : StrongDual Real E) (u v : Real), (forall a in s, f a < u) ∧ u < v ∧ forall b in t, v < f b :=
  let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

/--
theorem `geometric_hahn_banach_point_closed` / 定理 `geometric_hahn_banach_point_closed`

English:
theorem geometric_hahn_banach_point_closed
  given: (ht₁ : Convex Real t) (ht₂ : IsClosed t) (disj : x ∉ t)
  proof: let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
⟨f, v, hst.trans' ha x mem_singleton _, hb⟩

中文:
定理 geometric_hahn_banach_point_closed
  条件: (ht₁ : 凸 实数 t) (ht₂ : 是闭集 t) (disj : x ∉ t)
  证明: let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
⟨f, v, hst.trans' ha x mem_singleton _, hb⟩

Depends on / 依赖: convex_singleton, disjoint_singleton_left, geometric_hahn_banach_compact_closed, hst.trans, isCompact_singleton, mem_singleton
-/
theorem geometric_hahn_banach_point_closed (ht₁ : Convex Real t) (ht₂ : IsClosed t) (disj : x ∉ t) :
    exists (f : StrongDual Real E) (u : Real), f x < u ∧ forall b in t, u < f b :=
  let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
⟨f, v, hst.trans' ha x mem_singleton _, hb⟩

/--
theorem `geometric_hahn_banach_closed_point` / 定理 `geometric_hahn_banach_closed_point`

English:
theorem geometric_hahn_banach_closed_point
  given: (hs₁ : Convex Real s) (hs₂ : IsClosed s) (disj : x ∉ s)
  proof: let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
⟨f, s, ha, hst.trans hb x mem_singleton _⟩

中文:
定理 geometric_hahn_banach_closed_point
  条件: (hs₁ : 凸 实数 s) (hs₂ : 是闭集 s) (disj : x ∉ s)
  证明: let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
⟨f, s, ha, hst.trans hb x mem_singleton _⟩

Depends on / 依赖: convex_singleton, disjoint_singleton_right, geometric_hahn_banach_closed_compact, hst.trans, isCompact_singleton, mem_singleton
-/
theorem geometric_hahn_banach_closed_point (hs₁ : Convex Real s) (hs₂ : IsClosed s) (disj : x ∉ s) :
    exists (f : StrongDual Real E) (u : Real), (forall a in s, f a < u) ∧ u < f x :=
  let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
⟨f, s, ha, hst.trans hb x mem_singleton _⟩

/--
theorem `geometric_hahn_banach_point_point` / 定理 `geometric_hahn_banach_point_point`

English:
theorem geometric_hahn_banach_point_point
  given: [T1Space E] (hxy : x != y)
  proof: by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩

中文:
定理 geometric_hahn_banach_point_point
  条件: [T1空间 E] (hxy : x != y)
  证明: by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩

Depends on / 依赖: convex_singleton, disjoint_singleton, geometric_hahn_banach_compact_closed, isClosed_singleton, isCompact_singleton
-/
theorem geometric_hahn_banach_point_point [T1Space E] (hxy : x != y) :
    exists f : StrongDual Real E, f x < f y := by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩

/--
theorem `iInter_halfSpaces_eq` / 定理 `iInter_halfSpaces_eq`

English:
theorem iInter_halfSpaces_eq
  given: (hs₁ : Convex Real s) (hs₂ : IsClosed s)
  proof: by
  rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra h
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).not_ge le_rfl

中文:
定理 i整数er_halfSpaces_eq
  条件: (hs₁ : 凸 实数 s) (hs₂ : 是闭集 s)
  证明: by
  rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra h
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).not_ge le_rfl

Depends on / 依赖: Set.Subset.antisymm, Set.iInter_ofPred, Subset, antisymm, geometric_hahn_banach_closed_point, hxy.trans_lt, iInter_ofPred, le_rfl, not_ge, trans_lt
-/
theorem iInter_halfSpaces_eq (hs₁ : Convex Real s) (hs₂ : IsClosed s) :
    ⋂ l : StrongDual Real E, { x | exists y in s, l x <= l y } = s := by
  rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra h
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).not_ge le_rfl
end

namespace RCLike

variable [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower Real 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/--
theorem `separate_convex_open_set` / 定理 `separate_convex_open_set`

English:
theorem separate_convex_open_set
  statement: {s : Set E}
  proof: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨g, hg⟩ := _root_.separate_convex_open_set hs₀ hs₁ hs₂ hx₀
  use g.extendRCLikeₗ
  simpa [g.extendRCLikeₗ_apply]

中文:
定理 separate_convex_open_set
  结论: {s : 集合 E}
  证明: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨g, hg⟩ := _root_.separate_convex_open_set hs₀ hs₁ hs₂ hx₀
  use g.extendRCLikeₗ
  simpa [g.extendRCLikeₗ_apply]

Depends on / 依赖: IsScalarTower, IsScalarTower.continuousSMul, _root_, _root_.separate_convex_open_set, continuousSMul, g.extendRCLike, separate_convex_open_set
-/
theorem separate_convex_open_set {s : Set E}
    (hs₀ : (0 : E) in s) (hs₁ : Convex Real s) (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) :
    exists f : StrongDual 𝕜 E, re (f x₀) = 1 ∧ forall x in s, re (f x) < 1 := by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨g, hg⟩ := _root_.separate_convex_open_set hs₀ hs₁ hs₂ hx₀
  use g.extendRCLikeₗ
  simpa [g.extendRCLikeₗ_apply]

/--
theorem `geometric_hahn_banach_open` / 定理 `geometric_hahn_banach_open`

English:
theorem geometric_hahn_banach_open
  statement: (hs₁ : Convex Real s) (hs₂ : IsOpen s) (ht : Convex Real t)
  proof: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, u, h⟩ := _root_.geometric_hahn_banach_open hs₁ hs₂ ht disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply] using Exists.intro u h

中文:
定理 geometric_hahn_banach_open
  结论: (hs₁ : 凸 实数 s) (hs₂ : 是开集 s) (ht : 凸 实数 t)
  证明: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, u, h⟩ := _root_.geometric_hahn_banach_open hs₁ hs₂ ht disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply] using Exists.intro u h

Depends on / 依赖: Exists, Exists.intro, IsScalarTower, IsScalarTower.continuousSMul, _root_, _root_.geometric_hahn_banach_open, continuousSMul, f.extendRCLike, geometric_hahn_banach_open
-/
theorem geometric_hahn_banach_open (hs₁ : Convex Real s) (hs₂ : IsOpen s) (ht : Convex Real t)
    (disj : Disjoint s t) : exists (f : StrongDual 𝕜 E) (u : Real), (forall a in s, re (f a) < u) ∧
    forall b in t, u <= re (f b) := by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, u, h⟩ := _root_.geometric_hahn_banach_open hs₁ hs₂ ht disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply] using Exists.intro u h

/--
theorem `geometric_hahn_banach_open_point` / 定理 `geometric_hahn_banach_open_point`

English:
theorem geometric_hahn_banach_open_point
  given: (hs₁ : Convex Real s) (hs₂ : IsOpen s) (disj : x ∉ s)
  proof: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, h⟩ := _root_.geometric_hahn_banach_open_point hs₁ hs₂ disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply]

中文:
定理 geometric_hahn_banach_open_point
  条件: (hs₁ : 凸 实数 s) (hs₂ : 是开集 s) (disj : x ∉ s)
  证明: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, h⟩ := _root_.geometric_hahn_banach_open_point hs₁ hs₂ disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply]

Depends on / 依赖: IsScalarTower, IsScalarTower.continuousSMul, _root_, _root_.geometric_hahn_banach_open_point, continuousSMul, f.extendRCLike, geometric_hahn_banach_open_point
-/
theorem geometric_hahn_banach_open_point (hs₁ : Convex Real s) (hs₂ : IsOpen s) (disj : x ∉ s) :
    exists f : StrongDual 𝕜 E, forall a in s, re (f a) < re (f x) := by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, h⟩ := _root_.geometric_hahn_banach_open_point hs₁ hs₂ disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply]

/--
theorem `geometric_hahn_banach_point_open` / 定理 `geometric_hahn_banach_point_open`

English:
theorem geometric_hahn_banach_point_open
  given: (ht₁ : Convex Real t) (ht₂ : IsOpen t) (disj : x ∉ t)
  proof: let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩

中文:
定理 geometric_hahn_banach_point_open
  条件: (ht₁ : 凸 实数 t) (ht₂ : 是开集 t) (disj : x ∉ t)
  证明: let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩

Depends on / 依赖: geometric_hahn_banach_open_point
-/
theorem geometric_hahn_banach_point_open (ht₁ : Convex Real t) (ht₂ : IsOpen t) (disj : x ∉ t) :
    exists f : StrongDual 𝕜 E, forall b in t, re (f x) < re (f b) :=
  let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩

/--
theorem `geometric_hahn_banach_open_open` / 定理 `geometric_hahn_banach_open_open`

English:
theorem geometric_hahn_banach_open_open
  statement: (hs₁ : Convex Real s) (hs₂ : IsOpen s)
  proof: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, u, h⟩ := _root_.geometric_hahn_banach_open_open hs₁ hs₂ ht₁ ht₃ disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply] using Exists.intro u h

中文:
定理 geometric_hahn_banach_open_open
  结论: (hs₁ : 凸 实数 s) (hs₂ : 是开集 s)
  证明: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, u, h⟩ := _root_.geometric_hahn_banach_open_open hs₁ hs₂ ht₁ ht₃ disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply] using Exists.intro u h

Depends on / 依赖: Exists, Exists.intro, IsScalarTower, IsScalarTower.continuousSMul, _root_, _root_.geometric_hahn_banach_open_open, continuousSMul, f.extendRCLike, geometric_hahn_banach_open_open
-/
theorem geometric_hahn_banach_open_open (hs₁ : Convex Real s) (hs₂ : IsOpen s)
    (ht₁ : Convex Real t) (ht₃ : IsOpen t) (disj : Disjoint s t) :
    exists (f : StrongDual 𝕜 E) (u : Real), (forall a in s, re (f a) < u) ∧ forall b in t, u < re (f b) := by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, u, h⟩ := _root_.geometric_hahn_banach_open_open hs₁ hs₂ ht₁ ht₃ disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply] using Exists.intro u h

/--
theorem `geometric_hahn_banach_of_nonempty_interior` / 定理 `geometric_hahn_banach_of_nonempty_interior`

English:
theorem geometric_hahn_banach_of_nonempty_interior
  proof: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, u, hfne, hA', hB'⟩ :=
    _root_.geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
  refine ⟨f.extendRCLikeₗ, u, fun hzero => ?_, ?_, ?_⟩
· exact hfne (StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).injective (by simpa using hzero)
  · simpa [f.extendRCLikeₗ_apply] using hA'
  · simpa [f.extendRCLikeₗ_apply] using hB'

中文:
定理 geometric_hahn_banach_of_nonempty_interior
  证明: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, u, hfne, hA', hB'⟩ :=
    _root_.geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
  refine ⟨f.extendRCLikeₗ, u, fun hzero => ?_, ?_, ?_⟩
· exact hfne (StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).injective (by simpa using hzero)
  · simpa [f.extendRCLikeₗ_apply] using hA'
  · simpa [f.extendRCLikeₗ_apply] using hB'

Depends on / 依赖: IsScalarTower, IsScalarTower.continuousSMul, StrongDual, StrongDual.extendRCLike, _root_, _root_.geometric_hahn_banach_of_nonempty_interior, continuousSMul, f.extendRCLike, geometric_hahn_banach_of_nonempty_interior, injective
-/
theorem geometric_hahn_banach_of_nonempty_interior
  (hs : Convex Real s) (ht : Convex Real t) (hst : Disjoint (interior s) t)
    (hsint : (interior s).Nonempty) (htne : t.Nonempty) :
    exists (f : StrongDual 𝕜 E) (u : Real), f != 0 ∧ (forall a in s, re (f a) <= u) ∧ forall b in t, u <= re (f b) := by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, u, hfne, hA', hB'⟩ :=
    _root_.geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
  refine ⟨f.extendRCLikeₗ, u, fun hzero => ?_, ?_, ?_⟩
· exact hfne (StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).injective (by simpa using hzero)
  · simpa [f.extendRCLikeₗ_apply] using hA'
  · simpa [f.extendRCLikeₗ_apply] using hB'

/--
theorem `geometric_hahn_banach_of_nonempty_interior'` / 定理 `geometric_hahn_banach_of_nonempty_interior'`

English:
theorem geometric_hahn_banach_of_nonempty_interior'
  proof: by
  by_cases htne : t.Nonempty
  · have hsep :
        exists (f : StrongDual 𝕜 E) (u : Real),
          f != 0 ∧ (forall a in s, re (f a) <= u) ∧ forall b in t, u <= re (f b) :=
        geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
    obtain ⟨f, u, -, hs', ht'⟩ := hsep
    exact ⟨f, u, hs', ht'⟩
  · exact ⟨0, 0, by simp⟩

中文:
定理 geometric_hahn_banach_of_nonempty_interior'
  证明: by
  by_cases htne : t.Nonempty
  · have hsep :
        exists (f : StrongDual 𝕜 E) (u : Real),
          f != 0 ∧ (forall a in s, re (f a) <= u) ∧ forall b in t, u <= re (f b) :=
        geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
    obtain ⟨f, u, -, hs', ht'⟩ := hsep
    exact ⟨f, u, hs', ht'⟩
  · exact ⟨0, 0, by simp⟩

Depends on / 依赖: Nonempty, StrongDual, geometric_hahn_banach_of_nonempty_interior, t.Nonempty
-/
theorem geometric_hahn_banach_of_nonempty_interior'
  (hs : Convex Real s) (ht : Convex Real t) (hst : Disjoint (interior s) t)
    (hsint : (interior s).Nonempty) :
    exists (f : StrongDual 𝕜 E) (u : Real), (forall a in s, re (f a) <= u) ∧ forall b in t, u <= re (f b) := by
  by_cases htne : t.Nonempty
  · have hsep :
        exists (f : StrongDual 𝕜 E) (u : Real),
          f != 0 ∧ (forall a in s, re (f a) <= u) ∧ forall b in t, u <= re (f b) :=
        geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
    obtain ⟨f, u, -, hs', ht'⟩ := hsep
    exact ⟨f, u, hs', ht'⟩
  · exact ⟨0, 0, by simp⟩

/--
theorem `geometric_hahn_banach_of_nonempty_interior_point` / 定理 `geometric_hahn_banach_of_nonempty_interior_point`

English:
theorem geometric_hahn_banach_of_nonempty_interior_point
  proof: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, hfne, hA'⟩ := _root_.geometric_hahn_banach_of_nonempty_interior_point hA hxA hAint
  refine ⟨f.extendRCLikeₗ, fun hzero => ?_, ?_⟩
· exact hfne (StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).injective (by simpa using hzero)
  · simpa [f.extendRCLikeₗ_apply] using hA'

中文:
定理 geometric_hahn_banach_of_nonempty_interior_point
  证明: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, hfne, hA'⟩ := _root_.geometric_hahn_banach_of_nonempty_interior_point hA hxA hAint
  refine ⟨f.extendRCLikeₗ, fun hzero => ?_, ?_⟩
· exact hfne (StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).injective (by simpa using hzero)
  · simpa [f.extendRCLikeₗ_apply] using hA'

Depends on / 依赖: IsScalarTower, IsScalarTower.continuousSMul, StrongDual, StrongDual.extendRCLike, _root_, _root_.geometric_hahn_banach_of_nonempty_interior_point, continuousSMul, f.extendRCLike, geometric_hahn_banach_of_nonempty_interior_point, injective
-/
theorem geometric_hahn_banach_of_nonempty_interior_point
    {A : Set E} (hA : Convex Real A) (hxA : x ∉ interior A) (hAint : (interior A).Nonempty) :
    exists f : StrongDual 𝕜 E, f != 0 ∧ forall a in A, re (f a) <= re (f x) := by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨f, hfne, hA'⟩ := _root_.geometric_hahn_banach_of_nonempty_interior_point hA hxA hAint
  refine ⟨f.extendRCLikeₗ, fun hzero => ?_, ?_⟩
· exact hfne (StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).injective (by simpa using hzero)
  · simpa [f.extendRCLikeₗ_apply] using hA'

variable [LocallyConvexSpace Real E]

/--
theorem `geometric_hahn_banach_compact_closed` / 定理 `geometric_hahn_banach_compact_closed`

English:
theorem geometric_hahn_banach_compact_closed
  statement: (hs₁ : Convex Real s) (hs₂ : IsCompact s)
  proof: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨g, u, v, h1⟩ := _root_.geometric_hahn_banach_compact_closed hs₁ hs₂ ht₁ ht₂ disj
  use g.extendRCLikeₗ
  simpa [g.extendRCLikeₗ_apply, exists_and_left] using ⟨u, h1.1, v, h1.2⟩

中文:
定理 geometric_hahn_banach_compact_closed
  结论: (hs₁ : 凸 实数 s) (hs₂ : 是紧集 s)
  证明: by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨g, u, v, h1⟩ := _root_.geometric_hahn_banach_compact_closed hs₁ hs₂ ht₁ ht₂ disj
  use g.extendRCLikeₗ
  simpa [g.extendRCLikeₗ_apply, exists_and_left] using ⟨u, h1.1, v, h1.2⟩

Depends on / 依赖: IsScalarTower, IsScalarTower.continuousSMul, _root_, _root_.geometric_hahn_banach_compact_closed, continuousSMul, exists_and_left, g.extendRCLike, geometric_hahn_banach_compact_closed
-/
theorem geometric_hahn_banach_compact_closed (hs₁ : Convex Real s) (hs₂ : IsCompact s)
    (ht₁ : Convex Real t) (ht₂ : IsClosed t) (disj : Disjoint s t) :
    exists (f : StrongDual 𝕜 E) (u v : Real), (forall a in s, re (f a) < u) ∧ u < v ∧ forall b in t, v < re (f b) := by
  have := IsScalarTower.continuousSMul (M := Real) (α := E) 𝕜
  obtain ⟨g, u, v, h1⟩ := _root_.geometric_hahn_banach_compact_closed hs₁ hs₂ ht₁ ht₂ disj
  use g.extendRCLikeₗ
  simpa [g.extendRCLikeₗ_apply, exists_and_left] using ⟨u, h1.1, v, h1.2⟩

/--
theorem `geometric_hahn_banach_closed_compact` / 定理 `geometric_hahn_banach_closed_compact`

English:
theorem geometric_hahn_banach_closed_compact
  statement: (hs₁ : Convex Real s) (hs₂ : IsClosed s)
  proof: let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

中文:
定理 geometric_hahn_banach_closed_compact
  结论: (hs₁ : 凸 实数 s) (hs₂ : 是闭集 s)
  证明: let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

Depends on / 依赖: NonUnitalSeminormedRing, NonUnitalSeminormedRing.toContinuousMul, disj.symm, geometric_hahn_banach_compact_closed, toContinuousMul
-/
theorem geometric_hahn_banach_closed_compact (hs₁ : Convex Real s) (hs₂ : IsClosed s)
    (ht₁ : Convex Real t) (ht₂ : IsCompact t) (disj : Disjoint s t) :
    exists (f : StrongDual 𝕜 E) (u v : Real), (forall a in s, re (f a) < u) ∧ u < v ∧ forall b in t, v < re (f b) :=
  let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩

/--
theorem `geometric_hahn_banach_point_closed` / 定理 `geometric_hahn_banach_point_closed`

English:
theorem geometric_hahn_banach_point_closed
  statement: (ht₁ : Convex Real t) (ht₂ : IsClosed t)
  proof: let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
⟨f, v, hst.trans' ha x mem_singleton _, hb⟩

中文:
定理 geometric_hahn_banach_point_closed
  结论: (ht₁ : 凸 实数 t) (ht₂ : 是闭集 t)
  证明: let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
⟨f, v, hst.trans' ha x mem_singleton _, hb⟩

Depends on / 依赖: NonUnitalSeminormedRing, NonUnitalSeminormedRing.toIsTopologicalRing, convex_singleton, disjoint_singleton_left, geometric_hahn_banach_compact_closed, hst.trans, isCompact_singleton, mem_singleton, toIsTopologicalRing
-/
theorem geometric_hahn_banach_point_closed (ht₁ : Convex Real t) (ht₂ : IsClosed t)
    (disj : x ∉ t) : exists (f : StrongDual 𝕜 E) (u : Real), re (f x) < u ∧ forall b in t, u < re (f b) :=
  let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
⟨f, v, hst.trans' ha x mem_singleton _, hb⟩

/--
theorem `geometric_hahn_banach_closed_point` / 定理 `geometric_hahn_banach_closed_point`

English:
theorem geometric_hahn_banach_closed_point
  statement: (hs₁ : Convex Real s) (hs₂ : IsClosed s)
  proof: let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
⟨f, s, ha, hst.trans hb x mem_singleton _⟩

中文:
定理 geometric_hahn_banach_closed_point
  结论: (hs₁ : 凸 实数 s) (hs₂ : 是闭集 s)
  证明: let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
⟨f, s, ha, hst.trans hb x mem_singleton _⟩

Depends on / 依赖: convex_singleton, disjoint_singleton_right, geometric_hahn_banach_closed_compact, hst.trans, isCompact_singleton, mem_singleton
-/
theorem geometric_hahn_banach_closed_point (hs₁ : Convex Real s) (hs₂ : IsClosed s)
    (disj : x ∉ s) : exists (f : StrongDual 𝕜 E) (u : Real), (forall a in s, re (f a) < u) ∧ u < re (f x) :=
  let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
⟨f, s, ha, hst.trans hb x mem_singleton _⟩

/--
theorem `geometric_hahn_banach_point_point` / 定理 `geometric_hahn_banach_point_point`

English:
theorem geometric_hahn_banach_point_point
  given: [T1Space E] (hxy : x != y)
  proof: by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (𝕜 := 𝕜) (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩

中文:
定理 geometric_hahn_banach_point_point
  条件: [T1空间 E] (hxy : x != y)
  证明: by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (𝕜 := 𝕜) (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩

Depends on / 依赖: convex_singleton, disjoint_singleton, geometric_hahn_banach_compact_closed, isClosed_singleton, isCompact_singleton
-/
theorem geometric_hahn_banach_point_point [T1Space E] (hxy : x != y) :
    exists f : StrongDual 𝕜 E, re (f x) < re (f y) := by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (𝕜 := 𝕜) (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩

/--
theorem `iInter_halfSpaces_eq` / 定理 `iInter_halfSpaces_eq`

English:
theorem iInter_halfSpaces_eq
  given: (hs₁ : Convex Real s) (hs₂ : IsClosed s)
  proof: by
  rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra h
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point (𝕜 := 𝕜) hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).false

中文:
定理 i整数er_halfSpaces_eq
  条件: (hs₁ : 凸 实数 s) (hs₂ : 是闭集 s)
  证明: by
  rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra h
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point (𝕜 := 𝕜) hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).false

Depends on / 依赖: Set.Subset.antisymm, Set.iInter_ofPred, Subset, antisymm, geometric_hahn_banach_closed_point, hxy.trans_lt, iInter_ofPred, le_rfl, trans_lt
-/
theorem iInter_halfSpaces_eq (hs₁ : Convex Real s) (hs₂ : IsClosed s) :
    ⋂ l : StrongDual 𝕜 E, { x | exists y in s, re (l x) <= re (l y) } = s := by
  rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra h
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point (𝕜 := 𝕜) hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).false

/--
theorem `iInter_halfSpaces_eq'` / 定理 `iInter_halfSpaces_eq'`

English:
theorem iInter_halfSpaces_eq'
  given: (hs₁ : Convex Real s) (hs₂ : IsClosed s)
  proof: by
  simp_rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l c hc => hc x hx
  by_contra h
  obtain ⟨l, c, hls, hl⟩ := geometric_hahn_banach_closed_point (𝕜 := 𝕜) hs₁ hs₂ h
  exact (hl.trans_le (hx l c (fun y hy => (hls y hy).le))).false

中文:
定理 i整数er_halfSpaces_eq'
  条件: (hs₁ : 凸 实数 s) (hs₂ : 是闭集 s)
  证明: by
  simp_rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l c hc => hc x hx
  by_contra h
  obtain ⟨l, c, hls, hl⟩ := geometric_hahn_banach_closed_point (𝕜 := 𝕜) hs₁ hs₂ h
  exact (hl.trans_le (hx l c (fun y hy => (hls y hy).le))).false

Depends on / 依赖: Set.Subset.antisymm, Set.iInter_ofPred, Subset, antisymm, geometric_hahn_banach_closed_point, hl.trans_le, iInter_ofPred, simp_rw, trans_le
-/
theorem iInter_halfSpaces_eq' (hs₁ : Convex Real s) (hs₂ : IsClosed s) :
    ⋂ (l : StrongDual 𝕜 E) (c : Real) (_ : forall y in s, re (l y) <= c), { x | re (l x) <= c } = s := by
  simp_rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l c hc => hc x hx
  by_contra h
  obtain ⟨l, c, hls, hl⟩ := geometric_hahn_banach_closed_point (𝕜 := 𝕜) hs₁ hs₂ h
  exact (hl.trans_le (hx l c (fun y hy => (hls y hy).le))).false

/--
theorem `iInter_countable_halfSpaces_eq` / 定理 `iInter_countable_halfSpaces_eq`

English:
theorem iInter_countable_halfSpaces_eq
  statement: [HereditarilyLindelofSpace E]
  proof: by
  set ι := Σ (l : StrongDual 𝕜 E), { c : Real // forall y in s, re (l y) <= c }
  set l : ι -> StrongDual 𝕜 E := fun lc => lc.1
  set c : ι -> Real := fun lc => lc.2.val
  set hc : forall i, forall y in s, re (l i y) <= c i := fun lc => lc.2.prop
  have : Nonempty ι := ⟨0, 0, fun _ _ => by simp⟩
  have : ⋂ i : ι, { x | re (l i x) <= c i } = s := by
    simpa only [ι, iInter_sigma, iInter_subtype, l, c] using iInter_halfSpaces_eq' hs₁ hs₂
  obtain ⟨k, hk⟩ := eq_closed_inter_nat (fun i : ι => { x | re (l i x) <= c i })
    (fun i => isClosed_le (continuous_re.comp (l i).continuous) continuous_const)
  exact ⟨l ∘ k, c ∘ k, hk.trans this⟩

中文:
定理 i整数er_countable_halfSpaces_eq
  结论: [HereditarilyLindelof空间 E]
  证明: by
  set ι := Σ (l : StrongDual 𝕜 E), { c : Real // forall y in s, re (l y) <= c }
  set l : ι -> StrongDual 𝕜 E := fun lc => lc.1
  set c : ι -> Real := fun lc => lc.2.val
  set hc : forall i, forall y in s, re (l i y) <= c i := fun lc => lc.2.prop
  have : Nonempty ι := ⟨0, 0, fun _ _ => by simp⟩
  have : ⋂ i : ι, { x | re (l i x) <= c i } = s := by
    simpa only [ι, iInter_sigma, iInter_subtype, l, c] using iInter_halfSpaces_eq' hs₁ hs₂
  obtain ⟨k, hk⟩ := eq_closed_inter_nat (fun i : ι => { x | re (l i x) <= c i })
    (fun i => isClosed_le (continuous_re.comp (l i).continuous) continuous_const)
  exact ⟨l ∘ k, c ∘ k, hk.trans this⟩

Depends on / 依赖: Nonempty, StrongDual, eq_closed_inter_nat, iInter_halfSpaces_eq, iInter_sigma, iInter_subtype
-/
theorem iInter_countable_halfSpaces_eq [HereditarilyLindelofSpace E]
    (hs₁ : Convex Real s) (hs₂ : IsClosed s) :
    exists l : Nat -> StrongDual 𝕜 E, exists c : Nat -> Real, ⋂ n, { x | re (l n x) <= c n } = s := by
  set ι := Σ (l : StrongDual 𝕜 E), { c : Real // forall y in s, re (l y) <= c }
  set l : ι -> StrongDual 𝕜 E := fun lc => lc.1
  set c : ι -> Real := fun lc => lc.2.val
  set hc : forall i, forall y in s, re (l i y) <= c i := fun lc => lc.2.prop
  have : Nonempty ι := ⟨0, 0, fun _ _ => by simp⟩
  have : ⋂ i : ι, { x | re (l i x) <= c i } = s := by
    simpa only [ι, iInter_sigma, iInter_subtype, l, c] using iInter_halfSpaces_eq' hs₁ hs₂
  obtain ⟨k, hk⟩ := eq_closed_inter_nat (fun i : ι => { x | re (l i x) <= c i })
    (fun i => isClosed_le (continuous_re.comp (l i).continuous) continuous_const)
  exact ⟨l ∘ k, c ∘ k, hk.trans this⟩

end RCLike
