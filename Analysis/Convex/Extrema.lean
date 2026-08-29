/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Minima and maxima of convex functions

We show that if a function `f : E → β` is convex, then a local minimum is also
a global minimum, and likewise for concave functions.
-/

public section


variable {E β : Type*} [AddCommGroup E] [TopologicalSpace E] [Module Real E] [IsTopologicalAddGroup E]
  [ContinuousSMul Real E] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module Real β] [IsOrderedModule Real β] [PosSMulReflectLE Real β] {s : Set E}

open Set Filter Function Topology

/--
theorem `IsMinOn.of_isLocalMinOn_of_convexOn_Icc` / 定理 `IsMinOn.of_isLocalMinOn_of_convexOn_Icc`

English:
theorem IsMinOn.of_isLocalMinOn_of_convexOn_Icc
  statement: {f : Real -> β} {a b : Real} (a_lt_b : a < b)
  proof: by
  rintro c hc
  dsimp only [mem_ofPred_eq]
  rw [IsLocalMinOn]; rw [nhdsWithin_Icc_eq_nhdsGE a_lt_b] at h_local_min
  rcases hc.1.eq_or_lt with (rfl | a_lt_c)
  · exact le_rfl
  have H₁ : forallᶠ y in 𝓝[>] a, f a <= f y :=
    h_local_min.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have

中文:
定理 IsMinOn.of_isLocalMinOn_of_convexOn_Icc
  结论: {f : 实数 -> β} {a b : 实数} (a_lt_b : a < b)
  证明: by
  rintro c hc
  dsimp only [mem_ofPred_eq]
  rw [IsLocalMinOn]; rw [nhdsWithin_Icc_eq_nhdsGE a_lt_b] at h_local_min
  rcases hc.1.eq_or_lt with (rfl | a_lt_c)
  · exact le_rfl
  have H₁ : forallᶠ y in 𝓝[>] a, f a <= f y :=
    h_local_min.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have

Depends on / 依赖: Convex, Convex.mem_Ioc, Ioc_mem_nhdsGT, Ioi_subset_Ici_self, IsLocalMinOn, a_lt_b, a_lt_c, eq_or_lt, filter_mono, h_local_min, h_local_min.filter_mono, hy_ac, le_rfl, mem_Ioc, mem_ofPred_eq, nhdsWithin_Icc_eq_nhdsGE, nhdsWithin_mono
-/
theorem IsMinOn.of_isLocalMinOn_of_convexOn_Icc {f : Real -> β} {a b : Real} (a_lt_b : a < b)
    (h_local_min : IsLocalMinOn f (Icc a b) a) (h_conv : ConvexOn Real (Icc a b) f) :
    IsMinOn f (Icc a b) a := by
  rintro c hc
  dsimp only [mem_ofPred_eq]
  rw [IsLocalMinOn]; rw [nhdsWithin_Icc_eq_nhdsGE a_lt_b] at h_local_min
  rcases hc.1.eq_or_lt with (rfl | a_lt_c)
  · exact le_rfl
  have H₁ : forallᶠ y in 𝓝[>] a, f a <= f y :=
    h_local_min.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have H₂ : forallᶠ y in 𝓝[>] a, y in Ioc a c := Ioc_mem_nhdsGT a_lt_c
  rcases (H₁.and H₂).exists with ⟨y, hfy, hy_ac⟩
  rcases (Convex.mem_Ioc a_lt_c).mp hy_ac with ⟨ya, yc, ya₀, yc₀, yac, rfl⟩
  suffices ya • f a + yc • f a <= ya • f a + yc • f c from
    (smul_le_smul_iff_of_pos_left yc₀).1 (le_of_add_le_add_left this)
  calc
    ya • f a + yc • f a = f a := by rw [← add_smul, yac, one_smul]
    _ <= f (ya * a + yc * c) := hfy
    _ <= ya • f a + yc • f c := h_conv.2 (left_mem_Icc.2 a_lt_b.le) hc ya₀ yc₀.le yac

/--
theorem `IsMinOn.of_isLocalMinOn_of_convexOn` / 定理 `IsMinOn.of_isLocalMinOn_of_convexOn`

English:
theorem IsMinOn.of_isLocalMinOn_of_convexOn
  statement: {f : E -> β} {a : E} (a_in_s : a in s)
  proof: by
  intro x x_in_s
  let g : Real ->ᵃ[Real] E := AffineMap.lineMap a x
  have hg0 : g 0 = a := AffineMap.lineMap_apply_zero a x
  have hg1 : g 1 = x := AffineMap.lineMap_apply_one a x
  have hgc : Continuous g := AffineMap.lineMap_continuous
  have h_maps : MapsTo g (Icc 0 1) s := by
    simpa only

中文:
定理 IsMinOn.of_isLocalMinOn_of_convexOn
  结论: {f : E -> β} {a : E} (a_in_s : a in s)
  证明: by
  intro x x_in_s
  let g : Real ->ᵃ[Real] E := AffineMap.lineMap a x
  have hg0 : g 0 = a := AffineMap.lineMap_apply_zero a x
  have hg1 : g 1 = x := AffineMap.lineMap_apply_one a x
  have hgc : Continuous g := AffineMap.lineMap_continuous
  have h_maps : MapsTo g (Icc 0 1) s := by
    simpa only

Depends on / 依赖: AffineMap, AffineMap.lineMap, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, AffineMap.lineMap_continuous, Continuous, IsLocalMinOn, MapsTo, a_in_s, comp_conti, fg_local_min_on, h_conv, h_localmin, h_localmin.comp_conti, h_maps, lineMap, lineMap_apply_one, lineMap_apply_zero, lineMap_continuous, mapsTo_iff_image_subset
-/
theorem IsMinOn.of_isLocalMinOn_of_convexOn {f : E -> β} {a : E} (a_in_s : a in s)
    (h_localmin : IsLocalMinOn f s a) (h_conv : ConvexOn Real s f) : IsMinOn f s a := by
  intro x x_in_s
  let g : Real ->ᵃ[Real] E := AffineMap.lineMap a x
  have hg0 : g 0 = a := AffineMap.lineMap_apply_zero a x
  have hg1 : g 1 = x := AffineMap.lineMap_apply_one a x
  have hgc : Continuous g := AffineMap.lineMap_continuous
  have h_maps : MapsTo g (Icc 0 1) s := by
    simpa only [g, mapsTo_iff_image_subset, ← segment_eq_image_lineMap]
      using h_conv.1.segment_subset a_in_s x_in_s
  have fg_local_min_on : IsLocalMinOn (f ∘ g) (Icc 0 1) 0 := by
    rw [← hg0] at h_localmin
    exact h_localmin.comp_continuousOn h_maps hgc.continuousOn (left_mem_Icc.2 zero_le_one)
  have fg_min_on : IsMinOn (f ∘ g) (Icc 0 1 : Set Real) 0 := by
    refine IsMinOn.of_isLocalMinOn_of_convexOn_Icc one_pos fg_local_min_on ?_
    exact (h_conv.comp_affineMap g).subset h_maps (convex_Icc 0 1)
  simpa only [hg0, hg1, comp_apply, mem_ofPred_eq] using fg_min_on (right_mem_Icc.2 zero_le_one)

/--
theorem `IsMaxOn.of_isLocalMaxOn_of_concaveOn` / 定理 `IsMaxOn.of_isLocalMaxOn_of_concaveOn`

English:
theorem IsMaxOn.of_isLocalMaxOn_of_concaveOn
  statement: {f : E -> β} {a : E} (a_in_s : a in s)
  proof: IsMinOn.of_isLocalMinOn_of_convexOn (β := βᵒᵈ) a_in_s h_localmax h_conc

中文:
定理 IsMaxOn.of_isLocalMaxOn_of_concaveOn
  结论: {f : E -> β} {a : E} (a_in_s : a in s)
  证明: IsMinOn.of_isLocalMinOn_of_convexOn (β := βᵒᵈ) a_in_s h_localmax h_conc

Depends on / 依赖: IsMinOn, IsMinOn.of_isLocalMinOn_of_convexOn, a_in_s, h_conc, h_localmax, of_isLocalMinOn_of_convexOn
-/
theorem IsMaxOn.of_isLocalMaxOn_of_concaveOn {f : E -> β} {a : E} (a_in_s : a in s)
    (h_localmax : IsLocalMaxOn f s a) (h_conc : ConcaveOn Real s f) : IsMaxOn f s a :=
  IsMinOn.of_isLocalMinOn_of_convexOn (β := βᵒᵈ) a_in_s h_localmax h_conc

/--
theorem `IsMinOn.of_isLocalMin_of_convex_univ` / 定理 `IsMinOn.of_isLocalMin_of_convex_univ`

English:
theorem IsMinOn.of_isLocalMin_of_convex_univ
  statement: {f : E -> β} {a : E} (h_local_min : IsLocalMin f a)
  proof: fun x =>
  (IsMinOn.of_isLocalMinOn_of_convexOn (mem_univ a) (h_local_min.on univ) h_conv) (mem_univ x)

中文:
定理 IsMinOn.of_isLocalMin_of_convex_univ
  结论: {f : E -> β} {a : E} (h_local_min : IsLocalMin f a)
  证明: fun x =>
  (IsMinOn.of_isLocalMinOn_of_convexOn (mem_univ a) (h_local_min.on univ) h_conv) (mem_univ x)
-/
theorem IsMinOn.of_isLocalMin_of_convex_univ {f : E -> β} {a : E} (h_local_min : IsLocalMin f a)
    (h_conv : ConvexOn Real univ f) : forall x, f a <= f x := fun x =>
  (IsMinOn.of_isLocalMinOn_of_convexOn (mem_univ a) (h_local_min.on univ) h_conv) (mem_univ x)

/--
theorem `IsMaxOn.of_isLocalMax_of_convex_univ` / 定理 `IsMaxOn.of_isLocalMax_of_convex_univ`

English:
theorem IsMaxOn.of_isLocalMax_of_convex_univ
  statement: {f : E -> β} {a : E} (h_local_max : IsLocalMax f a)
  proof: IsMinOn.of_isLocalMin_of_convex_univ (β := βᵒᵈ) h_local_max h_conc

中文:
定理 IsMaxOn.of_isLocalMax_of_convex_univ
  结论: {f : E -> β} {a : E} (h_local_max : IsLocalMax f a)
  证明: IsMinOn.of_isLocalMin_of_convex_univ (β := βᵒᵈ) h_local_max h_conc

Depends on / 依赖: IsMinOn, IsMinOn.of_isLocalMin_of_convex_univ, h_conc, h_local_max, of_isLocalMin_of_convex_univ
-/
theorem IsMaxOn.of_isLocalMax_of_convex_univ {f : E -> β} {a : E} (h_local_max : IsLocalMax f a)
    (h_conc : ConcaveOn Real univ f) : forall x, f x <= f a :=
  IsMinOn.of_isLocalMin_of_convex_univ (β := βᵒᵈ) h_local_max h_conc
