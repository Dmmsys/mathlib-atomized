/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.Convex.Function

/-!
# Convex and concave piecewise functions

This file proves convex and concave theorems for piecewise functions.

## Main statements

* `convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici` is the proof that the piecewise
  function `(Set.Iic e).piecewise f g` of a function `f` decreasing and convex on `Set.Iic e` and a
  function `g` increasing and convex on `Set.Ici e`, such that `f e = g e`, is convex on the
  universal set.

  This version has the boundary point included in the left-hand function.

  See `convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic` for the version with the
  boundary point included in the right-hand function.

  See concave version(s) `concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici`
  and `concaveOn_univ_piecewise_Ici_of_antitoneOn_Ici_monotoneOn_Iic`.
-/

public section


variable {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E]
  [PosSMulMono 𝕜 E] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module 𝕜 β] [PosSMulMono 𝕜 β] {e : E} {f g : E -> β}

/--
theorem `convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici` / 定理 `convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici`

English:
theorem convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
  proof: by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain hx | hx := le_or_gt x e <;> obtain hy | hy := le_or_gt y e
  · have hc : a • x + b • y <= e := (Convex.combo_le_max x y ha hb hab).trans (max_le hx hy)
    rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hx]; rw [Set.piecewise_eq_of_mem

中文:
定理 convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
  证明: by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain hx | hx := le_or_gt x e <;> obtain hy | hy := le_or_gt y e
  · have hc : a • x + b • y <= e := (Convex.combo_le_max x y ha hb hab).trans (max_le hx hy)
    rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hx]; rw [Set.piecewise_eq_of_mem

Depends on / 依赖: Convex, Convex.combo_le_max, Set.Iic, Set.notMem_Iic.mpr, Set.piecewise_eq_of_mem, Set.piecewise_eq_of_notMem, combo_le_max, convex_univ, le_or_gt, max_le, notMem_Iic, piecewise_eq_of_mem, piecewise_eq_of_notMem
-/
theorem convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    (hf : ConvexOn 𝕜 (Set.Iic e) f) (hg : ConvexOn 𝕜 (Set.Ici e) g)
    (h_anti : AntitoneOn f (Set.Iic e)) (h_mono : MonotoneOn g (Set.Ici e)) (h_eq : f e = g e) :
    ConvexOn 𝕜 Set.univ ((Set.Iic e).piecewise f g) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain hx | hx := le_or_gt x e <;> obtain hy | hy := le_or_gt y e
  · have hc : a • x + b • y <= e := (Convex.combo_le_max x y ha hb hab).trans (max_le hx hy)
    rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hx]; rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hy]; rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hc]
    exact hf.2 hx hy ha hb hab
  · rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hx,
      Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hy)]
    obtain hc | hc := le_or_gt (a • x + b • y) e
    · rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hc]
      have hc' : a • x + b • e <= a • x + b • y := by gcongr
      trans a • f x + b • f e
      · exact (h_anti (hc'.trans hc) hc hc').trans (hf.2 hx Set.self_mem_Iic ha hb hab)
      · rw [h_eq]
        gcongr
        exact h_mono Set.self_mem_Ici hy.le hy.le
    · rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hc)]
      have hc' : a • x + b • y <= a • e + b • y := by gcongr
      trans a • g e + b • g y
      · exact (h_mono hc.le (hc.le.trans hc') hc').trans (hg.2 Set.self_mem_Ici hy.le ha hb hab)
      · rw [← h_eq]
        gcongr
        exact h_anti hx Set.self_mem_Iic hx
  · rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hx),
      Set.piecewise_eq_of_mem (Set.Iic e) f g hy]
    obtain hc | hc := le_or_gt (a • x + b • y) e
    · rw [Set.piecewise_eq_of_mem (Set.Iic e) f g hc]
      have hc' : a • e + b • y <= a • x + b • y := by gcongr
      trans a • f e + b • f y
      · exact (h_anti (hc'.trans hc) hc hc').trans (hf.2 Set.self_mem_Iic hy ha hb hab)
      · rw [h_eq]
        gcongr
        exact h_mono Set.self_mem_Ici hx.le hx.le
    · rw [Set.piecewise_eq_of_notMem (Set.Iic e) f g (Set.notMem_Iic.mpr hc)]
      have hc' : a • x + b • y <= a • x + b • e := by gcongr
      trans a • g x + b • g e
      · exact (h_mono hc.le (hc.le.trans hc') hc').trans (hg.2 hx.le Set.self_mem_Ici ha hb hab)
      · rw [← h_eq]
        gcongr
        exact h_anti hy Set.self_mem_Iic hy
  · have hc : e < a • x + b • y :=
        (lt_min hx hy).trans_le (Convex.min_le_combo x y ha hb hab)
    rw [(Set.Iic e).piecewise_eq_of_notMem f g (Set.notMem_Iic.mpr hx)]; rw [(Set.Iic e).piecewise_eq_of_notMem f g (Set.notMem_Iic.mpr hy)]; rw [(Set.Iic e).piecewise_eq_of_notMem f g (Set.notMem_Iic.mpr hc)]
    exact hg.2 hx.le hy.le ha hb hab

/--
theorem `convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic` / 定理 `convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic`

English:
theorem convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
  proof: by
  have h_piecewise_Ici_eq_piecewise_Iic :
      (Set.Ici e).piecewise f g = (Set.Iic e).piecewise g f := by
    ext x; by_cases hx : x = e
      <;> simp [Set.piecewise, @le_iff_lt_or_eq _ _ x e, ← @ite_not _ (e <= _), hx, h_eq]
  rw [h_piecewise_Ici_eq_piecewise_Iic]
  exact convexOn_univ_piecew

中文:
定理 convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
  证明: by
  have h_piecewise_Ici_eq_piecewise_Iic :
      (Set.Ici e).piecewise f g = (Set.Iic e).piecewise g f := by
    ext x; by_cases hx : x = e
      <;> simp [Set.piecewise, @le_iff_lt_or_eq _ _ x e, ← @ite_not _ (e <= _), hx, h_eq]
  rw [h_piecewise_Ici_eq_piecewise_Iic]
  exact convexOn_univ_piecew

Depends on / 依赖: Set.Ici, Set.Iic, Set.piecewise, convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici, h_anti, h_eq, h_eq.symm, h_mono, h_piecewise_Ici_eq_piecewise_Iic, ite_not, le_iff_lt_or_eq, piecewise
-/
theorem convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    (hf : ConvexOn 𝕜 (Set.Ici e) f) (hg : ConvexOn 𝕜 (Set.Iic e) g)
    (h_mono : MonotoneOn f (Set.Ici e)) (h_anti : AntitoneOn g (Set.Iic e)) (h_eq : f e = g e) :
    ConvexOn 𝕜 Set.univ ((Set.Ici e).piecewise f g) := by
  have h_piecewise_Ici_eq_piecewise_Iic :
      (Set.Ici e).piecewise f g = (Set.Iic e).piecewise g f := by
    ext x; by_cases hx : x = e
      <;> simp [Set.piecewise, @le_iff_lt_or_eq _ _ x e, ← @ite_not _ (e <= _), hx, h_eq]
  rw [h_piecewise_Ici_eq_piecewise_Iic]
  exact convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici hg hf h_anti h_mono h_eq.symm

/--
theorem `concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici` / 定理 `concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici`

English:
theorem concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici
  proof: by
  rw [← neg_convexOn_iff]; rw [← Set.piecewise_neg]
  exact convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    hf.neg hg.neg h_mono.neg h_anti.neg (neg_inj.mpr h_eq)

中文:
定理 concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici
  证明: by
  rw [← neg_convexOn_iff]; rw [← Set.piecewise_neg]
  exact convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    hf.neg hg.neg h_mono.neg h_anti.neg (neg_inj.mpr h_eq)

Depends on / 依赖: Set.piecewise_neg, convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici, h_anti, h_anti.neg, h_eq, h_mono, h_mono.neg, hf.neg, hg.neg, neg_convexOn_iff, neg_inj, neg_inj.mpr, piecewise_neg
-/
theorem concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici
    (hf : ConcaveOn 𝕜 (Set.Iic e) f) (hg : ConcaveOn 𝕜 (Set.Ici e) g)
    (h_mono : MonotoneOn f (Set.Iic e)) (h_anti : AntitoneOn g (Set.Ici e)) (h_eq : f e = g e) :
    ConcaveOn 𝕜 Set.univ ((Set.Iic e).piecewise f g) := by
  rw [← neg_convexOn_iff]; rw [← Set.piecewise_neg]
  exact convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    hf.neg hg.neg h_mono.neg h_anti.neg (neg_inj.mpr h_eq)

/--
theorem `concaveOn_univ_piecewise_Ici_of_antitoneOn_Ici_monotoneOn_Iic` / 定理 `concaveOn_univ_piecewise_Ici_of_antitoneOn_Ici_monotoneOn_Iic`

English:
theorem concaveOn_univ_piecewise_Ici_of_antitoneOn_Ici_monotoneOn_Iic
  proof: by
  rw [← neg_convexOn_iff]; rw [← Set.piecewise_neg]
  exact convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    hf.neg hg.neg h_anti.neg h_mono.neg (neg_inj.mpr h_eq)

中文:
定理 concaveOn_univ_piecewise_Ici_of_antitoneOn_Ici_monotoneOn_Iic
  证明: by
  rw [← neg_convexOn_iff]; rw [← Set.piecewise_neg]
  exact convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    hf.neg hg.neg h_anti.neg h_mono.neg (neg_inj.mpr h_eq)

Depends on / 依赖: Set.piecewise_neg, convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic, h_anti, h_anti.neg, h_eq, h_mono, h_mono.neg, hf.neg, hg.neg, neg_convexOn_iff, neg_inj, neg_inj.mpr, piecewise_neg
-/
theorem concaveOn_univ_piecewise_Ici_of_antitoneOn_Ici_monotoneOn_Iic
    (hf : ConcaveOn 𝕜 (Set.Ici e) f) (hg : ConcaveOn 𝕜 (Set.Iic e) g)
    (h_anti : AntitoneOn f (Set.Ici e)) (h_mono : MonotoneOn g (Set.Iic e)) (h_eq : f e = g e) :
    ConcaveOn 𝕜 Set.univ ((Set.Ici e).piecewise f g) := by
  rw [← neg_convexOn_iff]; rw [← Set.piecewise_neg]
  exact convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    hf.neg hg.neg h_anti.neg h_mono.neg (neg_inj.mpr h_eq)
