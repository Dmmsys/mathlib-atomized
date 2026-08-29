/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Theorems about convexity on the complex plane

We show that the open and closed half-spaces in ℂ given by an inequality on either the real or
imaginary part are all convex over ℝ. We also prove some results on star-convexity for the
slit plane.
-/

public section

open Set
open scoped ComplexOrder

namespace Complex

/--
lemma `convexHull_reProdIm` / 引理 `convexHull_reProdIm`

English:
lemma convexHull_reProdIm
  given: (s t : Set Real)
  proof: calc
    convexHull Real (equivRealProdLm ⁻¹' (s ×ˢ t)) = equivRealProdLm ⁻¹' convexHull Real (s ×ˢ t) := by
      simpa only [← LinearEquiv.image_symm_eq_preimage]
        using! ((equivRealProdLm.symm.toLinearMap).image_convexHull (s ×ˢ t)).symm
    _ = convexHull Real s ×Complex convexHull Real t := by rw [convexHull_prod]; rfl

中文:
引理 convexHull_reProdIm
  条件: (s t : 集合 实数)
  证明: calc
    convexHull Real (equivRealProdLm ⁻¹' (s ×ˢ t)) = equivRealProdLm ⁻¹' convexHull Real (s ×ˢ t) := by
      simpa only [← LinearEquiv.image_symm_eq_preimage]
        using! ((equivRealProdLm.symm.toLinearMap).image_convexHull (s ×ˢ t)).symm
    _ = convexHull Real s ×Complex convexHull Real t := by rw [convexHull_prod]; rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.image_symm_eq_preimage, convexHull, convexHull_prod, equivRealProdLm, equivRealProdLm.symm.toLinearMap, image_convexHull, image_symm_eq_preimage, toLinearMap
-/
lemma convexHull_reProdIm (s t : Set Real) :
    convexHull Real (s ×Complex t) = convexHull Real s ×Complex convexHull Real t :=
  calc
    convexHull Real (equivRealProdLm ⁻¹' (s ×ˢ t)) = equivRealProdLm ⁻¹' convexHull Real (s ×ˢ t) := by
      simpa only [← LinearEquiv.image_symm_eq_preimage]
        using! ((equivRealProdLm.symm.toLinearMap).image_convexHull (s ×ˢ t)).symm
    _ = convexHull Real s ×Complex convexHull Real t := by rw [convexHull_prod]; rfl

/--
lemma `starConvex_slitPlane` / 引理 `starConvex_slitPlane`

English:
lemma starConvex_slitPlane
  given: {z : Complex} (hz : 0 < z)
  statement: StarConvex Real z slitPlane
  proof: Complex.compl_Iic_zero ▸ starConvex_compl_Iic hz

中文:
引理 starConvex_slitPlane
  条件: {z : 复形} (hz : 0 < z)
  结论: StarConvex 实数 z slitPlane
  证明: Complex.compl_Iic_zero ▸ starConvex_compl_Iic hz

Depends on / 依赖: Complex.compl_Iic_zero, compl_Iic_zero, starConvex_compl_Iic
-/
lemma starConvex_slitPlane {z : Complex} (hz : 0 < z) : StarConvex Real z slitPlane :=
  Complex.compl_Iic_zero ▸ starConvex_compl_Iic hz

/--
lemma `starConvex_ofReal_slitPlane` / 引理 `starConvex_ofReal_slitPlane`

English:
lemma starConvex_ofReal_slitPlane
  given: {x : Real} (hx : 0 < x)
  statement: StarConvex Real ↑x slitPlane
  proof: starConvex_slitPlane zero_lt_real.2 hx

中文:
引理 starConvex_of实数_slitPlane
  条件: {x : 实数} (hx : 0 < x)
  结论: StarConvex 实数 ↑x slitPlane
  证明: starConvex_slitPlane zero_lt_real.2 hx

Depends on / 依赖: starConvex_slitPlane, zero_lt_real
-/
lemma starConvex_ofReal_slitPlane {x : Real} (hx : 0 < x) : StarConvex Real ↑x slitPlane :=
starConvex_slitPlane zero_lt_real.2 hx

/--
lemma `starConvex_one_slitPlane` / 引理 `starConvex_one_slitPlane`

English:
lemma starConvex_one_slitPlane
  statement: StarConvex Real 1 slitPlane
  proof: starConvex_slitPlane one_pos

中文:
引理 starConvex_one_slitPlane
  结论: StarConvex 实数 1 slitPlane
  证明: starConvex_slitPlane one_pos

Depends on / 依赖: one_pos, starConvex_slitPlane
-/
lemma starConvex_one_slitPlane : StarConvex Real 1 slitPlane := starConvex_slitPlane one_pos

end Complex

open Complex

variable (r : Real)

/--
theorem `convex_halfSpace_re_lt` / 定理 `convex_halfSpace_re_lt`

English:
theorem convex_halfSpace_re_lt
  statement: Convex Real { c : Complex | c.re < r }
  proof: convex_halfSpace_lt (.mk add_re smul_re) _

中文:
定理 convex_halfSpace_re_lt
  结论: 凸 实数 { c : 复形 | c.re < r }
  证明: convex_halfSpace_lt (.mk add_re smul_re) _

Depends on / 依赖: add_re, convex_halfSpace_lt, smul_re
-/
theorem convex_halfSpace_re_lt : Convex Real { c : Complex | c.re < r } :=
  convex_halfSpace_lt (.mk add_re smul_re) _
/--
theorem `convex_halfSpace_re_le` / 定理 `convex_halfSpace_re_le`

English:
theorem convex_halfSpace_re_le
  statement: Convex Real { c : Complex | c.re <= r }
  proof: convex_halfSpace_le (.mk add_re smul_re) _

中文:
定理 convex_halfSpace_re_le
  结论: 凸 实数 { c : 复形 | c.re <= r }
  证明: convex_halfSpace_le (.mk add_re smul_re) _

Depends on / 依赖: add_re, convex_halfSpace_le, smul_re
-/
theorem convex_halfSpace_re_le : Convex Real { c : Complex | c.re <= r } :=
  convex_halfSpace_le (.mk add_re smul_re) _
/--
theorem `convex_halfSpace_re_gt` / 定理 `convex_halfSpace_re_gt`

English:
theorem convex_halfSpace_re_gt
  statement: Convex Real { c : Complex | r < c.re }
  proof: convex_halfSpace_gt (.mk add_re smul_re) _

中文:
定理 convex_halfSpace_re_gt
  结论: 凸 实数 { c : 复形 | r < c.re }
  证明: convex_halfSpace_gt (.mk add_re smul_re) _

Depends on / 依赖: add_re, convex_halfSpace_gt, smul_re
-/
theorem convex_halfSpace_re_gt : Convex Real { c : Complex | r < c.re } :=
  convex_halfSpace_gt (.mk add_re smul_re) _
/--
theorem `convex_halfSpace_re_ge` / 定理 `convex_halfSpace_re_ge`

English:
theorem convex_halfSpace_re_ge
  statement: Convex Real { c : Complex | r <= c.re }
  proof: convex_halfSpace_ge (.mk add_re smul_re) _

中文:
定理 convex_halfSpace_re_ge
  结论: 凸 实数 { c : 复形 | r <= c.re }
  证明: convex_halfSpace_ge (.mk add_re smul_re) _

Depends on / 依赖: add_re, convex_halfSpace_ge, smul_re
-/
theorem convex_halfSpace_re_ge : Convex Real { c : Complex | r <= c.re } :=
  convex_halfSpace_ge (.mk add_re smul_re) _
/--
theorem `convex_halfSpace_im_lt` / 定理 `convex_halfSpace_im_lt`

English:
theorem convex_halfSpace_im_lt
  statement: Convex Real { c : Complex | c.im < r }
  proof: convex_halfSpace_lt (.mk add_im smul_im) _

中文:
定理 convex_halfSpace_im_lt
  结论: 凸 实数 { c : 复形 | c.im < r }
  证明: convex_halfSpace_lt (.mk add_im smul_im) _

Depends on / 依赖: add_im, convex_halfSpace_lt, smul_im
-/
theorem convex_halfSpace_im_lt : Convex Real { c : Complex | c.im < r } :=
  convex_halfSpace_lt (.mk add_im smul_im) _
/--
theorem `convex_halfSpace_im_le` / 定理 `convex_halfSpace_im_le`

English:
theorem convex_halfSpace_im_le
  statement: Convex Real { c : Complex | c.im <= r }
  proof: convex_halfSpace_le (.mk add_im smul_im) _

中文:
定理 convex_halfSpace_im_le
  结论: 凸 实数 { c : 复形 | c.im <= r }
  证明: convex_halfSpace_le (.mk add_im smul_im) _

Depends on / 依赖: add_im, convex_halfSpace_le, smul_im
-/
theorem convex_halfSpace_im_le : Convex Real { c : Complex | c.im <= r } :=
  convex_halfSpace_le (.mk add_im smul_im) _
/--
theorem `convex_halfSpace_im_gt` / 定理 `convex_halfSpace_im_gt`

English:
theorem convex_halfSpace_im_gt
  statement: Convex Real { c : Complex | r < c.im }
  proof: convex_halfSpace_gt (.mk add_im smul_im) _

中文:
定理 convex_halfSpace_im_gt
  结论: 凸 实数 { c : 复形 | r < c.im }
  证明: convex_halfSpace_gt (.mk add_im smul_im) _

Depends on / 依赖: add_im, convex_halfSpace_gt, smul_im
-/
theorem convex_halfSpace_im_gt : Convex Real { c : Complex | r < c.im } :=
  convex_halfSpace_gt (.mk add_im smul_im) _
/--
theorem `convex_halfSpace_im_ge` / 定理 `convex_halfSpace_im_ge`

English:
theorem convex_halfSpace_im_ge
  statement: Convex Real { c : Complex | r <= c.im }
  proof: convex_halfSpace_ge (.mk add_im smul_im) _

中文:
定理 convex_halfSpace_im_ge
  结论: 凸 实数 { c : 复形 | r <= c.im }
  证明: convex_halfSpace_ge (.mk add_im smul_im) _

Depends on / 依赖: add_im, convex_halfSpace_ge, smul_im
-/
theorem convex_halfSpace_im_ge : Convex Real { c : Complex | r <= c.im } :=
  convex_halfSpace_ge (.mk add_im smul_im) _

namespace Complex

/--
lemma `isConnected_of_upperHalfPlane` / 引理 `isConnected_of_upperHalfPlane`

English:
lemma isConnected_of_upperHalfPlane
  statement: {r} {s : Set Complex} (hs₁ : {z | r < z.im} subseteq s)
  proof: by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOfPred_lt_im] using hs₂)
  exact (convex_halfSpace_im_gt r).isConnected ⟨(r + 1) * I, by simp⟩

中文:
引理 isConnected_of_upperHalfPlane
  结论: {r} {s : 集合 复形} (hs₁ : {z | r < z.im} subseteq s)
  证明: by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOfPred_lt_im] using hs₂)
  exact (convex_halfSpace_im_gt r).isConnected ⟨(r + 1) * I, by simp⟩

Depends on / 依赖: closure_setOfPred_lt_im, convex_halfSpace_im_gt, isConnected, subset_closure
-/
lemma isConnected_of_upperHalfPlane {r} {s : Set Complex} (hs₁ : {z | r < z.im} subseteq s)
    (hs₂ : s subseteq {z | r <= z.im}) : IsConnected s := by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOfPred_lt_im] using hs₂)
  exact (convex_halfSpace_im_gt r).isConnected ⟨(r + 1) * I, by simp⟩

/--
lemma `isConnected_of_lowerHalfPlane` / 引理 `isConnected_of_lowerHalfPlane`

English:
lemma isConnected_of_lowerHalfPlane
  statement: {r} {s : Set Complex} (hs₁ : {z | z.im < r} subseteq s)
  proof: by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOfPred_im_lt] using hs₂)
  exact (convex_halfSpace_im_lt r).isConnected ⟨(r - 1) * I, by simp⟩

中文:
引理 isConnected_of_lowerHalfPlane
  结论: {r} {s : 集合 复形} (hs₁ : {z | z.im < r} subseteq s)
  证明: by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOfPred_im_lt] using hs₂)
  exact (convex_halfSpace_im_lt r).isConnected ⟨(r - 1) * I, by simp⟩

Depends on / 依赖: closure_setOfPred_im_lt, convex_halfSpace_im_lt, isConnected, subset_closure
-/
lemma isConnected_of_lowerHalfPlane {r} {s : Set Complex} (hs₁ : {z | z.im < r} subseteq s)
    (hs₂ : s subseteq {z | z.im <= r}) : IsConnected s := by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOfPred_im_lt] using hs₂)
  exact (convex_halfSpace_im_lt r).isConnected ⟨(r - 1) * I, by simp⟩

/--
lemma `rectangle_eq_convexHull` / 引理 `rectangle_eq_convexHull`

English:
lemma rectangle_eq_convexHull
  given: (z w : Complex)
  proof: by
  simp_rw [Rectangle, ← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm,
    ← preimage_equivRealProd_prod, insert_prod, singleton_prod, image_pair, insert_union,
    ← insert_eq, ← Equiv.image_symm_eq_preimage, image_insert_eq, image_singleton,
    equivRealProd_symm_apply, re_add_im]

中文:
引理 rectangle_eq_convexHull
  条件: (z w : 复形)
  证明: by
  simp_rw [Rectangle, ← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm,
    ← preimage_equivRealProd_prod, insert_prod, singleton_prod, image_pair, insert_union,
    ← insert_eq, ← Equiv.image_symm_eq_preimage, image_insert_eq, image_singleton,
    equivRealProd_symm_apply, re_add_im]

Depends on / 依赖: Equiv.image_symm_eq_preimage, Rectangle, convexHull_pair, convexHull_reProdIm, equivRealProd_symm_apply, image_insert_eq, image_pair, image_singleton, image_symm_eq_preimage, insert_eq, insert_prod, insert_union, preimage_equivRealProd_prod, re_add_im, segment_eq_uIcc, simp_rw, singleton_prod
-/
lemma rectangle_eq_convexHull (z w : Complex) :
    Rectangle z w = convexHull Real {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [Rectangle, ← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm,
    ← preimage_equivRealProd_prod, insert_prod, singleton_prod, image_pair, insert_union,
    ← insert_eq, ← Equiv.image_symm_eq_preimage, image_insert_eq, image_singleton,
    equivRealProd_symm_apply, re_add_im]

/--
lemma `Convex.rectangle_subset` / 引理 `Convex.rectangle_subset`

English:
lemma Convex.rectangle_subset
  statement: {U : Set Complex} (U_convex : Convex Real U) {z w : Complex} (hz : z in U)
  proof: by
  simpa only [rectangle_eq_convexHull] using convexHull_min (by grind) U_convex

中文:
引理 凸.rectangle_subset
  结论: {U : 集合 复形} (U_convex : 凸 实数 U) {z w : 复形} (hz : z in U)
  证明: by
  simpa only [rectangle_eq_convexHull] using convexHull_min (by grind) U_convex

Depends on / 依赖: U_convex, convexHull_min, rectangle_eq_convexHull
-/
lemma Convex.rectangle_subset {U : Set Complex} (U_convex : Convex Real U) {z w : Complex} (hz : z in U)
    (hw : w in U) (hzw : (z.re + w.im * I) in U) (hwz : (w.re + z.im * I) in U) :
    Rectangle z w subseteq U := by
  simpa only [rectangle_eq_convexHull] using convexHull_min (by grind) U_convex

-- This also follows easily from `isPathConnected_compl_singleton_of_one_lt_rank`,
-- or that `Complex.range_exp` and `Complex.continuous_exp`,
-- but both of them requires a lot more import.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PathConnectedSpace Complexˣ
  body: have : PathConnectedSpace { z : Complex // z != 0 } :=
    (isPathConnected_iff_pathConnectedSpace (F := {0}ᶜ)).mp (by
      convert!
        (((convex_halfSpace_im_gt 0).isPathConnected ⟨.I, by simp⟩).union
              ((convex_halfSpace_re_gt 0).isPathConnected ⟨1, by simp⟩) ⟨1 + .I, by simp⟩).union
          (((convex_halfSpace_im_lt 0).isPathConnected ⟨-.I, by simp⟩).union
            ((convex_halfSpace_re_lt 0).isPathConnected ⟨-1, by simp⟩) ⟨-1 - .I, by simp⟩)
          ⟨1 - .I, by simp⟩ using 1
      ext x
      refine ⟨?_, by aesop⟩
      simp +contextual [Complex.ext_iff, -not_and, not_and_or, or_imp, ← ne_eq, ← lt_or_lt_iff_ne])
  let e := unitsHomeomorphNeZero (G₀ := Complex)
  e.symm.surjective.pathConnectedSpace e.symm.continuous

中文:
实例 :
  签名: 道路连通空间 Complexˣ
  定义体: have : PathConnectedSpace { z : Complex // z != 0 } :=
    (isPathConnected_iff_pathConnectedSpace (F := {0}ᶜ)).mp (by
      convert!
        (((convex_halfSpace_im_gt 0).isPathConnected ⟨.I, by simp⟩).union
              ((convex_halfSpace_re_gt 0).isPathConnected ⟨1, by simp⟩) ⟨1 + .I, by simp⟩).union
          (((convex_halfSpace_im_lt 0).isPathConnected ⟨-.I, by simp⟩).union
            ((convex_halfSpace_re_lt 0).isPathConnected ⟨-1, by simp⟩) ⟨-1 - .I, by simp⟩)
          ⟨1 - .I, by simp⟩ using 1
      ext x
      refine ⟨?_, by aesop⟩
      simp +contextual [Complex.ext_iff, -not_and, not_and_or, or_imp, ← ne_eq, ← lt_or_lt_iff_ne])
  let e := unitsHomeomorphNeZero (G₀ := Complex)
  e.symm.surjective.pathConnectedSpace e.symm.continuous

Depends on / 依赖: Complex.e, PathConnectedSpace, contextual, convert, convex_halfSpace_im_gt, convex_halfSpace_im_lt, convex_halfSpace_re_gt, convex_halfSpace_re_lt, isPathConnected, isPathConnected_iff_pathConnectedSpace
-/
instance : PathConnectedSpace Complexˣ :=
  have : PathConnectedSpace { z : Complex // z != 0 } :=
    (isPathConnected_iff_pathConnectedSpace (F := {0}ᶜ)).mp (by
      convert!
        (((convex_halfSpace_im_gt 0).isPathConnected ⟨.I, by simp⟩).union
              ((convex_halfSpace_re_gt 0).isPathConnected ⟨1, by simp⟩) ⟨1 + .I, by simp⟩).union
          (((convex_halfSpace_im_lt 0).isPathConnected ⟨-.I, by simp⟩).union
            ((convex_halfSpace_re_lt 0).isPathConnected ⟨-1, by simp⟩) ⟨-1 - .I, by simp⟩)
          ⟨1 - .I, by simp⟩ using 1
      ext x
      refine ⟨?_, by aesop⟩
      simp +contextual [Complex.ext_iff, -not_and, not_and_or, or_imp, ← ne_eq, ← lt_or_lt_iff_ne])
  let e := unitsHomeomorphNeZero (G₀ := Complex)
  e.symm.surjective.pathConnectedSpace e.symm.continuous

end Complex
