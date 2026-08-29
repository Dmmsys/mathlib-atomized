/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Semicontinuity.Lindelof

/-!
# Approximation to convex functions

In this file we show that a convex lower-semicontinuous function is the upper envelope of a family
of continuous affine linear functions. We follow the proof in
[N. Bourbaki, *Topological vector spaces*, Chapter II, §5][bourbaki1987].

## Main Statement

* `sSup_affine_eq` : A function `φ : E → ℝ` that is convex and lower-semicontinuous on a closed
  convex subset `s` is the supremum of a family of functions that are the restrictions to `s` of
  continuous affine linear functions.
* `sSup_of_countable_affine_eq` : Suppose `E` is a `HereditarilyLindelofSpace`. A function
  `φ : E → ℝ` that is convex and lower-semicontinuous on a closed convex subset `s` is the supremum
  of a family of countably many functions that are the restrictions to `s` of continuous affine
  linear functions.

-/

public section

open Function Set RCLike ContinuousLinearMap

namespace ConvexOn

variable {𝕜 E F : Type*} {s : Set E} {φ : E -> Real} [RCLike 𝕜]

/--
theorem `convex_re_epigraph` / 定理 `convex_re_epigraph`

English:
theorem convex_re_epigraph
  given: [AddCommMonoid E] [Module Real E] (hφcv : ConvexOn Real s φ)
  proof: by
  have lem : { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 } =
    ((LinearMap.id : E ->ₗ[Real] E).prodMap reLm) ⁻¹' { p : E × Real | p.1 in s ∧ φ p.1 <= p.2 } := by simp
  exact lem ▸ hφcv.convex_epigraph.linear_preimage _

中文:
定理 convex_re_epigraph
  条件: [AddCommMonoid E] [Module 实数 E] (hφcv : ConvexOn 实数 s φ)
  证明: by
  have lem : { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 } =
    ((LinearMap.id : E ->ₗ[Real] E).prodMap reLm) ⁻¹' { p : E × Real | p.1 in s ∧ φ p.1 <= p.2 } := by simp
  exact lem ▸ hφcv.convex_epigraph.linear_preimage _

Depends on / 依赖: LinearMap, LinearMap.id, convex_epigraph, cv.convex_epigraph.linear_preimage, linear_preimage, prodMap
-/
theorem convex_re_epigraph [AddCommMonoid E] [Module Real E] (hφcv : ConvexOn Real s φ) :
    Convex Real { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 } := by
  have lem : { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 } =
    ((LinearMap.id : E ->ₗ[Real] E).prodMap reLm) ⁻¹' { p : E × Real | p.1 in s ∧ φ p.1 <= p.2 } := by simp
  exact lem ▸ hφcv.convex_epigraph.linear_preimage _

variable [TopologicalSpace E]

/--
theorem `_root_.LowerSemicontinuousOn.isClosed_re_epigraph` / 定理 `_root_.LowerSemicontinuousOn.isClosed_re_epigraph`

English:
theorem _root_.LowerSemicontinuousOn.isClosed_re_epigraph
  statement: (hsc : IsClosed s)
  proof: by
  let A := { p : E × EReal | p.1 in s ∧ φ p.1 <= p.2 }
  have hC : { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 }
    = (Prod.map id ((Real.toEReal ∘ re) : 𝕜 -> EReal)) ⁻¹' A := by simp [A]
  refine hC.symm ▸ IsClosed.preimage ?_ ?_
· exact continuous_id.prodMap continuous_coe_real_ereal.comp reCLM.c

中文:
定理 _root_.LowerSemicontinuousOn.isClosed_re_epigraph
  结论: (hsc : IsClosed s)
  证明: by
  let A := { p : E × EReal | p.1 in s ∧ φ p.1 <= p.2 }
  have hC : { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 }
    = (Prod.map id ((Real.toEReal ∘ re) : 𝕜 -> EReal)) ⁻¹' A := by simp [A]
  refine hC.symm ▸ IsClosed.preimage ?_ ?_
· exact continuous_id.prodMap continuous_coe_real_ereal.comp reCLM.c

Depends on / 依赖: EReal.coe_strictMono.monotone, IsClosed, IsClosed.preimage, Prod.map, Real.toEReal, coe_strictMono, comp_lowerSemicontinuousOn, continuous_coe_real_ereal, continuous_coe_real_ereal.comp, continuous_coe_real_ereal.comp_lowerSemicontinuousOn, continuous_id, continuous_id.prodMap, hC.symm, lowerSemicontinuousOn_iff_isClosed_epigraph, monotone, preimage, prodMap, reCLM.cont, toEReal
-/
theorem _root_.LowerSemicontinuousOn.isClosed_re_epigraph (hsc : IsClosed s)
    (hφ_cont : LowerSemicontinuousOn φ s) :
    IsClosed { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 } := by
  let A := { p : E × EReal | p.1 in s ∧ φ p.1 <= p.2 }
  have hC : { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 }
    = (Prod.map id ((Real.toEReal ∘ re) : 𝕜 -> EReal)) ⁻¹' A := by simp [A]
  refine hC.symm ▸ IsClosed.preimage ?_ ?_
· exact continuous_id.prodMap continuous_coe_real_ereal.comp reCLM.cont
  · exact (lowerSemicontinuousOn_iff_isClosed_epigraph hsc).1
      (continuous_coe_real_ereal.comp_lowerSemicontinuousOn hφ_cont (EReal.coe_strictMono.monotone))

section RCLike

variable [AddCommGroup E] [Module Real E] [Module 𝕜 E] [IsScalarTower Real 𝕜 E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace Real E]

/--
lemma `exists_affine_le_of_lt` / 引理 `exists_affine_le_of_lt`

English:
lemma exists_affine_le_of_lt
  statement: {x : E} {a : Real} (hx : x in s) (hax : a < φ x) (hsc : IsClosed s)
  proof: by
  let A := { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 }
  obtain ⟨L, ⟨b, hLb⟩⟩ := geometric_hahn_banach_point_closed (𝕜 := 𝕜) hφcv.convex_re_epigraph
    (hφc.isClosed_re_epigraph hsc) (by simp [A, hax] : (x, ofReal a) ∉ A)
  let u := L.comp (.inl 𝕜 E 𝕜)
  let c := (re (L (0, 1)))⁻¹
  refine ⟨- c •

中文:
引理 exists_affine_le_of_lt
  结论: {x : E} {a : 实数} (hx : x in s) (hax : a < φ x) (hsc : IsClosed s)
  证明: by
  let A := { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 }
  obtain ⟨L, ⟨b, hLb⟩⟩ := geometric_hahn_banach_point_closed (𝕜 := 𝕜) hφcv.convex_re_epigraph
    (hφc.isClosed_re_epigraph hsc) (by simp [A, hax] : (x, ofReal a) ∉ A)
  let u := L.comp (.inl 𝕜 E 𝕜)
  let c := (re (L (0, 1)))⁻¹
  refine ⟨- c •

Depends on / 依赖: L.comp, c.isClosed_re_epigraph, convex_re_epigraph, cv.convex_re_epigraph, geometric_hahn_banach_point_closed, isClosed_re_epigraph, map_smul, ofReal, smul_eq_mul
-/
lemma exists_affine_le_of_lt {x : E} {a : Real} (hx : x in s) (hax : a < φ x) (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) :
    exists (l : E ->L[𝕜] 𝕜) (c : Real),
      s.domRestrict (re ∘ l) + const s c <= s.domRestrict φ ∧ re (l x) + c = a := by
  let A := { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 }
  obtain ⟨L, ⟨b, hLb⟩⟩ := geometric_hahn_banach_point_closed (𝕜 := 𝕜) hφcv.convex_re_epigraph
    (hφc.isClosed_re_epigraph hsc) (by simp [A, hax] : (x, ofReal a) ∉ A)
  let u := L.comp (.inl 𝕜 E 𝕜)
  let c := (re (L (0, 1)))⁻¹
  refine ⟨- c • u, c * re (u x) + a, fun z => ?_, ?_⟩
  · have hv (v : 𝕜) : v * L (0, 1) = L (0, v) := by rw [← smul_eq_mul, ← map_smul]; simp
    have hine {w : E} (h : w in s) : re (L (x, 0)) + re (L (0, 1)) * a
      < re (L (w, 0)) + re (L (0, 1)) * φ w := by
      have hw := hLb.1.trans (hLb.2 _ (by simp [A, h] : (w, ofReal (φ w)) in A))
      rw [← coprod_comp_inl_inr L] at hw
      simpa [-coprod_comp_inl_inr, ← hv (ofReal a), ← hv (ofReal (φ w)), mul_comm a,
        mul_comm (φ w)] using hw
    have hc : 0 < c := inv_pos.2 (pos_of_right_mul_lt_le (lt_of_add_lt_add_left (hine hx)) hax.le)
    simpa [smul_re, u, c, mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (inv_pos.1 hc))]
      using mul_le_mul_of_nonneg_left (hine z.2).le hc.le
  · simp [u, c, smul_re]

/--
lemma `exists_affine_le_of_lt_real` / 引理 `exists_affine_le_of_lt_real`

English:
lemma exists_affine_le_of_lt_real
  statement: {s : Set Real} {f : Real -> Real} {x : Real} {a : Real} (hx : x in s)
  proof: by
  obtain ⟨l, c', hlc'_le, hlc'_eq⟩ := exists_affine_le_of_lt (𝕜 := Real) hx hax hsc hfc hf
  have h1 y : l 1 * y = l y := by rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  exact ⟨l 1, c', fun y hy => by simpa [h1] using hlc'_le ⟨y, hy⟩, by simpa [h1] using hlc'_eq⟩

中文:
引理 exists_affine_le_of_lt_real
  结论: {s : Set 实数} {f : 实数 -> 实数} {x : 实数} {a : 实数} (hx : x in s)
  证明: by
  obtain ⟨l, c', hlc'_le, hlc'_eq⟩ := exists_affine_le_of_lt (𝕜 := Real) hx hax hsc hfc hf
  have h1 y : l 1 * y = l y := by rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  exact ⟨l 1, c', fun y hy => by simpa [h1] using hlc'_le ⟨y, hy⟩, by simpa [h1] using hlc'_eq⟩

Depends on / 依赖: exists_affine_le_of_lt, map_smul, mul_comm, mul_one, smul_eq_mul
-/
lemma exists_affine_le_of_lt_real {s : Set Real} {f : Real -> Real} {x : Real} {a : Real} (hx : x in s)
    (hax : a < f x) (hsc : IsClosed s) (hfc : LowerSemicontinuousOn f s) (hf : ConvexOn Real s f) :
    exists (c c' : Real), (forall y in s, c * y + c' <= f y) ∧ c * x + c' = a := by
  obtain ⟨l, c', hlc'_le, hlc'_eq⟩ := exists_affine_le_of_lt (𝕜 := Real) hx hax hsc hfc hf
  have h1 y : l 1 * y = l y := by rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  exact ⟨l 1, c', fun y hy => by simpa [h1] using hlc'_le ⟨y, hy⟩, by simpa [h1] using hlc'_eq⟩

/--
lemma `exists_affine_le_real` / 引理 `exists_affine_le_real`

English:
lemma exists_affine_le_real
  statement: {s : Set Real} {f : Real -> Real}
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hxs⟩
  · simp
  obtain ⟨c, c', hlc'_le, -⟩ :=
    hf.exists_affine_le_of_lt_real (a := f x - 1) hxs (by simp) hsc hfc
  exact ⟨c, c', hlc'_le⟩

中文:
引理 exists_affine_le_real
  结论: {s : Set 实数} {f : 实数 -> 实数}
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hxs⟩
  · simp
  obtain ⟨c, c', hlc'_le, -⟩ :=
    hf.exists_affine_le_of_lt_real (a := f x - 1) hxs (by simp) hsc hfc
  exact ⟨c, c', hlc'_le⟩

Depends on / 依赖: eq_empty_or_nonempty, exists_affine_le_of_lt_real, hf.exists_affine_le_of_lt_real, s.eq_empty_or_nonempty
-/
lemma exists_affine_le_real {s : Set Real} {f : Real -> Real}
    (hsc : IsClosed s) (hfc : LowerSemicontinuousOn f s) (hf : ConvexOn Real s f) :
    exists c c', forall x in s, c * x + c' <= f x := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hxs⟩
  · simp
  obtain ⟨c, c', hlc'_le, -⟩ :=
    hf.exists_affine_le_of_lt_real (a := f x - 1) hxs (by simp) hsc hfc
  exact ⟨c, c', hlc'_le⟩

/--
theorem `sSup_affine_eq` / 定理 `sSup_affine_eq`

English:
theorem sSup_affine_eq
  statement: (hsc : IsClosed s)
  proof: by
  let A := { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 }
  ext x
  rw [sSup_apply]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ (fun r ⟨f, hf⟩ => ?_) (fun r hr => ?_)
  · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) x.2 (show φ x - 1 < φ x by grind)
      hsc hφc hφcv
    exact 

中文:
定理 sSup_affine_eq
  结论: (hsc : IsClosed s)
  证明: by
  let A := { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 }
  ext x
  rw [sSup_apply]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ (fun r ⟨f, hf⟩ => ?_) (fun r hr => ?_)
  · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) x.2 (show φ x - 1 < φ x by grind)
      hsc hφc hφcv
    exact 

Depends on / 依赖: csSup_eq_of_forall_le_of_forall_lt_exists_gt, domRestrict, exists_affine_le_of_lt, exists_between, s.domRestrict, sSup_apply
-/
theorem sSup_affine_eq (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) :
    sSup {f | f <= s.domRestrict φ ∧
      exists (l : E ->L[𝕜] 𝕜) (c : Real), f = s.domRestrict (re ∘ l) + const s c} = s.domRestrict φ := by
  let A := { p : E × 𝕜 | p.1 in s ∧ φ p.1 <= re p.2 }
  ext x
  rw [sSup_apply]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ (fun r ⟨f, hf⟩ => ?_) (fun r hr => ?_)
  · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) x.2 (show φ x - 1 < φ x by grind)
      hsc hφc hφcv
    exact ⟨φ x - 1, hlc.2 ▸ ⟨⟨s.domRestrict (re ∘ l) + const s c, hlc.1, l, c, rfl⟩, rfl⟩⟩
  · exact hf ▸ f.2.1 x
  · obtain ⟨z, hz⟩ := exists_between hr
    obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) x.2 hz.2 hsc hφc hφcv
    exact ⟨z, hlc.2 ▸ ⟨⟨s.domRestrict (re ∘ l) + const s c, hlc.1, l, c, rfl⟩, rfl⟩, hz.1⟩

/--
theorem `sSup_of_countable_affine_eq` / 定理 `sSup_of_countable_affine_eq`

English:
theorem sSup_of_countable_affine_eq
  statement: [HereditarilyLindelofSpace E] (hsc : IsClosed s)
  proof: by
  by_cases! hs : s.Nonempty
  · let 𝓕 := {f | f <= s.domRestrict φ ∧
      exists (l : E ->L[𝕜] 𝕜) (c : Real), f = s.domRestrict (re ∘ l) + const s c}
    have hl : IsLUB 𝓕 (s.domRestrict φ) := by
      refine (hφcv.sSup_affine_eq (𝕜 := 𝕜) hsc hφc) ▸ isLUB_csSup ?_ ?_
      · obtain ⟨l, c, hlc⟩ :

中文:
定理 sSup_of_countable_affine_eq
  结论: [HereditarilyLindelofSpace E] (hsc : IsClosed s)
  证明: by
  by_cases! hs : s.Nonempty
  · let 𝓕 := {f | f <= s.domRestrict φ ∧
      exists (l : E ->L[𝕜] 𝕜) (c : Real), f = s.domRestrict (re ∘ l) + const s c}
    have hl : IsLUB 𝓕 (s.domRestrict φ) := by
      refine (hφcv.sSup_affine_eq (𝕜 := 𝕜) hsc hφc) ▸ isLUB_csSup ?_ ?_
      · obtain ⟨l, c, hlc⟩ :

Depends on / 依赖: Nonempty, Subtype, Subtype.val, bddAbove_def, cv.sSup_affine_eq, domRestrict, exists_affine_le_of_lt, hs.some, hs.some_mem, isLUB_csSup, s.Nonempty, s.domRestrict, sSup_affine_eq, some_mem
-/
theorem sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) :
    exists 𝓕' : Set (s -> Real), 𝓕'.Countable ∧ sSup 𝓕' = s.domRestrict φ ∧
      forall f in 𝓕', f <= s.domRestrict φ ∧
      exists (l : E ->L[𝕜] 𝕜) (c : Real), f = s.domRestrict (re ∘ l) + const s c := by
  by_cases! hs : s.Nonempty
  · let 𝓕 := {f | f <= s.domRestrict φ ∧
      exists (l : E ->L[𝕜] 𝕜) (c : Real), f = s.domRestrict (re ∘ l) + const s c}
    have hl : IsLUB 𝓕 (s.domRestrict φ) := by
      refine (hφcv.sSup_affine_eq (𝕜 := 𝕜) hsc hφc) ▸ isLUB_csSup ?_ ?_
      · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) hs.some_mem
          (by grind : φ hs.some - 1 < φ (⟨hs.some, hs.some_mem⟩ : s)) hsc hφc hφcv
        exact ⟨s.domRestrict (re ∘ l) + const s c, hlc.1, l, c, rfl⟩
      · exact (bddAbove_def.2 ⟨φ ∘ Subtype.val, fun y hy => hy.1⟩)
    have hr (f) (hf : f in 𝓕) : LowerSemicontinuous f := by
      obtain ⟨l, c, hlc⟩ := hf.2
      exact Continuous.lowerSemicontinuous (hlc ▸ by fun_prop)
    obtain ⟨𝓕', h𝓕'⟩ := exists_countable_lowerSemicontinuous_isLUB hr hl
    refine ⟨𝓕', h𝓕'.2.1, h𝓕'.2.2.csSup_eq ?_, fun f hf => h𝓕'.1 hf⟩
    by_contra!
    grind [(isLUB_empty_iff.1 (this ▸ h𝓕'.2.2)) (fun x : s => φ x - 1) ⟨hs.some, hs.some_mem⟩]
  · use ∅; simp [domRestrict_def]; grind

/--
theorem `sSup_of_nat_affine_eq` / 定理 `sSup_of_nat_affine_eq`

English:
theorem sSup_of_nat_affine_eq
  statement: [HereditarilyLindelofSpace E] (hsc : IsClosed s)
  proof: by
  obtain ⟨𝓕', h𝓕'⟩ := hφcv.sSup_of_countable_affine_eq (𝕜 := 𝕜) hsc hφc
  by_cases! he : 𝓕'.Nonempty
  · obtain ⟨f, hf⟩ := h𝓕'.1.exists_eq_range he
    have (i : Nat) : exists (l : E ->L[𝕜] 𝕜) (c : Real),
        f i = s.domRestrict (re ∘ l) + const s c := by simp_all
    choose l c hlc using thi

中文:
定理 sSup_of_nat_affine_eq
  结论: [HereditarilyLindelofSpace E] (hsc : IsClosed s)
  证明: by
  obtain ⟨𝓕', h𝓕'⟩ := hφcv.sSup_of_countable_affine_eq (𝕜 := 𝕜) hsc hφc
  by_cases! he : 𝓕'.Nonempty
  · obtain ⟨f, hf⟩ := h𝓕'.1.exists_eq_range he
    have (i : Nat) : exists (l : E ->L[𝕜] 𝕜) (c : Real),
        f i = s.domRestrict (re ∘ l) + const s c := by simp_all
    choose l c hlc using thi

Depends on / 依赖: Nonempty, cv.sSup_of_countable_affine_eq, domRestrict, exists_eq_range, mem_range_self, s.domRe, s.domRestrict, sSup_of_countable_affine_eq, sSup_range
-/
theorem sSup_of_nat_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) :
    exists (l : Nat -> E ->L[𝕜] 𝕜) (c : Nat -> Real),
      (forall i, s.domRestrict (re ∘ (l i)) + const s (c i) <= s.domRestrict φ) ∧
      ⨆ i, s.domRestrict (re ∘ (l i)) + const s (c i) = s.domRestrict φ := by
  obtain ⟨𝓕', h𝓕'⟩ := hφcv.sSup_of_countable_affine_eq (𝕜 := 𝕜) hsc hφc
  by_cases! he : 𝓕'.Nonempty
  · obtain ⟨f, hf⟩ := h𝓕'.1.exists_eq_range he
    have (i : Nat) : exists (l : E ->L[𝕜] 𝕜) (c : Real),
        f i = s.domRestrict (re ∘ l) + const s c := by simp_all
    choose l c hlc using this
    refine ⟨l, c, fun i => (hlc i) ▸ (h𝓕'.2.2 (f i) (hf ▸ mem_range_self i)).1, ?_⟩
    calc
    _ = ⨆ i, f i := by congr with i x; exact congrFun (hlc i).symm x
    _ = _ := by rw [← sSup_range, ← hf, h𝓕'.2.1]
  · by_cases! hsφ : s.domRestrict φ = 0
    · have := congrFun hsφ
      refine ⟨fun _ => 0, fun _ => 0, ?_, ?_⟩
      · simp_all [domRestrict_def]
      · ext; simp_all
    · obtain ⟨x, hx⟩ := Function.ne_iff.1 hsφ
      have : s = ∅ := by have := congrFun h𝓕'.2.1 x; simp_all
      grind

/--
theorem `univ_sSup_affine_eq` / 定理 `univ_sSup_affine_eq`

English:
theorem univ_sSup_affine_eq
  given: (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Real univ φ)
  proof: by
  let 𝓕 := {f | f <= φ ∘ Subtype.val ∧ exists (l : E ->L[𝕜] 𝕜) (c : Real), f = (re ∘ l) ∘ Subtype.val +
    const univ c}
  have := hφcv.sSup_affine_eq (𝕜 := 𝕜) isClosed_univ (lowerSemicontinuousOn_univ_iff.2 hφc)
  simp only [domRestrict_eq] at this
  calc
  _ = sSup ((fun g => g ∘ (Equiv.Set.un

中文:
定理 univ_sSup_affine_eq
  条件: (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn 实数 univ φ)
  证明: by
  let 𝓕 := {f | f <= φ ∘ Subtype.val ∧ exists (l : E ->L[𝕜] 𝕜) (c : Real), f = (re ∘ l) ∘ Subtype.val +
    const univ c}
  have := hφcv.sSup_affine_eq (𝕜 := 𝕜) isClosed_univ (lowerSemicontinuousOn_univ_iff.2 hφc)
  simp only [domRestrict_eq] at this
  calc
  _ = sSup ((fun g => g ∘ (Equiv.Set.un

Depends on / 依赖: Equiv.Set.univ, Subtype, Subtype.val, cv.sSup_affine_eq, domRestrict_eq, isClosed_univ, lowerSemicontinuousOn_univ_iff, sSup_affine_eq
-/
theorem univ_sSup_affine_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Real univ φ) :
    sSup {f | f <= φ ∧ exists (l : E ->L[𝕜] 𝕜) (c : Real), f = (re ∘ l) + const E c} = φ := by
  let 𝓕 := {f | f <= φ ∘ Subtype.val ∧ exists (l : E ->L[𝕜] 𝕜) (c : Real), f = (re ∘ l) ∘ Subtype.val +
    const univ c}
  have := hφcv.sSup_affine_eq (𝕜 := 𝕜) isClosed_univ (lowerSemicontinuousOn_univ_iff.2 hφc)
  simp only [domRestrict_eq] at this
  calc
  _ = sSup ((fun g => g ∘ (Equiv.Set.univ E).symm) '' 𝓕) := by
    congr
    ext f
    refine ⟨fun ⟨hp, l, c, hlc⟩ => ⟨f ∘ Subtype.val, ⟨fun x => hp (Subtype.val x), ⟨l, c, ?_⟩⟩, ?_⟩,
      fun ⟨a, ⟨⟨h, ⟨l, c, hlc⟩⟩, hb⟩⟩ => ⟨fun x => ?_, ⟨l, c, ?_⟩⟩⟩
    · ext x; simpa using! congrFun hlc x
    · ext; simp
    · simpa using! hb ▸ h ⟨x, trivial⟩
    · subst hlc; simpa using! hb.symm
  _ = sSup 𝓕 ∘ (Equiv.Set.univ E).symm := by ext x; rw [sSup_image', sSup_eq_iSup']; simp
  _ = φ ∘ Subtype.val ∘ (Equiv.Set.univ E).symm :=
    congrArg (fun g => g ∘ (Equiv.Set.univ E).symm) this
  _ = φ := by ext; simp

/--
theorem `univ_sSup_of_countable_affine_eq` / 定理 `univ_sSup_of_countable_affine_eq`

English:
theorem univ_sSup_of_countable_affine_eq
  statement: [HereditarilyLindelofSpace E]
  proof: by
  let 𝓕 := {f | f <= φ ∧ exists (l : E ->L[𝕜] 𝕜) (c : Real), f = (re ∘ l) + const E c}
  have hl : IsLUB 𝓕 φ := by
    refine (hφcv.univ_sSup_affine_eq (𝕜 := 𝕜) hφc) ▸ isLUB_csSup ?_ ?_
    · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) (@mem_univ E 0)
        (by grind : φ 0 - 1 < φ (⟨0

中文:
定理 univ_sSup_of_countable_affine_eq
  结论: [HereditarilyLindelofSpace E]
  证明: by
  let 𝓕 := {f | f <= φ ∧ exists (l : E ->L[𝕜] 𝕜) (c : Real), f = (re ∘ l) + const E c}
  have hl : IsLUB 𝓕 φ := by
    refine (hφcv.univ_sSup_affine_eq (𝕜 := 𝕜) hφc) ▸ isLUB_csSup ?_ ?_
    · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) (@mem_univ E 0)
        (by grind : φ 0 - 1 < φ (⟨0

Depends on / 依赖: bddAbove_def, cv.univ_sSup_affine_eq, exists_affine_le_of_lt, isClosed_univ, isLUB_csSup, lowerSemicontinuousOn_univ_iff, mem_univ, univ_sSup_affine_eq
-/
theorem univ_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Real univ φ) :
    exists 𝓕' : Set (E -> Real), 𝓕'.Countable ∧ sSup 𝓕' = φ ∧
      forall f in 𝓕', f <= φ ∧ exists (l : E ->L[𝕜] 𝕜) (c : Real), f = (re ∘ l) + const E c := by
  let 𝓕 := {f | f <= φ ∧ exists (l : E ->L[𝕜] 𝕜) (c : Real), f = (re ∘ l) + const E c}
  have hl : IsLUB 𝓕 φ := by
    refine (hφcv.univ_sSup_affine_eq (𝕜 := 𝕜) hφc) ▸ isLUB_csSup ?_ ?_
    · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) (@mem_univ E 0)
        (by grind : φ 0 - 1 < φ (⟨0, @mem_univ E 0⟩ : univ)) isClosed_univ
        (lowerSemicontinuousOn_univ_iff.2 hφc) hφcv
      exact ⟨(re ∘ l) + const E c, fun x => hlc.1 ⟨x, mem_univ x⟩, ⟨l, c, rfl⟩⟩
    · exact (bddAbove_def.2 ⟨φ, fun y hy => hy.1⟩)
  have hr (f) (hf : f in 𝓕) : LowerSemicontinuous f := by
    obtain ⟨l, c, hlc⟩ := hf.2
    exact Continuous.lowerSemicontinuous (by rw [hlc]; fun_prop)
  obtain ⟨𝓕', h𝓕'⟩ := exists_countable_lowerSemicontinuous_isLUB hr hl
  refine ⟨𝓕', h𝓕'.2.1, h𝓕'.2.2.csSup_eq ?_, fun f hf => h𝓕'.1 hf⟩
  by_contra!
  grind [(isLUB_empty_iff.1 (this ▸ h𝓕'.2.2)) (fun x => φ x - 1) 0]

/--
theorem `univ_sSup_of_nat_affine_eq` / 定理 `univ_sSup_of_nat_affine_eq`

English:
theorem univ_sSup_of_nat_affine_eq
  statement: [HereditarilyLindelofSpace E]
  proof: by
  obtain ⟨l, c, hle, hsup⟩ := hφcv.sSup_of_nat_affine_eq (𝕜 := 𝕜) (s := univ) isClosed_univ
    (lowerSemicontinuousOn_univ_iff.2 hφc)
  refine ⟨l, c, fun i x => hle i ⟨x, trivial⟩, ?_⟩
  ext x
  simpa using congrFun hsup ⟨x, trivial⟩

中文:
定理 univ_sSup_of_nat_affine_eq
  结论: [HereditarilyLindelofSpace E]
  证明: by
  obtain ⟨l, c, hle, hsup⟩ := hφcv.sSup_of_nat_affine_eq (𝕜 := 𝕜) (s := univ) isClosed_univ
    (lowerSemicontinuousOn_univ_iff.2 hφc)
  refine ⟨l, c, fun i x => hle i ⟨x, trivial⟩, ?_⟩
  ext x
  simpa using congrFun hsup ⟨x, trivial⟩

Depends on / 依赖: cv.sSup_of_nat_affine_eq, isClosed_univ, lowerSemicontinuousOn_univ_iff, sSup_of_nat_affine_eq
-/
theorem univ_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Real univ φ) :
    exists (l : Nat -> E ->L[𝕜] 𝕜) (c : Nat -> Real), (forall i, re ∘ (l i) + const E (c i) <= φ)
      ∧ ⨆ i, re ∘ (l i) + const E (c i) = φ := by
  obtain ⟨l, c, hle, hsup⟩ := hφcv.sSup_of_nat_affine_eq (𝕜 := 𝕜) (s := univ) isClosed_univ
    (lowerSemicontinuousOn_univ_iff.2 hφc)
  refine ⟨l, c, fun i x => hle i ⟨x, trivial⟩, ?_⟩
  ext x
  simpa using congrFun hsup ⟨x, trivial⟩

end RCLike

section Real

variable [AddCommGroup E] [Module Real E] [IsTopologicalAddGroup E] [ContinuousSMul Real E]
  [LocallyConvexSpace Real E]

/--
theorem `real_sSup_affine_eq` / 定理 `real_sSup_affine_eq`

English:
theorem real_sSup_affine_eq
  statement: (hsc : IsClosed s)
  proof: sSup_affine_eq (𝕜 := Real) hsc hφc hφcv

中文:
定理 real_sSup_affine_eq
  结论: (hsc : IsClosed s)
  证明: sSup_affine_eq (𝕜 := Real) hsc hφc hφcv

Depends on / 依赖: sSup_affine_eq
-/
theorem real_sSup_affine_eq (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) :
    sSup {f | f <= s.domRestrict φ ∧
      exists (l : E ->L[Real] Real) (c : Real), f = s.domRestrict l + const s c} = s.domRestrict φ :=
  sSup_affine_eq (𝕜 := Real) hsc hφc hφcv

/--
theorem `real_sSup_of_countable_affine_eq` / 定理 `real_sSup_of_countable_affine_eq`

English:
theorem real_sSup_of_countable_affine_eq
  statement: [HereditarilyLindelofSpace E] (hsc : IsClosed s)
  proof: sSup_of_countable_affine_eq (𝕜 := Real) hsc hφc hφcv

中文:
定理 real_sSup_of_countable_affine_eq
  结论: [HereditarilyLindelofSpace E] (hsc : IsClosed s)
  证明: sSup_of_countable_affine_eq (𝕜 := Real) hsc hφc hφcv

Depends on / 依赖: sSup_of_countable_affine_eq
-/
theorem real_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) :
    exists 𝓕' : Set (s -> Real), 𝓕'.Countable ∧ sSup 𝓕' = s.domRestrict φ ∧
      forall f in 𝓕', f <= s.domRestrict φ ∧ exists (l : E ->L[Real] Real) (c : Real), f = s.domRestrict l + const s c :=
  sSup_of_countable_affine_eq (𝕜 := Real) hsc hφc hφcv

/--
theorem `real_sSup_of_nat_affine_eq` / 定理 `real_sSup_of_nat_affine_eq`

English:
theorem real_sSup_of_nat_affine_eq
  statement: [HereditarilyLindelofSpace E] (hsc : IsClosed s)
  proof: sSup_of_nat_affine_eq (𝕜 := Real) hsc hφc hφcv

中文:
定理 real_sSup_of_nat_affine_eq
  结论: [HereditarilyLindelofSpace E] (hsc : IsClosed s)
  证明: sSup_of_nat_affine_eq (𝕜 := Real) hsc hφc hφcv

Depends on / 依赖: sSup_of_nat_affine_eq
-/
theorem real_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn Real s φ) :
    exists (l : Nat -> E ->L[Real] Real) (c : Nat -> Real),
      (forall i, s.domRestrict (l i) + const s (c i) <= s.domRestrict φ) ∧
      ⨆ i, s.domRestrict (l i) + const s (c i) = s.domRestrict φ :=
  sSup_of_nat_affine_eq (𝕜 := Real) hsc hφc hφcv

/--
theorem `real_univ_sSup_affine_eq` / 定理 `real_univ_sSup_affine_eq`

English:
theorem real_univ_sSup_affine_eq
  given: (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Real univ φ)
  proof: univ_sSup_affine_eq (𝕜 := Real) hφc hφcv

中文:
定理 real_univ_sSup_affine_eq
  条件: (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn 实数 univ φ)
  证明: univ_sSup_affine_eq (𝕜 := Real) hφc hφcv

Depends on / 依赖: univ_sSup_affine_eq
-/
theorem real_univ_sSup_affine_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Real univ φ) :
    sSup {f | f <= φ ∧ exists (l : E ->L[Real] Real) (c : Real), f = l + const E c} = φ :=
  univ_sSup_affine_eq (𝕜 := Real) hφc hφcv

/--
theorem `real_univ_sSup_of_countable_affine_eq` / 定理 `real_univ_sSup_of_countable_affine_eq`

English:
theorem real_univ_sSup_of_countable_affine_eq
  statement: [HereditarilyLindelofSpace E]
  proof: univ_sSup_of_countable_affine_eq (𝕜 := Real) hφc hφcv

中文:
定理 real_univ_sSup_of_countable_affine_eq
  结论: [HereditarilyLindelofSpace E]
  证明: univ_sSup_of_countable_affine_eq (𝕜 := Real) hφc hφcv

Depends on / 依赖: univ_sSup_of_countable_affine_eq
-/
theorem real_univ_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Real univ φ) :
    exists 𝓕' : Set (E -> Real), 𝓕'.Countable ∧ sSup 𝓕' = φ ∧
      forall f in 𝓕', f <= φ ∧ exists (l : E ->L[Real] Real) (c : Real), f = l + const E c :=
  univ_sSup_of_countable_affine_eq (𝕜 := Real) hφc hφcv

/--
theorem `real_univ_sSup_of_nat_affine_eq` / 定理 `real_univ_sSup_of_nat_affine_eq`

English:
theorem real_univ_sSup_of_nat_affine_eq
  statement: [HereditarilyLindelofSpace E]
  proof: univ_sSup_of_nat_affine_eq (𝕜 := Real) hφc hφcv

中文:
定理 real_univ_sSup_of_nat_affine_eq
  结论: [HereditarilyLindelofSpace E]
  证明: univ_sSup_of_nat_affine_eq (𝕜 := Real) hφc hφcv

Depends on / 依赖: univ_sSup_of_nat_affine_eq
-/
theorem real_univ_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn Real univ φ) :
    exists (l : Nat -> E ->L[Real] Real) (c : Nat -> Real), (forall i, (l i) + const E (c i) <= φ) ∧
      ⨆ i, (l i) + const E (c i) = φ :=
  univ_sSup_of_nat_affine_eq (𝕜 := Real) hφc hφcv

end Real

end ConvexOn
