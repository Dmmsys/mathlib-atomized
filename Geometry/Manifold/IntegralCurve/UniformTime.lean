/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-!
# Uniform time lemma for the global existence of integral curves

## Main results

* `exists_isMIntegralCurve_of_isMIntegralCurveOn`: If there exists `ε > 0` such that the local
  integral curve at each point `x : M` is defined at least on an open interval `Ioo (-ε) ε`, then
  every point on `M` has a global integral curve passing through it.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field, global existence
-/

public section

open scoped Topology

open Function Manifold Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [T2Space M] {γ γ' : Real -> M} {v : (x : M) -> TangentSpace I x} {s s' : Set Real} {t₀ : Real}

/--
lemma `eqOn_of_isMIntegralCurveOn_Ioo` / 引理 `eqOn_of_isMIntegralCurveOn_Ioo`

English:
lemma eqOn_of_isMIntegralCurveOn_Ioo
  statement: [BoundarylessManifold I M]
  proof: by
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless _ hv
    (hγ a' (by positivity)) ((hγ a (lt_of_lt_of_le hpos hle)).mono _)
    (by rw [hγx a, hγx a'])
  · rw [mem_Ioo]
    exact ⟨neg_lt_zero.mpr hpos, by positivity⟩
  · apply Ioo_subset_Ioo <;> linarith

中文:
引理 eqOn_of_isM整数egralCurveOn_Ioo
  结论: [无边界流形 I M]
  证明: by
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless _ hv
    (hγ a' (by positivity)) ((hγ a (lt_of_lt_of_le hpos hle)).mono _)
    (by rw [hγx a, hγx a'])
  · rw [mem_Ioo]
    exact ⟨neg_lt_zero.mpr hpos, by positivity⟩
  · apply Ioo_subset_Ioo <;> linarith

Depends on / 依赖: Ioo_subset_Ioo, isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless, lt_of_lt_of_le, mem_Ioo, neg_lt_zero, neg_lt_zero.mpr
-/
lemma eqOn_of_isMIntegralCurveOn_Ioo [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (γ : Real -> Real -> M) (hγx : forall a, γ a 0 = x) (hγ : forall a > 0, IsMIntegralCurveOn (γ a) v (Ioo (-a) a))
    {a a' : Real} (hpos : 0 < a') (hle : a' <= a) :
    EqOn (γ a') (γ a) (Ioo (-a') a') := by
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless _ hv
    (hγ a' (by positivity)) ((hγ a (lt_of_lt_of_le hpos hle)).mono _)
    (by rw [hγx a, hγx a'])
  · rw [mem_Ioo]
    exact ⟨neg_lt_zero.mpr hpos, by positivity⟩
  · apply Ioo_subset_Ioo <;> linarith

/--
lemma `eqOn_abs_add_one_of_isMIntegralCurveOn_Ioo` / 引理 `eqOn_abs_add_one_of_isMIntegralCurveOn_Ioo`

English:
lemma eqOn_abs_add_one_of_isMIntegralCurveOn_Ioo
  statement: [BoundarylessManifold I M]
  proof: by
  intro t ht
  by_cases! hlt : |t| + 1 < a
  · exact eqOn_of_isMIntegralCurveOn_Ioo hv γ hγx hγ
      (by positivity) hlt.le (abs_lt.mp <| lt_add_one _)
  · exact eqOn_of_isMIntegralCurveOn_Ioo hv γ hγx hγ
.symm (neg_lt_self_iff.mp <| lt_trans ht.1 ht.2) hlt ht

中文:
引理 eqOn_abs_add_one_of_isM整数egralCurveOn_Ioo
  结论: [无边界流形 I M]
  证明: by
  intro t ht
  by_cases! hlt : |t| + 1 < a
  · exact eqOn_of_isMIntegralCurveOn_Ioo hv γ hγx hγ
      (by positivity) hlt.le (abs_lt.mp <| lt_add_one _)
  · exact eqOn_of_isMIntegralCurveOn_Ioo hv γ hγx hγ
.symm (neg_lt_self_iff.mp <| lt_trans ht.1 ht.2) hlt ht

Depends on / 依赖: abs_lt, abs_lt.mp, eqOn_of_isMIntegralCurveOn_Ioo, hlt.le, lt_add_one, lt_trans, neg_lt_self_iff, neg_lt_self_iff.mp
-/
lemma eqOn_abs_add_one_of_isMIntegralCurveOn_Ioo [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (γ : Real -> Real -> M) (hγx : forall a, γ a 0 = x) (hγ : forall a > 0, IsMIntegralCurveOn (γ a) v (Ioo (-a) a))
    {a : Real} : EqOn (fun t => γ (|t| + 1) t) (γ a) (Ioo (-a) a) := by
  intro t ht
  by_cases! hlt : |t| + 1 < a
  · exact eqOn_of_isMIntegralCurveOn_Ioo hv γ hγx hγ
      (by positivity) hlt.le (abs_lt.mp <| lt_add_one _)
  · exact eqOn_of_isMIntegralCurveOn_Ioo hv γ hγx hγ
.symm (neg_lt_self_iff.mp <| lt_trans ht.1 ht.2) hlt ht

/--
lemma `isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo` / 引理 `isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo`

English:
lemma isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo
  statement: [BoundarylessManifold I M]
  proof: by
  intro t
  have ht : t in Ioo (-(|t| + 1)) (|t| + 1) := by
    rw [mem_Ioo]; rw [← abs_lt]
    exact lt_add_one _
  apply HasMFDerivAt.congr_of_eventuallyEq (f := γ (|t| + 1))
.hasMFDerivAt (Ioo_mem_nhds ht.1 ht.2) · exact hγ (|t| + 1) (by positivity) _ ht
  · rw [Filter.eventuallyEq_iff_exists_

中文:
引理 isM整数egralCurve_abs_add_one_of_isM整数egralCurveOn_Ioo
  结论: [无边界流形 I M]
  证明: by
  intro t
  have ht : t in Ioo (-(|t| + 1)) (|t| + 1) := by
    rw [mem_Ioo]; rw [← abs_lt]
    exact lt_add_one _
  apply HasMFDerivAt.congr_of_eventuallyEq (f := γ (|t| + 1))
.hasMFDerivAt (Ioo_mem_nhds ht.1 ht.2) · exact hγ (|t| + 1) (by positivity) _ ht
  · rw [Filter.eventuallyEq_iff_exists_

Depends on / 依赖: Filter, Filter.eventuallyEq_iff_exists_mem, HasMFDerivAt, HasMFDerivAt.congr_of_eventuallyEq, Ioo_mem_nhds, abs_lt, congr_of_eventuallyEq, eqOn_abs_add_one_of_isMIntegralCurveOn_Ioo, eventuallyEq_iff_exists_mem, hasMFDerivAt, lt_add_of_pos_right, lt_add_one, mem_Ioo, zero_lt_one
-/
lemma isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (γ : Real -> Real -> M) (hγx : forall a, γ a 0 = x) (hγ : forall a > 0, IsMIntegralCurveOn (γ a) v (Ioo (-a) a)) :
    IsMIntegralCurve (fun t => γ (|t| + 1) t) v := by
  intro t
  have ht : t in Ioo (-(|t| + 1)) (|t| + 1) := by
    rw [mem_Ioo]; rw [← abs_lt]
    exact lt_add_one _
  apply HasMFDerivAt.congr_of_eventuallyEq (f := γ (|t| + 1))
.hasMFDerivAt (Ioo_mem_nhds ht.1 ht.2) · exact hγ (|t| + 1) (by positivity) _ ht
  · rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo (-(|t| + 1)) (|t| + 1), ?_,
      eqOn_abs_add_one_of_isMIntegralCurveOn_Ioo hv γ hγx hγ⟩
    have : |t| < |t| + 1 := lt_add_of_pos_right |t| zero_lt_one
    rw [abs_lt] at this
    exact Ioo_mem_nhds this.1 this.2

/--
lemma `exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo` / 引理 `exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo`

English:
lemma exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo
  statement: [BoundarylessManifold I M]
  proof: by
  refine ⟨fun ⟨γ, h1, h2⟩ _ => ⟨γ, h1, h2.isMIntegralCurveOn _⟩, fun h => ?_⟩
  choose γ hγx hγ using h
  exact ⟨fun t => γ (|t| + 1) t, hγx (|0| + 1),
    isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo hv γ hγx (fun a _ => hγ a)⟩

中文:
引理 存在_isM整数egralCurve_iff_存在_isM整数egralCurveOn_Ioo
  结论: [无边界流形 I M]
  证明: by
  refine ⟨fun ⟨γ, h1, h2⟩ _ => ⟨γ, h1, h2.isMIntegralCurveOn _⟩, fun h => ?_⟩
  choose γ hγx hγ using h
  exact ⟨fun t => γ (|t| + 1) t, hγx (|0| + 1),
    isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo hv γ hγx (fun a _ => hγ a)⟩

Depends on / 依赖: h2.isMIntegralCurveOn, isMIntegralCurveOn, isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo
-/
lemma exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) (x : M) :
    (exists γ, γ 0 = x ∧ IsMIntegralCurve γ v) ↔
      forall a, exists γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-a) a) := by
  refine ⟨fun ⟨γ, h1, h2⟩ _ => ⟨γ, h1, h2.isMIntegralCurveOn _⟩, fun h => ?_⟩
  choose γ hγx hγ using h
  exact ⟨fun t => γ (|t| + 1) t, hγx (|0| + 1),
    isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo hv γ hγx (fun a _ => hγ a)⟩

/--
lemma `eqOn_piecewise_of_isMIntegralCurveOn_Ioo` / 引理 `eqOn_piecewise_of_isMIntegralCurveOn_Ioo`

English:
lemma eqOn_piecewise_of_isMIntegralCurveOn_Ioo
  statement: [BoundarylessManifold I M]
  proof: by
  intro t ht
  suffices H : EqOn γ γ' (Ioo (max a a') (min b b')) by
    by_cases hmem : t in Ioo a b
    · rw [piecewise, if_pos hmem]
      apply H
      simp [ht.1, ht.2, hmem.1, hmem.2]
    · rw [piecewise, if_neg hmem]
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless _ hv
    (h

中文:
引理 eqOn_piecewise_of_isM整数egralCurveOn_Ioo
  结论: [无边界流形 I M]
  证明: by
  intro t ht
  suffices H : EqOn γ γ' (Ioo (max a a') (min b b')) by
    by_cases hmem : t in Ioo a b
    · rw [piecewise, if_pos hmem]
      apply H
      simp [ht.1, ht.2, hmem.1, hmem.2]
    · rw [piecewise, if_neg hmem]
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless _ hv
    (h

Depends on / 依赖: Ioo_subset_Ioo, if_neg, if_pos, isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless, le_max_left, le_max_right, lt_min, max_lt, min_le_left, min_le_right, piecewise
-/
lemma eqOn_piecewise_of_isMIntegralCurveOn_Ioo [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {a b a' b' : Real} (hγ : IsMIntegralCurveOn γ v (Ioo a b))
    (hγ' : IsMIntegralCurveOn γ' v (Ioo a' b'))
    (ht₀ : t₀ in Ioo a b inter Ioo a' b') (h : γ t₀ = γ' t₀) :
    EqOn (piecewise (Ioo a b) γ γ') γ' (Ioo a' b') := by
  intro t ht
  suffices H : EqOn γ γ' (Ioo (max a a') (min b b')) by
    by_cases hmem : t in Ioo a b
    · rw [piecewise, if_pos hmem]
      apply H
      simp [ht.1, ht.2, hmem.1, hmem.2]
    · rw [piecewise, if_neg hmem]
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless _ hv
    (hγ.mono (Ioo_subset_Ioo (le_max_left ..) (min_le_left ..)))
    (hγ'.mono (Ioo_subset_Ioo (le_max_right ..) (min_le_right ..))) h
  exact ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩

/--
lemma `isMIntegralCurveOn_piecewise` / 引理 `isMIntegralCurveOn_piecewise`

English:
lemma isMIntegralCurveOn_piecewise
  statement: [BoundarylessManifold I M]
  proof: by
  intro t ht
  by_cases hmem : t in Ioo a b
  · rw [piecewise, if_pos hmem]
.hasMFDerivWithinAt .hasMFDerivAt (Ioo_mem_nhds hmem.1 hmem.2) apply hγ t hmem
.congr_of_eventuallyEq _ (by rw [piecewise, if_pos hmem]) (s := Ioo a b union Ioo a' b')
    rw [Filter.eventuallyEq_iff_exists_mem]
    refin

中文:
引理 isM整数egralCurveOn_piecewise
  结论: [无边界流形 I M]
  证明: by
  intro t ht
  by_cases hmem : t in Ioo a b
  · rw [piecewise, if_pos hmem]
.hasMFDerivWithinAt .hasMFDerivAt (Ioo_mem_nhds hmem.1 hmem.2) apply hγ t hmem
.congr_of_eventuallyEq _ (by rw [piecewise, if_pos hmem]) (s := Ioo a b union Ioo a' b')
    rw [Filter.eventuallyEq_iff_exists_mem]
    refin

Depends on / 依赖: Filter, Filter.eventuallyEq_iff_exists_mem, Ioo_mem_nhds, congr_of_eventuallyEq, eventuallyEq_iff_exists_mem, hasMFDerivAt, hasMFDerivWithinAt, if_pos, isOpen_Ioo, isOpen_Ioo.union, mem_union, nhdsWithin_eq, or_iff_not_imp_left, piecewise
-/
lemma isMIntegralCurveOn_piecewise [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {a b a' b' : Real} (hγ : IsMIntegralCurveOn γ v (Ioo a b))
    (hγ' : IsMIntegralCurveOn γ' v (Ioo a' b')) {t₀ : Real}
    (ht₀ : t₀ in Ioo a b inter Ioo a' b') (h : γ t₀ = γ' t₀) :
    IsMIntegralCurveOn (piecewise (Ioo a b) γ γ') v (Ioo a b union Ioo a' b') := by
  intro t ht
  by_cases hmem : t in Ioo a b
  · rw [piecewise, if_pos hmem]
.hasMFDerivWithinAt .hasMFDerivAt (Ioo_mem_nhds hmem.1 hmem.2) apply hγ t hmem
.congr_of_eventuallyEq _ (by rw [piecewise, if_pos hmem]) (s := Ioo a b union Ioo a' b')
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a b, ?_, fun _ ht' => by rw [piecewise, if_pos ht']⟩
    rw [(isOpen_Ioo.union isOpen_Ioo).nhdsWithin_eq ht]
    exact Ioo_mem_nhds hmem.1 hmem.2
  · have ht' := ht
    rw [mem_union]; rw [or_iff_not_imp_left] at ht
    rw [piecewise]; rw [if_neg hmem]
.hasMFDerivAt (Ioo_mem_nhds (ht hmem).1 (ht hmem).2) apply hγ' t (ht hmem)
.hasMFDerivWithinAt (s := Ioo a b union Ioo a' b')
.congr_of_eventuallyEq _ (by rw [piecewise, if_neg hmem])
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a' b', ?_,
      eqOn_piecewise_of_isMIntegralCurveOn_Ioo hv hγ hγ' ht₀ h⟩
    rw [(isOpen_Ioo.union isOpen_Ioo).nhdsWithin_eq ht']
    exact Ioo_mem_nhds (ht hmem).1 (ht hmem).2

/--
lemma `exists_isMIntegralCurve_of_isMIntegralCurveOn` / 引理 `exists_isMIntegralCurve_of_isMIntegralCurveOn`

English:
lemma exists_isMIntegralCurve_of_isMIntegralCurveOn
  statement: [BoundarylessManifold I M]
  proof: by
  let s := { a | exists γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-a) a) }
  suffices hbdd : ¬BddAbove s by
    rw [not_bddAbove_iff] at hbdd
    rw [exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv]
    intro a
    obtain ⟨y, ⟨γ, hγ1, hγ2⟩, hlt⟩ := hbdd a
exact ⟨γ, hγ1, hγ2.mono Ioo_

中文:
引理 存在_isM整数egralCurve_of_isM整数egralCurveOn
  结论: [无边界流形 I M]
  证明: by
  let s := { a | exists γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-a) a) }
  suffices hbdd : ¬BddAbove s by
    rw [not_bddAbove_iff] at hbdd
    rw [exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv]
    intro a
    obtain ⟨y, ⟨γ, hγ1, hγ2⟩, hlt⟩ := hbdd a
exact ⟨γ, hγ1, hγ2.mono Ioo_

Depends on / 依赖: BddAbove, Ioo_subset_Ioo, IsMIntegralCurveOn, exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo, hlt.le, neg_le_neg, not_bddAbove_iff
-/
lemma exists_isMIntegralCurve_of_isMIntegralCurveOn [BoundarylessManifold I M]
    {v : (x : M) -> TangentSpace I x}
    (hv : CMDiff 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {ε : Real} (hε : 0 < ε) (h : forall x : M, exists γ : Real -> M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε))
    (x : M) : exists γ : Real -> M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  let s := { a | exists γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-a) a) }
  suffices hbdd : ¬BddAbove s by
    rw [not_bddAbove_iff] at hbdd
    rw [exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv]
    intro a
    obtain ⟨y, ⟨γ, hγ1, hγ2⟩, hlt⟩ := hbdd a
exact ⟨γ, hγ1, hγ2.mono Ioo_subset_Ioo (neg_le_neg hlt.le) hlt.le⟩
  intro hbdd
  set asup := sSup s with hasup
  -- we will obtain two integral curves, one centred at some `t₀ > 0` with
  -- `0 ≤ asup - ε < t₀ < asup`; let `t₀ = asup - ε / 2`
  -- another centred at 0 with domain up to `a ∈ S` with `t₀ < a < asup`
  obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup (⟨ε, h x⟩ : Set.Nonempty s) (ε := - (ε / 2))
    (by rw [neg_lt, neg_zero]; exact half_pos hε)
  rw [mem_ofPred] at ha
  rw [← hasup]; rw [← sub_eq_add_neg] at hlt
  -- integral curve defined on `Ioo (-a) a`
  obtain ⟨γ, h0, hγ⟩ := ha
  -- integral curve starting at `-(asup - ε / 2)` with radius `ε`
  obtain ⟨γ1_aux, h1_aux, hγ1⟩ := h (γ (-(asup - ε / 2)))
  rw [← isMIntegralCurveOn_comp_add (dt := asup - ε / 2)] at hγ1
  set γ1 := γ1_aux ∘ (· + (asup - ε / 2)) with γ1_def
  have heq1 : γ1 (-(asup - ε / 2)) = γ (-(asup - ε / 2)) := by simp [γ1_def, h1_aux]
  -- integral curve starting at `asup - ε / 2` with radius `ε`
  obtain ⟨γ2_aux, h2_aux, hγ2⟩ := h (γ (asup - ε / 2))
  rw [← isMIntegralCurveOn_comp_sub (dt := asup - ε / 2)] at hγ2
  set γ2 := γ2_aux ∘ (· - (asup - ε / 2)) with γ2_def
  have heq2 : γ2 (asup - ε / 2) = γ (asup - ε / 2) := by simp [γ2_def, h2_aux]
  -- rewrite shifted Ioo as Ioo
  simp_rw [Set.mem_Ioo, ← sub_lt_iff_lt_add, ← lt_sub_iff_add_lt, ← Set.mem_Ioo] at hγ1
  simp_rw [Set.mem_Ioo, lt_sub_iff_add_lt, sub_lt_iff_lt_add, ← Set.mem_Ioo] at hγ2
  -- to help `linarith`
  have hεle : ε <= asup := le_csSup hbdd (h x)
  -- extend `γ` on the left by `γ1` and on the right by `γ2`
  set γ_ext : Real -> M := piecewise (Ioo (-(asup + ε / 2)) a)
    (piecewise (Ioo (-a) a) γ γ1) γ2 with γ_ext_def
  have heq_ext : γ_ext 0 = x := by
    rw [γ_ext_def]; rw [piecewise]; rw [if_pos ⟨by linarith]; rw [by linarith⟩]; rw [piecewise]; rw [if_pos ⟨by linarith]; rw [by linarith⟩]; rw [h0]
  -- `asup + ε / 2` is an element of `s` greater than `asup`, a contradiction
  suffices hext : IsMIntegralCurveOn γ_ext v (Ioo (-(asup + ε / 2)) (asup + ε / 2)) from
(not_lt.mpr <| le_csSup hbdd ⟨γ_ext, heq_ext, hext⟩) lt_add_of_pos_right asup (half_pos hε)
  apply (isMIntegralCurveOn_piecewise (t₀ := asup - ε / 2) hv _ hγ2
      ⟨⟨by linarith, hlt⟩, ⟨by linarith, by linarith⟩⟩
      (by rw [piecewise, if_pos ⟨by linarith, hlt⟩, ← heq2])).mono
    (Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith))
  exact (isMIntegralCurveOn_piecewise (t₀ := -(asup - ε / 2)) hv hγ hγ1
      ⟨⟨neg_lt_neg hlt, by linarith⟩, ⟨by linarith, by linarith⟩⟩ heq1.symm).mono
    (union_comm _ _ ▸ Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl)
