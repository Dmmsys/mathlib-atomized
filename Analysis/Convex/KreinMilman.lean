/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# The Krein-Milman theorem

This file proves the Krein-Milman lemma and the Krein-Milman theorem.

## The lemma

The lemma states that a nonempty compact set `s` has an extreme point. The proof goes:
1. Using Zorn's lemma, find a minimal nonempty closed `t` that is an extreme subset of `s`. We will
  show that `t` is a singleton, thus corresponding to an extreme point.
2. By contradiction, `t` contains two distinct points `x` and `y`.
3. With the (geometric) Hahn-Banach theorem, find a hyperplane that separates `x` and `y`.
4. Look at the extreme (actually exposed) subset of `t` obtained by going the furthest away from
  the separating hyperplane in the direction of `x`. It is nonempty, closed and an extreme subset
  of `s`.
5. It is a strict subset of `t` (`y` isn't in it), so `t` isn't minimal. Absurd.

## The theorem

The theorem states that a compact convex set `s` is the closure of the convex hull of its extreme
points. It is an almost immediate strengthening of the lemma. The proof goes:
1. By contradiction, `s \ closure (convexHull ℝ (extremePoints ℝ s))` is nonempty, say with `x`.
2. With the (geometric) Hahn-Banach theorem, find a hyperplane that separates `x` from
  `closure (convexHull ℝ (extremePoints ℝ s))`.
3. Look at the extreme (actually exposed) subset of
  `s \ closure (convexHull ℝ (extremePoints ℝ s))` obtained by going the furthest away from the
  separating hyperplane. It is nonempty by assumption of nonemptiness and compactness, so by the
  lemma it has an extreme point.
4. This point is also an extreme point of `s`. Absurd.

## Related theorems

When the space is finite dimensional, the `closure` can be dropped to strengthen the result of the
Krein-Milman theorem. This leads to the Minkowski-Carathéodory theorem (currently not in mathlib).
Birkhoff's theorem is the Minkowski-Carathéodory theorem applied to the set of bistochastic
matrices, permutation matrices being the extreme points.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

-/

public section

open Set

variable {E F : Type*} [AddCommGroup E] [Module Real E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul Real E] [LocallyConvexSpace Real E] {s : Set E}
  [AddCommGroup F] [Module Real F] [TopologicalSpace F] [T1Space F]

/--
theorem `IsCompact.extremePoints_nonempty` / 定理 `IsCompact.extremePoints_nonempty`

English:
theorem IsCompact.extremePoints_nonempty
  given: (hscomp : IsCompact s) (hsnemp : s.Nonempty)
  proof: by
  let S : Set (Set E) := { t | t.Nonempty ∧ IsClosed t ∧ IsExtreme Real s t }
  rsuffices ⟨t, ht⟩ : exists t, Minimal (· in S) t
  · obtain ⟨⟨x, hxt⟩, htclos, hst⟩ := ht.prop
    refine ⟨x, IsExtreme.mem_extremePoints ?_⟩
    rwa [← eq_singleton_iff_unique_mem.2 ⟨hxt, fun y hyB => ?_⟩]
    by_con

中文:
定理 是紧集.extremePoints_nonempty
  条件: (hscomp : 是紧集 s) (hsnemp : s.非空)
  证明: by
  let S : Set (Set E) := { t | t.Nonempty ∧ IsClosed t ∧ IsExtreme Real s t }
  rsuffices ⟨t, ht⟩ : exists t, Minimal (· in S) t
  · obtain ⟨⟨x, hxt⟩, htclos, hst⟩ := ht.prop
    refine ⟨x, IsExtreme.mem_extremePoints ?_⟩
    rwa [← eq_singleton_iff_unique_mem.2 ⟨hxt, fun y hyB => ?_⟩]
    by_con

Depends on / 依赖: IsClosed, IsExposed, IsExtreme, IsExtreme.mem_extremePoints, Minimal, Nonempty, continuous, continuousOn, eq_singleton_iff_unique_mem, exists_isMaxOn, geometric_hahn_banach_point_point, hscomp, hscomp.of_isClosed_subset, ht.prop, htclos, l.continuous.continuousOn, mem_extremePoints, of_isClosed_subset, rsuffices, t.Nonempty
-/
theorem IsCompact.extremePoints_nonempty (hscomp : IsCompact s) (hsnemp : s.Nonempty) :
    (s.extremePoints Real).Nonempty := by
  let S : Set (Set E) := { t | t.Nonempty ∧ IsClosed t ∧ IsExtreme Real s t }
  rsuffices ⟨t, ht⟩ : exists t, Minimal (· in S) t
  · obtain ⟨⟨x, hxt⟩, htclos, hst⟩ := ht.prop
    refine ⟨x, IsExtreme.mem_extremePoints ?_⟩
    rwa [← eq_singleton_iff_unique_mem.2 ⟨hxt, fun y hyB => ?_⟩]
    by_contra hyx
    obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hyx
    obtain ⟨z, hzt, hz⟩ :=
      (hscomp.of_isClosed_subset htclos hst.1).exists_isMaxOn ⟨x, hxt⟩
        l.continuous.continuousOn
    have h : IsExposed Real t ({ z in t | forall w in t, l w <= l z }) := fun _ => ⟨l, rfl⟩
    rw [ht.eq_of_ge (y := ({ z in t | forall w in t]; rw [l w <= l z }))
      ⟨⟨z]; rw [hzt]; rw [hz⟩]; rw [h.isClosed htclos]; rw [hst.trans h.isExtreme⟩ (t.sep_subset _)] at hyB
    exact hl.not_ge (hyB.2 x hxt)
  refine zorn_superset _ fun F hFS hF => ?_
  obtain rfl | hFnemp := F.eq_empty_or_nonempty
  · exact ⟨s, ⟨hsnemp, hscomp.isClosed, IsExtreme.rfl⟩, fun _ => False.elim⟩
  refine ⟨⋂₀ F, ⟨?_, isClosed_sInter fun t ht => (hFS ht).2.1,
    isExtreme_sInter hFnemp fun t ht => (hFS ht).2.2⟩, fun t ht => sInter_subset_of_mem ht⟩
  have : Nonempty (↥F) := hFnemp.to_subtype
  rw [sInter_eq_iInter]
  refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ (fun t u => ?_)
    (fun t => (hFS t.mem).1)
    (fun t => hscomp.of_isClosed_subset (hFS t.mem).2.1 (hFS t.mem).2.2.1) fun t =>
      (hFS t.mem).2.1
  obtain htu | hut := hF.total t.mem u.mem
  exacts [⟨t, Subset.rfl, htu⟩, ⟨u, hut, Subset.rfl⟩]

/--
theorem `closure_convexHull_extremePoints` / 定理 `closure_convexHull_extremePoints`

English:
theorem closure_convexHull_extremePoints
  given: (hscomp : IsCompact s) (hAconv : Convex Real s)
  proof: by
  apply (closure_minimal (convexHull_min extremePoints_subset hAconv) hscomp.isClosed).antisymm
  by_contra hs
  obtain ⟨x, hxA, hxt⟩ := not_subset.1 hs
  obtain ⟨l, r, hlr, hrx⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull _ _).closure isClosed_closure hxt
  have h : IsExposed Re

中文:
定理 closure_convexHull_extremePoints
  条件: (hscomp : 是紧集 s) (hAconv : 凸 实数 s)
  证明: by
  apply (closure_minimal (convexHull_min extremePoints_subset hAconv) hscomp.isClosed).antisymm
  by_contra hs
  obtain ⟨x, hxA, hxt⟩ := not_subset.1 hs
  obtain ⟨l, r, hlr, hrx⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull _ _).closure isClosed_closure hxt
  have h : IsExposed Re

Depends on / 依赖: IsExposed, antisymm, closure, closure_minimal, continuous, continuousOn, convexHull_min, convex_convexHull, exists_isMaxOn, extremePoints_nonempty, extremePoints_subset, geometric_hahn_banach_closed_point, h.isCompact, hAconv, hscomp, hscomp.exists_isMaxOn, hscomp.isClosed, isClosed, isClosed_closure, isCompact
-/
theorem closure_convexHull_extremePoints (hscomp : IsCompact s) (hAconv : Convex Real s) :
    closure (convexHull Real <| s.extremePoints Real) = s := by
  apply (closure_minimal (convexHull_min extremePoints_subset hAconv) hscomp.isClosed).antisymm
  by_contra hs
  obtain ⟨x, hxA, hxt⟩ := not_subset.1 hs
  obtain ⟨l, r, hlr, hrx⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull _ _).closure isClosed_closure hxt
  have h : IsExposed Real s ({ y in s | forall z in s, l z <= l y }) := fun _ => ⟨l, rfl⟩
  obtain ⟨z, hzA, hz⟩ := hscomp.exists_isMaxOn ⟨x, hxA⟩ l.continuous.continuousOn
  obtain ⟨y, hy⟩ := (h.isCompact hscomp).extremePoints_nonempty ⟨z, hzA, hz⟩
  linarith [hlr _ (subset_closure <| subset_convexHull _ _ <|
    h.isExtreme.extremePoints_subset_extremePoints hy), hy.1.2 x hxA]

/--
lemma `surjOn_extremePoints_image` / 引理 `surjOn_extremePoints_image`

English:
lemma surjOn_extremePoints_image
  given: (f : E ->ᴬ[Real] F) (hs : IsCompact s)
  proof: by
  rintro w hw
  -- The fiber of `w` is nonempty and compact
  have ht : IsCompact {x in s | f x = w} :=
hs.inter_right isClosed_singleton.preimage f.continuous
  have ht₀ : {x in s | f x = w}.Nonempty := by simpa using! extremePoints_subset hw
  -- Hence by the Krein-Milman lemma it has an extrem

中文:
引理 surjOn_extremePoints_image
  条件: (f : E ->ᴬ[实数] F) (hs : 是紧集 s)
  证明: by
  rintro w hw
  -- The fiber of `w` is nonempty and compact
  have ht : IsCompact {x in s | f x = w} :=
hs.inter_right isClosed_singleton.preimage f.continuous
  have ht₀ : {x in s | f x = w}.Nonempty := by simpa using! extremePoints_subset hw
  -- Hence by the Krein-Milman lemma it has an extrem
-/
lemma surjOn_extremePoints_image (f : E ->ᴬ[Real] F) (hs : IsCompact s) :
    SurjOn f (extremePoints Real s) (extremePoints Real (f '' s)) := by
  rintro w hw
  -- The fiber of `w` is nonempty and compact
  have ht : IsCompact {x in s | f x = w} :=
hs.inter_right isClosed_singleton.preimage f.continuous
  have ht₀ : {x in s | f x = w}.Nonempty := by simpa using! extremePoints_subset hw
  -- Hence by the Krein-Milman lemma it has an extreme point `x`
  obtain ⟨x, ⟨hx, rfl⟩, hyt⟩ := ht.extremePoints_nonempty ht₀
  -- `f x = w` and `x` is an extreme point of `s`, so we're done
  refine mem_image_of_mem _ ⟨hx, fun y hy z hz hxyz => ?_⟩
  have := by simpa using! image_openSegment _ f.toAffineMap y z
  rw [mem_extremePoints] at hw
have := hw.2 _ (mem_image_of_mem _ hy) _ (mem_image_of_mem _ hz) by
    rw [← this]; exact mem_image_of_mem _ hxyz
  exact hyt ⟨hy, this.1⟩ ⟨hz, this.2⟩ hxyz
