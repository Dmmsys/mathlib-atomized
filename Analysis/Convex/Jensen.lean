/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.FieldSimp

/-!
# Jensen's inequality and maximum principle for convex functions

In this file, we prove the finite Jensen inequality and the finite maximum principle for convex
functions. The integral versions are to be found in `Analysis.Convex.Integral`.

## Main declarations

Jensen's inequalities:
* `ConvexOn.map_centerMass_le`, `ConvexOn.map_sum_le`: Convex Jensen's inequality. The image of a
  convex combination of points under a convex function is less than the convex combination of the
  images.
* `ConcaveOn.le_map_centerMass`, `ConcaveOn.le_map_sum`: Concave Jensen's inequality.
* `StrictConvexOn.map_sum_lt`: Convex strict Jensen inequality.
* `StrictConcaveOn.lt_map_sum`: Concave strict Jensen inequality.

As corollaries, we get:
* `StrictConvexOn.map_sum_eq_iff`: Equality case of the convex Jensen inequality.
* `StrictConcaveOn.map_sum_eq_iff`: Equality case of the concave Jensen inequality.
* `ConvexOn.exists_ge_of_mem_convexHull`: Maximum principle for convex functions.
* `ConcaveOn.exists_le_of_mem_convexHull`: Minimum principle for concave functions.
-/

public section


open Finset LinearMap Set Convex Pointwise

variable {𝕜 E F β ι : Type*}

/-! ### Jensen's inequality -/


section Jensen

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [AddCommGroup β]
  [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 E] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]
  {s : Set E} {f : E -> β} {t : Finset ι} {w : ι -> 𝕜} {p : ι -> E} {v : 𝕜} {q : E}

/--
theorem `ConvexOn.map_centerMass_le` / 定理 `ConvexOn.map_centerMass_le`

English:
theorem ConvexOn.map_centerMass_le
  statement: (hf : ConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
  proof: by
  have hmem' : forall i in t, (p i, (f ∘ p) i) in { p : E × β | p.1 in s ∧ f p.1 <= p.2 } := fun i hi =>
    ⟨hmem i hi, le_rfl⟩
  convert! (hf.convex_epigraph.centerMass_mem h₀ h₁ hmem').2 <;>
    simp only [centerMass, Function.comp, Prod.smul_fst, Prod.fst_sum, Prod.smul_snd, Prod.snd_sum]

中文:
定理 ConvexOn.map_centerMass_le
  结论: (hf : ConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i)
  证明: by
  have hmem' : forall i in t, (p i, (f ∘ p) i) in { p : E × β | p.1 in s ∧ f p.1 <= p.2 } := fun i hi =>
    ⟨hmem i hi, le_rfl⟩
  convert! (hf.convex_epigraph.centerMass_mem h₀ h₁ hmem').2 <;>
    simp only [centerMass, Function.comp, Prod.smul_fst, Prod.fst_sum, Prod.smul_snd, Prod.snd_sum]

Depends on / 依赖: Function, Function.comp, Prod.fst_sum, Prod.smul_fst, Prod.smul_snd, Prod.snd_sum, centerMass, centerMass_mem, convert, convex_epigraph, fst_sum, hf.convex_epigraph.centerMass_mem, le_rfl, smul_fst, smul_snd, snd_sum
-/
theorem ConvexOn.map_centerMass_le (hf : ConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
    (h₁ : 0 < ∑ i in t, w i) (hmem : forall i in t, p i in s) :
    f (t.centerMass w p) <= t.centerMass w (f ∘ p) := by
  have hmem' : forall i in t, (p i, (f ∘ p) i) in { p : E × β | p.1 in s ∧ f p.1 <= p.2 } := fun i hi =>
    ⟨hmem i hi, le_rfl⟩
  convert! (hf.convex_epigraph.centerMass_mem h₀ h₁ hmem').2 <;>
    simp only [centerMass, Function.comp, Prod.smul_fst, Prod.fst_sum, Prod.smul_snd, Prod.snd_sum]

/--
theorem `ConcaveOn.le_map_centerMass` / 定理 `ConcaveOn.le_map_centerMass`

English:
theorem ConcaveOn.le_map_centerMass
  statement: (hf : ConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
  proof: ConvexOn.map_centerMass_le (β := βᵒᵈ) hf h₀ h₁ hmem

中文:
定理 ConcaveOn.le_map_centerMass
  结论: (hf : ConcaveOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i)
  证明: ConvexOn.map_centerMass_le (β := βᵒᵈ) hf h₀ h₁ hmem

Depends on / 依赖: ConvexOn, ConvexOn.map_centerMass_le, map_centerMass_le
-/
theorem ConcaveOn.le_map_centerMass (hf : ConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
    (h₁ : 0 < ∑ i in t, w i) (hmem : forall i in t, p i in s) :
    t.centerMass w (f ∘ p) <= f (t.centerMass w p) :=
  ConvexOn.map_centerMass_le (β := βᵒᵈ) hf h₀ h₁ hmem

/--
theorem `ConvexOn.map_sum_le` / 定理 `ConvexOn.map_sum_le`

English:
theorem ConvexOn.map_sum_le
  statement: (hf : ConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1)
  proof: by
  simpa only [centerMass, h₁, inv_one, one_smul] using!
    hf.map_centerMass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

中文:
定理 ConvexOn.map_sum_le
  结论: (hf : ConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1)
  证明: by
  simpa only [centerMass, h₁, inv_one, one_smul] using!
    hf.map_centerMass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

Depends on / 依赖: centerMass, hf.map_centerMass_le, inv_one, map_centerMass_le, one_smul, zero_lt_one
-/
theorem ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1)
    (hmem : forall i in t, p i in s) : f (∑ i in t, w i • p i) <= ∑ i in t, w i • f (p i) := by
  simpa only [centerMass, h₁, inv_one, one_smul] using!
    hf.map_centerMass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

/--
theorem `ConcaveOn.le_map_sum` / 定理 `ConcaveOn.le_map_sum`

English:
theorem ConcaveOn.le_map_sum
  statement: (hf : ConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
  proof: ConvexOn.map_sum_le (β := βᵒᵈ) hf h₀ h₁ hmem

中文:
定理 ConcaveOn.le_map_sum
  结论: (hf : ConcaveOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i)
  证明: ConvexOn.map_sum_le (β := βᵒᵈ) hf h₀ h₁ hmem

Depends on / 依赖: ConvexOn, ConvexOn.map_sum_le, map_sum_le
-/
theorem ConcaveOn.le_map_sum (hf : ConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    (∑ i in t, w i • f (p i)) <= f (∑ i in t, w i • p i) :=
  ConvexOn.map_sum_le (β := βᵒᵈ) hf h₀ h₁ hmem

/--
lemma `ConvexOn.map_add_sum_le` / 引理 `ConvexOn.map_add_sum_le`

English:
lemma ConvexOn.map_add_sum_le
  statement: (hf : ConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
  proof: by
  let W j := Option.elim j v w
  let P j := Option.elim j q p
  have : f (∑ j in insertNone t, W j • P j) <= ∑ j in insertNone t, W j • f (P j) :=
    hf.map_sum_le (forall_mem_insertNone.2 ⟨hv, h₀⟩) (by simpa using! h₁)
      (forall_mem_insertNone.2 ⟨hq, hmem⟩)
  simpa using! this

中文:
引理 ConvexOn.map_add_sum_le
  结论: (hf : ConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i)
  证明: by
  let W j := Option.elim j v w
  let P j := Option.elim j q p
  have : f (∑ j in insertNone t, W j • P j) <= ∑ j in insertNone t, W j • f (P j) :=
    hf.map_sum_le (forall_mem_insertNone.2 ⟨hv, h₀⟩) (by simpa using! h₁)
      (forall_mem_insertNone.2 ⟨hq, hmem⟩)
  simpa using! this

Depends on / 依赖: Option.elim, forall_mem_insertNone, hf.map_sum_le, insertNone, map_sum_le
-/
lemma ConvexOn.map_add_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
    (h₁ : v + ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) (hv : 0 <= v) (hq : q in s) :
    f (v • q + ∑ i in t, w i • p i) <= v • f q + ∑ i in t, w i • f (p i) := by
  let W j := Option.elim j v w
  let P j := Option.elim j q p
  have : f (∑ j in insertNone t, W j • P j) <= ∑ j in insertNone t, W j • f (P j) :=
    hf.map_sum_le (forall_mem_insertNone.2 ⟨hv, h₀⟩) (by simpa using! h₁)
      (forall_mem_insertNone.2 ⟨hq, hmem⟩)
  simpa using! this

/--
lemma `ConcaveOn.map_add_sum_le` / 引理 `ConcaveOn.map_add_sum_le`

English:
lemma ConcaveOn.map_add_sum_le
  statement: (hf : ConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
  proof: hf.dual.map_add_sum_le h₀ h₁ hmem hv hq

中文:
引理 ConcaveOn.map_add_sum_le
  结论: (hf : ConcaveOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i)
  证明: hf.dual.map_add_sum_le h₀ h₁ hmem hv hq

Depends on / 依赖: hf.dual.map_add_sum_le, map_add_sum_le
-/
lemma ConcaveOn.map_add_sum_le (hf : ConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
    (h₁ : v + ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) (hv : 0 <= v) (hq : q in s) :
    v • f q + ∑ i in t, w i • f (p i) <= f (v • q + ∑ i in t, w i • p i) :=
  hf.dual.map_add_sum_le h₀ h₁ hmem hv hq

/-! ### Strict Jensen inequality -/

/--
lemma `StrictConvexOn.map_sum_lt` / 引理 `StrictConvexOn.map_sum_lt`

English:
lemma StrictConvexOn.map_sum_lt
  statement: (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: by
  classical
  obtain ⟨j, hj, k, hk, hjk⟩ := hp
  -- We replace `t` by `t \ {j, k}`
  have : k in t.erase j := mem_erase.2 ⟨ne_of_apply_ne _ hjk.symm, hk⟩
  let u := (t.erase j).erase k
  have hj : j ∉ u := by simp [u]
  have hk : k ∉ u := by simp [u]
  have ht :
      t = (u.cons k hk).cons j (me

中文:
引理 StrictConvexOn.map_sum_lt
  结论: (hf : StrictConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: by
  classical
  obtain ⟨j, hj, k, hk, hjk⟩ := hp
  -- We replace `t` by `t \ {j, k}`
  have : k in t.erase j := mem_erase.2 ⟨ne_of_apply_ne _ hjk.symm, hk⟩
  let u := (t.erase j).erase k
  have hj : j ∉ u := by simp [u]
  have hk : k ∉ u := by simp [u]
  have ht :
      t = (u.cons k hk).cons j (me

Depends on / 依赖: classical
-/
lemma StrictConvexOn.map_sum_lt (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) (hp : exists j in t, exists k in t, p j != p k) :
    f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) := by
  classical
  obtain ⟨j, hj, k, hk, hjk⟩ := hp
  -- We replace `t` by `t \ {j, k}`
  have : k in t.erase j := mem_erase.2 ⟨ne_of_apply_ne _ hjk.symm, hk⟩
  let u := (t.erase j).erase k
  have hj : j ∉ u := by simp [u]
  have hk : k ∉ u := by simp [u]
  have ht :
      t = (u.cons k hk).cons j (mem_cons.not.2 <| not_or_intro (ne_of_apply_ne _ hjk) hj) := by
    simp [u, insert_erase this, insert_erase ‹j in t›, *]
  clear_value u
  subst ht
  simp only [sum_cons]
have := h₀ j by simp
have := h₀ k by simp
  let c := w j + w k
  have hc : w j / c + w k / c = 1 := by simp [field, c]
  calc f (w j • p j + (w k • p k + ∑ x in u, w x • p x))
    _ = f (c • ((w j / c) • p j + (w k / c) • p k) + ∑ x in u, w x • p x) := by
      congrm f ?_
      match_scalars <;> simp [field, c]
    _ <= c • f ((w j / c) • p j + (w k / c) • p k) + ∑ x in u, w x • f (p x) :=
      -- apply the usual Jensen's inequality w.r.t. the weighted average of the two distinguished
      -- points and all the other points
        hf.convexOn.map_add_sum_le (fun i hi => (h₀ _ <| by simp [hi]).le)
          (by simpa [-cons_eq_insert, ← add_assoc] using h₁)
(forall_of_forall_cons <| forall_of_forall_cons hmem) (by positivity) by
           refine hf.1 (hmem _ <| by simp) (hmem _ <| by simp) ?_ ?_ hc <;> positivity
    _ < c • ((w j / c) • f (p j) + (w k / c) • f (p k)) + ∑ x in u, w x • f (p x) := by
      -- then apply the definition of strict convexity for the two distinguished points
      gcongr; refine hf.2 (hmem _ <| by simp) (hmem _ <| by simp) hjk ?_ ?_ hc <;> positivity
    _ = (w j • f (p j) + w k • f (p k)) + ∑ x in u, w x • f (p x) := by
      match_scalars <;> simp [field, c]
    _ = w j • f (p j) + (w k • f (p k) + ∑ x in u, w x • f (p x)) := by abel_nf

/--
lemma `StrictConcaveOn.lt_map_sum` / 引理 `StrictConcaveOn.lt_map_sum`

English:
lemma StrictConcaveOn.lt_map_sum
  statement: (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: hf.dual.map_sum_lt h₀ h₁ hmem hp

中文:
引理 StrictConcaveOn.lt_map_sum
  结论: (hf : StrictConcaveOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: hf.dual.map_sum_lt h₀ h₁ hmem hp

Depends on / 依赖: hf.dual.map_sum_lt, map_sum_lt
-/
lemma StrictConcaveOn.lt_map_sum (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) (hp : exists j in t, exists k in t, p j != p k) :
    ∑ i in t, w i • f (p i) < f (∑ i in t, w i • p i) := hf.dual.map_sum_lt h₀ h₁ hmem hp

/-! ### Equality case of Jensen's inequality -/

/--
lemma `StrictConvexOn.eq_of_le_map_sum` / 引理 `StrictConvexOn.eq_of_le_map_sum`

English:
lemma StrictConvexOn.eq_of_le_map_sum
  statement: (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: by
by_contra!; exact h_eq.not_gt hf.map_sum_lt h₀ h₁ hmem this

中文:
引理 StrictConvexOn.eq_of_le_map_sum
  结论: (hf : StrictConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: by
by_contra!; exact h_eq.not_gt hf.map_sum_lt h₀ h₁ hmem this

Depends on / 依赖: h_eq, h_eq.not_gt, hf.map_sum_lt, map_sum_lt, not_gt
-/
lemma StrictConvexOn.eq_of_le_map_sum (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s)
    (h_eq : ∑ i in t, w i • f (p i) <= f (∑ i in t, w i • p i)) :
    forall ⦃j⦄, j in t -> forall ⦃k⦄, k in t -> p j = p k := by
by_contra!; exact h_eq.not_gt hf.map_sum_lt h₀ h₁ hmem this

/--
lemma `StrictConcaveOn.eq_of_map_sum_eq` / 引理 `StrictConcaveOn.eq_of_map_sum_eq`

English:
lemma StrictConcaveOn.eq_of_map_sum_eq
  statement: (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: hf.dual.eq_of_le_map_sum h₀ h₁ hmem h_eq

中文:
引理 StrictConcaveOn.eq_of_map_sum_eq
  结论: (hf : StrictConcaveOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: hf.dual.eq_of_le_map_sum h₀ h₁ hmem h_eq

Depends on / 依赖: eq_of_le_map_sum, h_eq, hf.dual.eq_of_le_map_sum
-/
lemma StrictConcaveOn.eq_of_map_sum_eq (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s)
    (h_eq : f (∑ i in t, w i • p i) <= ∑ i in t, w i • f (p i)) :
    forall ⦃j⦄, j in t -> forall ⦃k⦄, k in t -> p j = p k :=
  hf.dual.eq_of_le_map_sum h₀ h₁ hmem h_eq

/--
theorem `StrictConvexOn.map_sum_eq_iff_of_pos` / 定理 `StrictConvexOn.map_sum_eq_iff_of_pos`

English:
theorem StrictConvexOn.map_sum_eq_iff_of_pos
  statement: (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: by
  refine ⟨fun h j hj k hk => hf.eq_of_le_map_sum h₀ h₁ hmem h.ge hj hk, fun h => ?_⟩
  rcases t.eq_empty_or_nonempty with (rfl | ⟨i, hi⟩)
  · simp at h₁
  · suffices f (∑ k in t, w k • p i) = ∑ k in t, w k • f (p i) by convert this using 3 <;> grind
    simp [← sum_smul, h₁]

中文:
定理 StrictConvexOn.map_sum_eq_iff_of_pos
  结论: (hf : StrictConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: by
  refine ⟨fun h j hj k hk => hf.eq_of_le_map_sum h₀ h₁ hmem h.ge hj hk, fun h => ?_⟩
  rcases t.eq_empty_or_nonempty with (rfl | ⟨i, hi⟩)
  · simp at h₁
  · suffices f (∑ k in t, w k • p i) = ∑ k in t, w k • f (p i) by convert this using 3 <;> grind
    simp [← sum_smul, h₁]

Depends on / 依赖: convert, eq_empty_or_nonempty, eq_of_le_map_sum, h.ge, hf.eq_of_le_map_sum, sum_smul, t.eq_empty_or_nonempty
-/
theorem StrictConvexOn.map_sum_eq_iff_of_pos (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall ⦃j⦄, j in t -> forall ⦃k⦄, k in t -> p j = p k := by
  refine ⟨fun h j hj k hk => hf.eq_of_le_map_sum h₀ h₁ hmem h.ge hj hk, fun h => ?_⟩
  rcases t.eq_empty_or_nonempty with (rfl | ⟨i, hi⟩)
  · simp at h₁
  · suffices f (∑ k in t, w k • p i) = ∑ k in t, w k • f (p i) by convert this using 3 <;> grind
    simp [← sum_smul, h₁]

/--
theorem `StrictConcaveOn.map_sum_eq_iff_of_pos` / 定理 `StrictConcaveOn.map_sum_eq_iff_of_pos`

English:
theorem StrictConcaveOn.map_sum_eq_iff_of_pos
  statement: (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: hf.dual.map_sum_eq_iff_of_pos h₀ h₁ hmem

中文:
定理 StrictConcaveOn.map_sum_eq_iff_of_pos
  结论: (hf : StrictConcaveOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: hf.dual.map_sum_eq_iff_of_pos h₀ h₁ hmem

Depends on / 依赖: hf.dual.map_sum_eq_iff_of_pos, map_sum_eq_iff_of_pos
-/
theorem StrictConcaveOn.map_sum_eq_iff_of_pos (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall ⦃j⦄, j in t -> forall ⦃k⦄, k in t -> p j = p k :=
  hf.dual.map_sum_eq_iff_of_pos h₀ h₁ hmem

/--
theorem `StrictConvexOn.map_sum_eq_iff_of_nonneg` / 定理 `StrictConvexOn.map_sum_eq_iff_of_nonneg`

English:
theorem StrictConvexOn.map_sum_eq_iff_of_nonneg
  statement: (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
  proof: by
  have :
      f (∑ i in t with w i != 0, w i • p i) = ∑ i in t with w i != 0, w i • f (p i) ↔
        forall ⦃j : ι⦄, j in {x in t | w x != 0} -> forall ⦃k : ι⦄, k in {x in t | w x != 0} -> p j = p k :=
    hf.map_sum_eq_iff_of_pos (by grind)
      (sum_filter_ne_zero _ |>.trans h₁) (hmem _ <| m

中文:
定理 StrictConvexOn.map_sum_eq_iff_of_nonneg
  结论: (hf : StrictConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i)
  证明: by
  have :
      f (∑ i in t with w i != 0, w i • p i) = ∑ i in t with w i != 0, w i • f (p i) ↔
        forall ⦃j : ι⦄, j in {x in t | w x != 0} -> forall ⦃k : ι⦄, k in {x in t | w x != 0} -> p j = p k :=
    hf.map_sum_eq_iff_of_pos (by grind)
      (sum_filter_ne_zero _ |>.trans h₁) (hmem _ <| m

Depends on / 依赖: hf.map_sum_eq_iff_of_pos, left_ne_zero_of_smul, map_sum_eq_iff_of_pos, mem_of_mem_filter, sum_filter_ne_zero, sum_filter_of_ne
-/
theorem StrictConvexOn.map_sum_eq_iff_of_nonneg (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔
      forall ⦃j⦄, j in t -> w j != 0 -> forall ⦃k⦄, k in t -> w k != 0 -> p j = p k := by
  have :
      f (∑ i in t with w i != 0, w i • p i) = ∑ i in t with w i != 0, w i • f (p i) ↔
        forall ⦃j : ι⦄, j in {x in t | w x != 0} -> forall ⦃k : ι⦄, k in {x in t | w x != 0} -> p j = p k :=
    hf.map_sum_eq_iff_of_pos (by grind)
      (sum_filter_ne_zero _ |>.trans h₁) (hmem _ <| mem_of_mem_filter · ·)
  grind [sum_filter_of_ne, left_ne_zero_of_smul]

/--
theorem `StrictConcaveOn.map_sum_eq_iff_of_nonneg` / 定理 `StrictConcaveOn.map_sum_eq_iff_of_nonneg`

English:
theorem StrictConcaveOn.map_sum_eq_iff_of_nonneg
  statement: (hf : StrictConcaveOn 𝕜 s f)
  proof: hf.dual.map_sum_eq_iff_of_nonneg h₀ h₁ hmem

中文:
定理 StrictConcaveOn.map_sum_eq_iff_of_nonneg
  结论: (hf : StrictConcaveOn 𝕜 s f)
  证明: hf.dual.map_sum_eq_iff_of_nonneg h₀ h₁ hmem

Depends on / 依赖: hf.dual.map_sum_eq_iff_of_nonneg, map_sum_eq_iff_of_nonneg
-/
theorem StrictConcaveOn.map_sum_eq_iff_of_nonneg (hf : StrictConcaveOn 𝕜 s f)
    (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔
      forall ⦃j⦄, j in t -> w j != 0 -> forall ⦃k⦄, k in t -> w k != 0 -> p j = p k :=
  hf.dual.map_sum_eq_iff_of_nonneg h₀ h₁ hmem

/--
theorem `StrictConvexOn.map_sum_lt_iff_of_pos` / 定理 `StrictConvexOn.map_sum_lt_iff_of_pos`

English:
theorem StrictConvexOn.map_sum_lt_iff_of_pos
  statement: (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: by
  refine ⟨fun h => ?_, hf.map_sum_lt h₀ h₁ hmem⟩
  contrapose! h
.not_lt .mpr h exact hf.map_sum_eq_iff_of_pos h₀ h₁ hmem

中文:
定理 StrictConvexOn.map_sum_lt_iff_of_pos
  结论: (hf : StrictConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: by
  refine ⟨fun h => ?_, hf.map_sum_lt h₀ h₁ hmem⟩
  contrapose! h
.not_lt .mpr h exact hf.map_sum_eq_iff_of_pos h₀ h₁ hmem

Depends on / 依赖: contrapose, hf.map_sum_eq_iff_of_pos, hf.map_sum_lt, map_sum_eq_iff_of_pos, map_sum_lt, not_lt
-/
theorem StrictConvexOn.map_sum_lt_iff_of_pos (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) ↔ exists j in t, exists k in t, p j != p k := by
  refine ⟨fun h => ?_, hf.map_sum_lt h₀ h₁ hmem⟩
  contrapose! h
.not_lt .mpr h exact hf.map_sum_eq_iff_of_pos h₀ h₁ hmem

/--
theorem `StrictConcaveOn.lt_map_sum_iff_of_pos` / 定理 `StrictConcaveOn.lt_map_sum_iff_of_pos`

English:
theorem StrictConcaveOn.lt_map_sum_iff_of_pos
  statement: (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: hf.dual.map_sum_lt_iff_of_pos h₀ h₁ hmem

中文:
定理 StrictConcaveOn.lt_map_sum_iff_of_pos
  结论: (hf : StrictConcaveOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: hf.dual.map_sum_lt_iff_of_pos h₀ h₁ hmem

Depends on / 依赖: hf.dual.map_sum_lt_iff_of_pos, map_sum_lt_iff_of_pos
-/
theorem StrictConcaveOn.lt_map_sum_iff_of_pos (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    ∑ i in t, w i • f (p i) < f (∑ i in t, w i • p i) ↔ exists j in t, exists k in t, p j != p k :=
  hf.dual.map_sum_lt_iff_of_pos h₀ h₁ hmem

/--
theorem `StrictConvexOn.map_sum_lt_iff_of_nonneg` / 定理 `StrictConvexOn.map_sum_lt_iff_of_nonneg`

English:
theorem StrictConvexOn.map_sum_lt_iff_of_nonneg
  statement: (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
  proof: by
  grind [hf.convexOn.map_sum_le h₀ h₁ hmem |>.not_lt_iff_eq, hf.map_sum_eq_iff_of_nonneg h₀ h₁ hmem]

中文:
定理 StrictConvexOn.map_sum_lt_iff_of_nonneg
  结论: (hf : StrictConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i)
  证明: by
  grind [hf.convexOn.map_sum_le h₀ h₁ hmem |>.not_lt_iff_eq, hf.map_sum_eq_iff_of_nonneg h₀ h₁ hmem]

Depends on / 依赖: convexOn, hf.convexOn.map_sum_le, hf.map_sum_eq_iff_of_nonneg, map_sum_eq_iff_of_nonneg, map_sum_le, not_lt_iff_eq
-/
theorem StrictConvexOn.map_sum_lt_iff_of_nonneg (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) ↔
      exists j in t, exists k in t, w j != 0 ∧ w k != 0 ∧ p j != p k := by
  grind [hf.convexOn.map_sum_le h₀ h₁ hmem |>.not_lt_iff_eq, hf.map_sum_eq_iff_of_nonneg h₀ h₁ hmem]

/--
theorem `StrictConcaveOn.lt_map_sum_iff_of_nonneg` / 定理 `StrictConcaveOn.lt_map_sum_iff_of_nonneg`

English:
theorem StrictConcaveOn.lt_map_sum_iff_of_nonneg
  statement: (hf : StrictConcaveOn 𝕜 s f)
  proof: hf.dual.map_sum_lt_iff_of_nonneg h₀ h₁ hmem

中文:
定理 StrictConcaveOn.lt_map_sum_iff_of_nonneg
  结论: (hf : StrictConcaveOn 𝕜 s f)
  证明: hf.dual.map_sum_lt_iff_of_nonneg h₀ h₁ hmem

Depends on / 依赖: hf.dual.map_sum_lt_iff_of_nonneg, map_sum_lt_iff_of_nonneg
-/
theorem StrictConcaveOn.lt_map_sum_iff_of_nonneg (hf : StrictConcaveOn 𝕜 s f)
    (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    ∑ i in t, w i • f (p i) < f (∑ i in t, w i • p i) ↔
      exists j in t, exists k in t, w j != 0 ∧ w k != 0 ∧ p j != p k :=
  hf.dual.map_sum_lt_iff_of_nonneg h₀ h₁ hmem

/--
lemma `StrictConvexOn.map_sum_eq_iff` / 引理 `StrictConvexOn.map_sum_eq_iff`

English:
lemma StrictConvexOn.map_sum_eq_iff
  statement: {w : ι -> 𝕜} {p : ι -> E} (hf : StrictConvexOn 𝕜 s f)
  proof: by
  refine ⟨?_, fun h => ?_⟩
  · obtain rfl | ⟨i₀, hi₀⟩ := t.eq_empty_or_nonempty
    · simp
    intro h_eq i hi
    have H (j) (hj : j in t) : p j = p i₀ := hf.eq_of_le_map_sum h₀ h₁ hmem h_eq.ge hj hi₀
    calc p i = p i₀ := by rw [H _ hi]
      _ = (1 : 𝕜) • p i₀ := by simp
      _ = (∑ j in t, 

中文:
引理 StrictConvexOn.map_sum_eq_iff
  结论: {w : ι -> 𝕜} {p : ι -> E} (hf : StrictConvexOn 𝕜 s f)
  证明: by
  refine ⟨?_, fun h => ?_⟩
  · obtain rfl | ⟨i₀, hi₀⟩ := t.eq_empty_or_nonempty
    · simp
    intro h_eq i hi
    have H (j) (hj : j in t) : p j = p i₀ := hf.eq_of_le_map_sum h₀ h₁ hmem h_eq.ge hj hi₀
    calc p i = p i₀ := by rw [H _ hi]
      _ = (1 : 𝕜) • p i₀ := by simp
      _ = (∑ j in t, 

Depends on / 依赖: eq_empty_or_nonempty, eq_of_le_map_sum, h_eq, h_eq.ge, hf.eq_of_le_map_sum, hf.map_sum_eq_iff_of_pos, map_sum_eq_iff_of_pos, sum_smul, t.eq_empty_or_nonempty
-/
lemma StrictConvexOn.map_sum_eq_iff {w : ι -> 𝕜} {p : ι -> E} (hf : StrictConvexOn 𝕜 s f)
    (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall j in t, p j = ∑ i in t, w i • p i := by
  refine ⟨?_, fun h => ?_⟩
  · obtain rfl | ⟨i₀, hi₀⟩ := t.eq_empty_or_nonempty
    · simp
    intro h_eq i hi
    have H (j) (hj : j in t) : p j = p i₀ := hf.eq_of_le_map_sum h₀ h₁ hmem h_eq.ge hj hi₀
    calc p i = p i₀ := by rw [H _ hi]
      _ = (1 : 𝕜) • p i₀ := by simp
      _ = (∑ j in t, w j) • p i₀ := by rw [h₁]
      _ = ∑ j in t, (w j • p i₀) := by rw [sum_smul]
      _ = ∑ j in t, (w j • p j) := by congr! 2 with j hj; rw [← H _ hj]
  · grind [hf.map_sum_eq_iff_of_pos h₀ h₁ hmem]

/--
lemma `StrictConcaveOn.map_sum_eq_iff` / 引理 `StrictConcaveOn.map_sum_eq_iff`

English:
lemma StrictConcaveOn.map_sum_eq_iff
  statement: (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: hf.dual.map_sum_eq_iff h₀ h₁ hmem

中文:
引理 StrictConcaveOn.map_sum_eq_iff
  结论: (hf : StrictConcaveOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: hf.dual.map_sum_eq_iff h₀ h₁ hmem

Depends on / 依赖: hf.dual.map_sum_eq_iff, map_sum_eq_iff
-/
lemma StrictConcaveOn.map_sum_eq_iff (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall j in t, p j = ∑ i in t, w i • p i :=
  hf.dual.map_sum_eq_iff h₀ h₁ hmem

/--
lemma `StrictConvexOn.map_sum_eq_iff'` / 引理 `StrictConvexOn.map_sum_eq_iff'`

English:
lemma StrictConvexOn.map_sum_eq_iff'
  statement: (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
  proof: by
  have hw (i) (_ : i in t) : w i • p i != 0 -> w i != 0 := by simp_all
  have hw' (i) (_ : i in t) : w i • f (p i) != 0 -> w i != 0 := by simp_all
  rw [← sum_filter_of_ne hw]; rw [← sum_filter_of_ne hw']; rw [hf.map_sum_eq_iff]
  · simp
  · simp +contextual [(h₀ _ _).lt_iff_ne']
  · rwa [sum_fil

中文:
引理 StrictConvexOn.map_sum_eq_iff'
  结论: (hf : StrictConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i)
  证明: by
  have hw (i) (_ : i in t) : w i • p i != 0 -> w i != 0 := by simp_all
  have hw' (i) (_ : i in t) : w i • f (p i) != 0 -> w i != 0 := by simp_all
  rw [← sum_filter_of_ne hw]; rw [← sum_filter_of_ne hw']; rw [hf.map_sum_eq_iff]
  · simp
  · simp +contextual [(h₀ _ _).lt_iff_ne']
  · rwa [sum_fil

Depends on / 依赖: contextual, hf.map_sum_eq_iff, lt_iff_ne, map_sum_eq_iff, sum_filter_ne_zero, sum_filter_of_ne
-/
lemma StrictConvexOn.map_sum_eq_iff' (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔
      forall j in t, w j != 0 -> p j = ∑ i in t, w i • p i := by
  have hw (i) (_ : i in t) : w i • p i != 0 -> w i != 0 := by simp_all
  have hw' (i) (_ : i in t) : w i • f (p i) != 0 -> w i != 0 := by simp_all
  rw [← sum_filter_of_ne hw]; rw [← sum_filter_of_ne hw']; rw [hf.map_sum_eq_iff]
  · simp
  · simp +contextual [(h₀ _ _).lt_iff_ne']
  · rwa [sum_filter_ne_zero]
  · simp +contextual [hmem _ _]

/--
lemma `StrictConcaveOn.map_sum_eq_iff'` / 引理 `StrictConcaveOn.map_sum_eq_iff'`

English:
lemma StrictConcaveOn.map_sum_eq_iff'
  statement: (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
  proof: hf.dual.map_sum_eq_iff' h₀ h₁ hmem

中文:
引理 StrictConcaveOn.map_sum_eq_iff'
  结论: (hf : StrictConcaveOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i)
  证明: hf.dual.map_sum_eq_iff' h₀ h₁ hmem

Depends on / 依赖: hf.dual.map_sum_eq_iff, map_sum_eq_iff
-/
lemma StrictConcaveOn.map_sum_eq_iff' (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔
      forall j in t, w j != 0 -> p j = ∑ i in t, w i • p i := hf.dual.map_sum_eq_iff' h₀ h₁ hmem

/--
theorem `StrictConvexOn.map_sum_lt_iff_of_pos'` / 定理 `StrictConvexOn.map_sum_lt_iff_of_pos'`

English:
theorem StrictConvexOn.map_sum_lt_iff_of_pos'
  statement: (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: by
.lt_iff_ne.trans apply hf.convexOn.map_sum_le (h₀ · · |>.le) h₁ hmem
  contrapose!
  exact hf.map_sum_eq_iff h₀ h₁ hmem

中文:
定理 StrictConvexOn.map_sum_lt_iff_of_pos'
  结论: (hf : StrictConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: by
.lt_iff_ne.trans apply hf.convexOn.map_sum_le (h₀ · · |>.le) h₁ hmem
  contrapose!
  exact hf.map_sum_eq_iff h₀ h₁ hmem

Depends on / 依赖: contrapose, convexOn, hf.convexOn.map_sum_le, hf.map_sum_eq_iff, lt_iff_ne, lt_iff_ne.trans, map_sum_eq_iff, map_sum_le
-/
theorem StrictConvexOn.map_sum_lt_iff_of_pos' (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) ↔ exists j in t, p j != ∑ i in t, w i • p i := by
.lt_iff_ne.trans apply hf.convexOn.map_sum_le (h₀ · · |>.le) h₁ hmem
  contrapose!
  exact hf.map_sum_eq_iff h₀ h₁ hmem

/--
theorem `StrictConcaveOn.lt_map_sum_iff_of_pos'` / 定理 `StrictConcaveOn.lt_map_sum_iff_of_pos'`

English:
theorem StrictConcaveOn.lt_map_sum_iff_of_pos'
  statement: (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
  proof: hf.dual.map_sum_lt_iff_of_pos' h₀ h₁ hmem

中文:
定理 StrictConcaveOn.lt_map_sum_iff_of_pos'
  结论: (hf : StrictConcaveOn 𝕜 s f) (h₀ : 对任意 i in t, 0 < w i)
  证明: hf.dual.map_sum_lt_iff_of_pos' h₀ h₁ hmem

Depends on / 依赖: hf.dual.map_sum_lt_iff_of_pos, map_sum_lt_iff_of_pos
-/
theorem StrictConcaveOn.lt_map_sum_iff_of_pos' (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    ∑ i in t, w i • f (p i) < f (∑ i in t, w i • p i) ↔ exists j in t, p j != ∑ i in t, w i • p i :=
  hf.dual.map_sum_lt_iff_of_pos' h₀ h₁ hmem

/--
theorem `StrictConvexOn.map_sum_lt_iff_of_nonneg'` / 定理 `StrictConvexOn.map_sum_lt_iff_of_nonneg'`

English:
theorem StrictConvexOn.map_sum_lt_iff_of_nonneg'
  statement: (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
  proof: by
  have :
      f (∑ i in t with w i != 0, w i • p i) < ∑ i in t with w i != 0, w i • f (p i) ↔
        exists j in {x in t | w x != 0}, p j != ∑ i in t with w i != 0, w i • p i :=
    hf.map_sum_lt_iff_of_pos' (by grind)
      (sum_filter_ne_zero _ |>.trans h₁) (hmem _ <| mem_of_mem_filter · ·)
 

中文:
定理 StrictConvexOn.map_sum_lt_iff_of_nonneg'
  结论: (hf : StrictConvexOn 𝕜 s f) (h₀ : 对任意 i in t, 0 <= w i)
  证明: by
  have :
      f (∑ i in t with w i != 0, w i • p i) < ∑ i in t with w i != 0, w i • f (p i) ↔
        exists j in {x in t | w x != 0}, p j != ∑ i in t with w i != 0, w i • p i :=
    hf.map_sum_lt_iff_of_pos' (by grind)
      (sum_filter_ne_zero _ |>.trans h₁) (hmem _ <| mem_of_mem_filter · ·)
 

Depends on / 依赖: hf.map_sum_lt_iff_of_pos, left_ne_zero_of_smul, map_sum_lt_iff_of_pos, mem_of_mem_filter, sum_filter_ne_zero, sum_filter_of_ne
-/
theorem StrictConvexOn.map_sum_lt_iff_of_nonneg' (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) ↔
      exists j in t, w j != 0 ∧ p j != ∑ i in t, w i • p i := by
  have :
      f (∑ i in t with w i != 0, w i • p i) < ∑ i in t with w i != 0, w i • f (p i) ↔
        exists j in {x in t | w x != 0}, p j != ∑ i in t with w i != 0, w i • p i :=
    hf.map_sum_lt_iff_of_pos' (by grind)
      (sum_filter_ne_zero _ |>.trans h₁) (hmem _ <| mem_of_mem_filter · ·)
  grind [sum_filter_of_ne, left_ne_zero_of_smul]

/--
theorem `StrictConcaveOn.lt_map_sum_iff_of_nonneg'` / 定理 `StrictConcaveOn.lt_map_sum_iff_of_nonneg'`

English:
theorem StrictConcaveOn.lt_map_sum_iff_of_nonneg'
  statement: (hf : StrictConcaveOn 𝕜 s f)
  proof: hf.dual.map_sum_lt_iff_of_nonneg' h₀ h₁ hmem

中文:
定理 StrictConcaveOn.lt_map_sum_iff_of_nonneg'
  结论: (hf : StrictConcaveOn 𝕜 s f)
  证明: hf.dual.map_sum_lt_iff_of_nonneg' h₀ h₁ hmem

Depends on / 依赖: hf.dual.map_sum_lt_iff_of_nonneg, map_sum_lt_iff_of_nonneg
-/
theorem StrictConcaveOn.lt_map_sum_iff_of_nonneg' (hf : StrictConcaveOn 𝕜 s f)
    (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
    ∑ i in t, w i • f (p i) < f (∑ i in t, w i • p i) ↔ exists j in t, w j != 0 ∧ p j != ∑ i in t, w i • p i :=
  hf.dual.map_sum_lt_iff_of_nonneg' h₀ h₁ hmem

end Jensen

/-! ### Maximum principle -/


section MaximumPrinciple

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module 𝕜 E]
  [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β] {s : Set E} {f : E -> β} {w : ι -> 𝕜} {p : ι -> E}
  {x y z : E}

/--
theorem `ConvexOn.le_sup_of_mem_convexHull` / 定理 `ConvexOn.le_sup_of_mem_convexHull`

English:
theorem ConvexOn.le_sup_of_mem_convexHull
  statement: {t : Finset E} (hf : ConvexOn 𝕜 s f) (hts : ↑t subseteq s)
  proof: by
  obtain ⟨w, hw₀, hw₁, rfl⟩ := mem_convexHull.1 hx
  exact (hf.map_centerMass_le hw₀ (by positivity) hts).trans
    (centerMass_le_sup hw₀ <| by positivity)

中文:
定理 ConvexOn.le_sup_of_mem_convexHull
  结论: {t : 有限集 E} (hf : ConvexOn 𝕜 s f) (hts : ↑t subseteq s)
  证明: by
  obtain ⟨w, hw₀, hw₁, rfl⟩ := mem_convexHull.1 hx
  exact (hf.map_centerMass_le hw₀ (by positivity) hts).trans
    (centerMass_le_sup hw₀ <| by positivity)

Depends on / 依赖: centerMass_le_sup, hf.map_centerMass_le, map_centerMass_le, mem_convexHull
-/
theorem ConvexOn.le_sup_of_mem_convexHull {t : Finset E} (hf : ConvexOn 𝕜 s f) (hts : ↑t subseteq s)
    (hx : x in convexHull 𝕜 (t : Set E)) :
    f x <= t.sup' (coe_nonempty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f := by
  obtain ⟨w, hw₀, hw₁, rfl⟩ := mem_convexHull.1 hx
  exact (hf.map_centerMass_le hw₀ (by positivity) hts).trans
    (centerMass_le_sup hw₀ <| by positivity)

/--
theorem `ConvexOn.inf_le_of_mem_convexHull` / 定理 `ConvexOn.inf_le_of_mem_convexHull`

English:
theorem ConvexOn.inf_le_of_mem_convexHull
  statement: {t : Finset E} (hf : ConcaveOn 𝕜 s f) (hts : ↑t subseteq s)
  proof: hf.dual.le_sup_of_mem_convexHull hts hx

中文:
定理 ConvexOn.inf_le_of_mem_convexHull
  结论: {t : 有限集 E} (hf : ConcaveOn 𝕜 s f) (hts : ↑t subseteq s)
  证明: hf.dual.le_sup_of_mem_convexHull hts hx

Depends on / 依赖: hf.dual.le_sup_of_mem_convexHull, le_sup_of_mem_convexHull
-/
theorem ConvexOn.inf_le_of_mem_convexHull {t : Finset E} (hf : ConcaveOn 𝕜 s f) (hts : ↑t subseteq s)
    (hx : x in convexHull 𝕜 (t : Set E)) :
    t.inf' (coe_nonempty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f <= f x :=
  hf.dual.le_sup_of_mem_convexHull hts hx

/--
lemma `ConvexOn.exists_ge_of_centerMass` / 引理 `ConvexOn.exists_ge_of_centerMass`

English:
lemma ConvexOn.exists_ge_of_centerMass
  statement: {t : Finset ι} (h : ConvexOn 𝕜 s f)
  proof: by
  set y := t.centerMass w p
  -- TODO: can `rsuffices` be used to write the `exact` first, then the proof of this obtain?
  obtain ⟨i, hi, hfi⟩ : exists i in {i in t | w i != 0}, w i • f y <= w i • (f ∘ p) i := by
    have hw' : (0 : 𝕜) < ∑ i in t with w i != 0, w i := by rwa [sum_filter_ne_zero]

中文:
引理 ConvexOn.存在_ge_of_centerMass
  结论: {t : 有限集 ι} (h : ConvexOn 𝕜 s f)
  证明: by
  set y := t.centerMass w p
  -- TODO: can `rsuffices` be used to write the `exact` first, then the proof of this obtain?
  obtain ⟨i, hi, hfi⟩ : exists i in {i in t | w i != 0}, w i • f y <= w i • (f ∘ p) i := by
    have hw' : (0 : 𝕜) < ∑ i in t with w i != 0, w i := by rwa [sum_filter_ne_zero]

Depends on / 依赖: centerMass, t.centerMass
-/
lemma ConvexOn.exists_ge_of_centerMass {t : Finset ι} (h : ConvexOn 𝕜 s f)
    (hw₀ : forall i in t, 0 <= w i) (hw₁ : 0 < ∑ i in t, w i) (hp : forall i in t, p i in s) :
    exists i in t, f (t.centerMass w p) <= f (p i) := by
  set y := t.centerMass w p
  -- TODO: can `rsuffices` be used to write the `exact` first, then the proof of this obtain?
  obtain ⟨i, hi, hfi⟩ : exists i in {i in t | w i != 0}, w i • f y <= w i • (f ∘ p) i := by
    have hw' : (0 : 𝕜) < ∑ i in t with w i != 0, w i := by rwa [sum_filter_ne_zero]
    refine exists_le_of_sum_le (nonempty_of_sum_ne_zero hw'.ne') ?_
    rw [← sum_smul]; rw [← smul_le_smul_iff_of_pos_left (inv_pos.2 hw')]; rw [inv_smul_smul₀ hw'.ne']; rw [←
      centerMass]; rw [centerMass_filter_ne_zero]
    exact h.map_centerMass_le hw₀ hw₁ hp
  rw [mem_filter] at hi
  exact ⟨i, hi.1, (smul_le_smul_iff_of_pos_left <| (hw₀ i hi.1).lt_of_ne hi.2.symm).1 hfi⟩

/--
lemma `ConcaveOn.exists_le_of_centerMass` / 引理 `ConcaveOn.exists_le_of_centerMass`

English:
lemma ConcaveOn.exists_le_of_centerMass
  statement: {t : Finset ι} (h : ConcaveOn 𝕜 s f)
  proof: h.dual.exists_ge_of_centerMass hw₀ hw₁ hp

中文:
引理 ConcaveOn.存在_le_of_centerMass
  结论: {t : 有限集 ι} (h : ConcaveOn 𝕜 s f)
  证明: h.dual.exists_ge_of_centerMass hw₀ hw₁ hp

Depends on / 依赖: exists_ge_of_centerMass, h.dual.exists_ge_of_centerMass
-/
lemma ConcaveOn.exists_le_of_centerMass {t : Finset ι} (h : ConcaveOn 𝕜 s f)
    (hw₀ : forall i in t, 0 <= w i) (hw₁ : 0 < ∑ i in t, w i) (hp : forall i in t, p i in s) :
    exists i in t, f (p i) <= f (t.centerMass w p) := h.dual.exists_ge_of_centerMass hw₀ hw₁ hp

/--
lemma `ConvexOn.exists_ge_of_mem_convexHull` / 引理 `ConvexOn.exists_ge_of_mem_convexHull`

English:
lemma ConvexOn.exists_ge_of_mem_convexHull
  statement: {t : Set E} (hf : ConvexOn 𝕜 s f) (hts : t subseteq s)
  proof: by
  rw [_root_.convexHull_eq] at hx
  obtain ⟨α, t, w, p, hw₀, hw₁, hp, rfl⟩ := hx
  obtain ⟨i, hit, Hi⟩ := hf.exists_ge_of_centerMass hw₀ (hw₁.symm ▸ zero_lt_one)
    fun i hi => hts (hp i hi)
  exact ⟨p i, hp i hit, Hi⟩

中文:
引理 ConvexOn.存在_ge_of_mem_convexHull
  结论: {t : 集合 E} (hf : ConvexOn 𝕜 s f) (hts : t subseteq s)
  证明: by
  rw [_root_.convexHull_eq] at hx
  obtain ⟨α, t, w, p, hw₀, hw₁, hp, rfl⟩ := hx
  obtain ⟨i, hit, Hi⟩ := hf.exists_ge_of_centerMass hw₀ (hw₁.symm ▸ zero_lt_one)
    fun i hi => hts (hp i hi)
  exact ⟨p i, hp i hit, Hi⟩

Depends on / 依赖: _root_, _root_.convexHull_eq, convexHull_eq, exists_ge_of_centerMass, hf.exists_ge_of_centerMass, zero_lt_one
-/
lemma ConvexOn.exists_ge_of_mem_convexHull {t : Set E} (hf : ConvexOn 𝕜 s f) (hts : t subseteq s)
    (hx : x in convexHull 𝕜 t) : exists y in t, f x <= f y := by
  rw [_root_.convexHull_eq] at hx
  obtain ⟨α, t, w, p, hw₀, hw₁, hp, rfl⟩ := hx
  obtain ⟨i, hit, Hi⟩ := hf.exists_ge_of_centerMass hw₀ (hw₁.symm ▸ zero_lt_one)
    fun i hi => hts (hp i hi)
  exact ⟨p i, hp i hit, Hi⟩

/--
lemma `ConcaveOn.exists_le_of_mem_convexHull` / 引理 `ConcaveOn.exists_le_of_mem_convexHull`

English:
lemma ConcaveOn.exists_le_of_mem_convexHull
  statement: {t : Set E} (hf : ConcaveOn 𝕜 s f) (hts : t subseteq s)
  proof: hf.dual.exists_ge_of_mem_convexHull hts hx

中文:
引理 ConcaveOn.存在_le_of_mem_convexHull
  结论: {t : 集合 E} (hf : ConcaveOn 𝕜 s f) (hts : t subseteq s)
  证明: hf.dual.exists_ge_of_mem_convexHull hts hx

Depends on / 依赖: exists_ge_of_mem_convexHull, hf.dual.exists_ge_of_mem_convexHull
-/
lemma ConcaveOn.exists_le_of_mem_convexHull {t : Set E} (hf : ConcaveOn 𝕜 s f) (hts : t subseteq s)
    (hx : x in convexHull 𝕜 t) : exists y in t, f y <= f x := hf.dual.exists_ge_of_mem_convexHull hts hx

/--
lemma `ConvexOn.le_max_of_mem_segment` / 引理 `ConvexOn.le_max_of_mem_segment`

English:
lemma ConvexOn.le_max_of_mem_segment
  statement: (hf : ConvexOn 𝕜 s f) (hx : x in s) (hy : y in s)
  proof: by
  rw [← convexHull_pair] at hz; simpa using hf.exists_ge_of_mem_convexHull (pair_subset hx hy) hz

中文:
引理 ConvexOn.le_max_of_mem_segment
  结论: (hf : ConvexOn 𝕜 s f) (hx : x in s) (hy : y in s)
  证明: by
  rw [← convexHull_pair] at hz; simpa using hf.exists_ge_of_mem_convexHull (pair_subset hx hy) hz

Depends on / 依赖: convexHull_pair, exists_ge_of_mem_convexHull, hf.exists_ge_of_mem_convexHull, pair_subset
-/
lemma ConvexOn.le_max_of_mem_segment (hf : ConvexOn 𝕜 s f) (hx : x in s) (hy : y in s)
    (hz : z in [x -[𝕜] y]) : f z <= max (f x) (f y) := by
  rw [← convexHull_pair] at hz; simpa using hf.exists_ge_of_mem_convexHull (pair_subset hx hy) hz

/--
lemma `ConcaveOn.min_le_of_mem_segment` / 引理 `ConcaveOn.min_le_of_mem_segment`

English:
lemma ConcaveOn.min_le_of_mem_segment
  statement: (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hy : y in s)
  proof: hf.dual.le_max_of_mem_segment hx hy hz

中文:
引理 ConcaveOn.min_le_of_mem_segment
  结论: (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hy : y in s)
  证明: hf.dual.le_max_of_mem_segment hx hy hz

Depends on / 依赖: hf.dual.le_max_of_mem_segment, le_max_of_mem_segment
-/
lemma ConcaveOn.min_le_of_mem_segment (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hy : y in s)
    (hz : z in [x -[𝕜] y]) : min (f x) (f y) <= f z := hf.dual.le_max_of_mem_segment hx hy hz

/--
lemma `ConvexOn.le_max_of_mem_Icc` / 引理 `ConvexOn.le_max_of_mem_Icc`

English:
lemma ConvexOn.le_max_of_mem_Icc
  statement: {s : Set 𝕜} {f : 𝕜 -> β} {x y z : 𝕜} (hf : ConvexOn 𝕜 s f)
  proof: by
  rw [← segment_eq_Icc (hz.1.trans hz.2)] at hz; exact hf.le_max_of_mem_segment hx hy hz

中文:
引理 ConvexOn.le_max_of_mem_Icc
  结论: {s : 集合 𝕜} {f : 𝕜 -> β} {x y z : 𝕜} (hf : ConvexOn 𝕜 s f)
  证明: by
  rw [← segment_eq_Icc (hz.1.trans hz.2)] at hz; exact hf.le_max_of_mem_segment hx hy hz

Depends on / 依赖: hf.le_max_of_mem_segment, le_max_of_mem_segment, segment_eq_Icc
-/
lemma ConvexOn.le_max_of_mem_Icc {s : Set 𝕜} {f : 𝕜 -> β} {x y z : 𝕜} (hf : ConvexOn 𝕜 s f)
    (hx : x in s) (hy : y in s) (hz : z in Icc x y) : f z <= max (f x) (f y) := by
  rw [← segment_eq_Icc (hz.1.trans hz.2)] at hz; exact hf.le_max_of_mem_segment hx hy hz

/--
lemma `ConcaveOn.min_le_of_mem_Icc` / 引理 `ConcaveOn.min_le_of_mem_Icc`

English:
lemma ConcaveOn.min_le_of_mem_Icc
  statement: {s : Set 𝕜} {f : 𝕜 -> β} {x y z : 𝕜} (hf : ConcaveOn 𝕜 s f)
  proof: hf.dual.le_max_of_mem_Icc hx hy hz

中文:
引理 ConcaveOn.min_le_of_mem_Icc
  结论: {s : 集合 𝕜} {f : 𝕜 -> β} {x y z : 𝕜} (hf : ConcaveOn 𝕜 s f)
  证明: hf.dual.le_max_of_mem_Icc hx hy hz

Depends on / 依赖: hf.dual.le_max_of_mem_Icc, le_max_of_mem_Icc
-/
lemma ConcaveOn.min_le_of_mem_Icc {s : Set 𝕜} {f : 𝕜 -> β} {x y z : 𝕜} (hf : ConcaveOn 𝕜 s f)
    (hx : x in s) (hy : y in s) (hz : z in Icc x y) : min (f x) (f y) <= f z :=
  hf.dual.le_max_of_mem_Icc hx hy hz

/--
lemma `ConvexOn.bddAbove_convexHull` / 引理 `ConvexOn.bddAbove_convexHull`

English:
lemma ConvexOn.bddAbove_convexHull
  given: {s t : Set E} (hst : s subseteq t) (hf : ConvexOn 𝕜 t f)
  proof: by
  rintro ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hf.exists_ge_of_mem_convexHull hst hx
exact hxy.trans hb mem_image_of_mem _ hy

中文:
引理 ConvexOn.bddAbove_convexHull
  条件: {s t : 集合 E} (hst : s subseteq t) (hf : ConvexOn 𝕜 t f)
  证明: by
  rintro ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hf.exists_ge_of_mem_convexHull hst hx
exact hxy.trans hb mem_image_of_mem _ hy

Depends on / 依赖: exists_ge_of_mem_convexHull, hf.exists_ge_of_mem_convexHull, hxy.trans, mem_image_of_mem
-/
lemma ConvexOn.bddAbove_convexHull {s t : Set E} (hst : s subseteq t) (hf : ConvexOn 𝕜 t f) :
    BddAbove (f '' s) -> BddAbove (f '' convexHull 𝕜 s) := by
  rintro ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hf.exists_ge_of_mem_convexHull hst hx
exact hxy.trans hb mem_image_of_mem _ hy

/--
lemma `ConcaveOn.bddBelow_convexHull` / 引理 `ConcaveOn.bddBelow_convexHull`

English:
lemma ConcaveOn.bddBelow_convexHull
  given: {s t : Set E} (hst : s subseteq t) (hf : ConcaveOn 𝕜 t f)
  proof: hf.dual.bddAbove_convexHull hst

中文:
引理 ConcaveOn.bddBelow_convexHull
  条件: {s t : 集合 E} (hst : s subseteq t) (hf : ConcaveOn 𝕜 t f)
  证明: hf.dual.bddAbove_convexHull hst

Depends on / 依赖: bddAbove_convexHull, hf.dual.bddAbove_convexHull
-/
lemma ConcaveOn.bddBelow_convexHull {s t : Set E} (hst : s subseteq t) (hf : ConcaveOn 𝕜 t f) :
    BddBelow (f '' s) -> BddBelow (f '' convexHull 𝕜 s) := hf.dual.bddAbove_convexHull hst

end MaximumPrinciple
