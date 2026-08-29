/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Ceva's theorem.

This file proves various versions of Ceva's theorem.

## References

* https://en.wikipedia.org/wiki/Ceva%27s_theorem

-/

public section


open scoped Affine

variable {k V P ι : Type*}

namespace AffineIndependent

variable [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_affineCombination_eq_smul_eq_aux` / 引理 `exists_affineCombination_eq_smul_eq_aux`

English:
lemma exists_affineCombination_eq_smul_eq_aux
  statement: {p : ι -> P} (hp : AffineIndependent k p)
  proof: by
  classical
  have hp'' : forall i : s, exists r : k, (fs i).affineCombination k p
      (AffineMap.lineMap (Pi.single (i : ι) 1) (w i) r) = p' := by
    intro i
    simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp'
    obtain ⟨r, rfl⟩ := hp' i
    exact ⟨r, by simp [hfs]⟩
  obtain ⟨i', 

中文:
引理 存在_affineCombination_eq_smul_eq_aux
  结论: {p : ι -> P} (hp : AffineIndependent k p)
  证明: by
  classical
  have hp'' : forall i : s, exists r : k, (fs i).affineCombination k p
      (AffineMap.lineMap (Pi.single (i : ι) 1) (w i) r) = p' := by
    intro i
    simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp'
    obtain ⟨r, rfl⟩ := hp' i
    exact ⟨r, by simp [hfs]⟩
  obtain ⟨i', 
-/
private lemma exists_affineCombination_eq_smul_eq_aux {p : ι -> P} (hp : AffineIndependent k p)
    {s : Set ι} (hs : s.Nonempty) {fs : s -> Finset ι} (hfs : forall i, (i : ι) in fs i) {w : s -> ι -> k}
    (hw : forall i, ∑ j in fs i, w i j = 1) {p' : P}
    (hp' : forall i : s, p' in line[k, p i, (fs i).affineCombination k p (w i)]) :
    exists (w' : ι -> k) (fs' : Finset ι), (∑ j in fs', w' j = 1) ∧ fs'.affineCombination k p w' = p' ∧
      forall i : s, exists r, forall j, r * Set.indicator ((fs i : Set ι) \ {(i : ι)}) (w i) j =
        Set.indicator ((fs' : Set ι) \ {(i : ι)}) w' j := by
  classical
  have hp'' : forall i : s, exists r : k, (fs i).affineCombination k p
      (AffineMap.lineMap (Pi.single (i : ι) 1) (w i) r) = p' := by
    intro i
    simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp'
    obtain ⟨r, rfl⟩ := hp' i
    exact ⟨r, by simp [hfs]⟩
  obtain ⟨i', hi'⟩ := hs
  obtain ⟨ri', hri'⟩ := hp'' ⟨i', hi'⟩
  let w' : ι -> k := AffineMap.lineMap (Pi.single i' 1) (w ⟨i', hi'⟩) ri'
  refine ⟨w', fs ⟨i', hi'⟩, ?_, ?_, ?_⟩
  · simp [w', AffineMap.lineMap_apply_module, Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]
  · simp [w', hri']
  · intro i
    obtain ⟨r, hr⟩ := hp'' i
    refine ⟨r, ?_⟩
    rw [← hri'] at hr
    simp only [AffineMap.lineMap_apply_module] at hr
    have hind := hp.indicator_eq_of_affineCombination_eq _ _ _ _ ?_ ?_ hr
    · intro j
      by_cases hj : j = i
      · simp [hj]
      replace hind := congr_fun hind j
      convert! hind using 1
      · simp [Set.indicator_apply, hj]
      · simp [Set.indicator_apply, hj, w', AffineMap.lineMap_apply_module]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]

/--
lemma `exists_affineCombination_eq_smul_eq` / 引理 `exists_affineCombination_eq_smul_eq`

English:
lemma exists_affineCombination_eq_smul_eq
  statement: {p : ι -> P} (hp : AffineIndependent k p) {s : Set ι}
  proof: by
  classical
  let fsx : s -> Finset ι := fun i => insert (i : ι) (fs i)
  have hfsx : forall i, (i : ι) in fsx i := by simp [fsx]
  let wx : s -> ι -> k := fun i => Set.indicator (fs i) (w i)
  have hwx : forall i, ∑ j in fsx i, wx i j = 1 := by
    intro i
    simp_rw [← hw i, fsx, wx]
    by_ca

中文:
引理 存在_affineCombination_eq_smul_eq
  结论: {p : ι -> P} (hp : AffineIndependent k p) {s : 集合 ι}
  证明: by
  classical
  let fsx : s -> Finset ι := fun i => insert (i : ι) (fs i)
  have hfsx : forall i, (i : ι) in fsx i := by simp [fsx]
  let wx : s -> ι -> k := fun i => Set.indicator (fs i) (w i)
  have hwx : forall i, ∑ j in fsx i, wx i j = 1 := by
    intro i
    simp_rw [← hw i, fsx, wx]
    by_ca

Depends on / 依赖: Finset, Finset.sum_congr, Set.indicator, affineCombination, classical, convert, indicator, insert, simp_rw, sum_congr
-/
lemma exists_affineCombination_eq_smul_eq {p : ι -> P} (hp : AffineIndependent k p) {s : Set ι}
    (hs : s.Nonempty) {fs : s -> Finset ι} {w : s -> ι -> k} (hw : forall i, ∑ j in fs i, w i j = 1) {p' : P}
    (hp' : forall i : s, p' in line[k, p i, (fs i).affineCombination k p (w i)]) :
    exists (w' : ι -> k) (fs' : Finset ι), (∑ j in fs', w' j = 1) ∧ fs'.affineCombination k p w' = p' ∧
      forall i : s, exists r, forall j, r * Set.indicator ((fs i : Set ι) \ {(i : ι)}) (w i) j =
        Set.indicator ((fs' : Set ι) \ {(i : ι)}) w' j := by
  classical
  let fsx : s -> Finset ι := fun i => insert (i : ι) (fs i)
  have hfsx : forall i, (i : ι) in fsx i := by simp [fsx]
  let wx : s -> ι -> k := fun i => Set.indicator (fs i) (w i)
  have hwx : forall i, ∑ j in fsx i, wx i j = 1 := by
    intro i
    simp_rw [← hw i, fsx, wx]
    by_cases hi : (i : ι) in fs i <;> simpa [hi] using Finset.sum_congr rfl (by aesop)
  have hp'x : forall i : s, p' in line[k, p i, (fsx i).affineCombination k p (wx i)] := by
    intro i
    convert! hp' i using 4
    simp_rw [fsx, wx]
    exact (Finset.affineCombination_indicator_subset _ _ (by simp)).symm
  obtain ⟨w', fs', h⟩ := hp.exists_affineCombination_eq_smul_eq_aux hs hfsx hwx hp'x
  refine ⟨w', fs', h.1, h.2.1, fun i => ?_⟩
  obtain ⟨r, hr⟩ := h.2.2 i
  refine ⟨r, fun j => ?_⟩
  convert! hr j using 2
  simp only [Set.indicator_apply, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff,
    Finset.coe_insert, Set.insert_sdiff_of_mem, fsx, wx]
  grind

/--
lemma `exists_affineCombination_eq_smul_eq_of_fintype` / 引理 `exists_affineCombination_eq_smul_eq_of_fintype`

English:
lemma exists_affineCombination_eq_smul_eq_of_fintype
  statement: [Fintype ι] {p : ι -> P}
  proof: by
  classical
  obtain ⟨w'', fs'', hw'', hw''p', hi⟩ := hp.exists_affineCombination_eq_smul_eq hs hw hp'
  refine ⟨Set.indicator fs'' w'', ?_, ?_, ?_⟩
  · rw [← hw'']
    exact Finset.sum_indicator_subset _ (by simp)
  · rw [← hw''p']
    exact (Finset.affineCombination_indicator_subset _ _ (by sim

中文:
引理 存在_affineCombination_eq_smul_eq_of_fintype
  结论: [有限类型 ι] {p : ι -> P}
  证明: by
  classical
  obtain ⟨w'', fs'', hw'', hw''p', hi⟩ := hp.exists_affineCombination_eq_smul_eq hs hw hp'
  refine ⟨Set.indicator fs'' w'', ?_, ?_, ?_⟩
  · rw [← hw'']
    exact Finset.sum_indicator_subset _ (by simp)
  · rw [← hw''p']
    exact (Finset.affineCombination_indicator_subset _ _ (by sim

Depends on / 依赖: Finset, Finset.affineCombination_indicator_subset, Finset.sum_indicator_subset, Set.indicator, Set.indicator_apply, affineCombination_indicator_subset, classical, convert, exists_affineCombination_eq_smul_eq, hp.exists_affineCombination_eq_smul_eq, indicator, indicator_apply, sum_indicator_subset
-/
lemma exists_affineCombination_eq_smul_eq_of_fintype [Fintype ι] {p : ι -> P}
    (hp : AffineIndependent k p) {s : Set ι} (hs : s.Nonempty) {w : s -> ι -> k}
    (hw : forall i, ∑ j, w i j = 1) {p' : P}
    (hp' : forall i : s, p' in line[k, p i, Finset.univ.affineCombination k p (w i)]) :
    exists w' : ι -> k, (∑ j, w' j = 1) ∧ Finset.univ.affineCombination k p w' = p' ∧
      forall i : s, exists r, forall j, r * Set.indicator {(i : ι)}ᶜ (w i) j =
        Set.indicator {(i : ι)}ᶜ w' j := by
  classical
  obtain ⟨w'', fs'', hw'', hw''p', hi⟩ := hp.exists_affineCombination_eq_smul_eq hs hw hp'
  refine ⟨Set.indicator fs'' w'', ?_, ?_, ?_⟩
  · rw [← hw'']
    exact Finset.sum_indicator_subset _ (by simp)
  · rw [← hw''p']
    exact (Finset.affineCombination_indicator_subset _ _ (by simp)).symm
  · intro i
    obtain ⟨r, hr⟩ := hi i
    refine ⟨r, fun j => ?_⟩
    convert! hr j using 1
    · simp [Set.indicator_apply]
    · by_cases hj : j = (i : ι) <;> simp [Set.indicator_apply, hj]

end AffineIndependent

namespace Affine.Triangle

section CommRing

variable [CommRing k] [NoZeroDivisors k] [AddCommGroup V] [Module k V] [AffineSpace V P]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `prod_eq_prod_one_sub_of_mem_line_point_lineMap` / 引理 `prod_eq_prod_one_sub_of_mem_line_point_lineMap`

English:
lemma prod_eq_prod_one_sub_of_mem_line_point_lineMap
  statement: {t : Triangle k P} {r : Fin 3 -> k} {p' : P}
  proof: by
  rcases subsingleton_or_nontrivial k
  · exact Subsingleton.elim _ _
  let w : ↑(Set.univ : Set (Fin 3)) -> Fin 3 -> k :=
    fun i => Finset.affineCombinationLineMapWeights (i + 1) (i + 2) (r i)
  have hw : forall i, ∑ j, w i j = 1 := by simp [w]
  have hp'w : forall i : ↑(Set.univ : Set (Fin 3

中文:
引理 prod_eq_prod_one_sub_of_mem_line_point_lineMap
  结论: {t : Triangle k P} {r : 有限集 3 -> k} {p' : P}
  证明: by
  rcases subsingleton_or_nontrivial k
  · exact Subsingleton.elim _ _
  let w : ↑(Set.univ : Set (Fin 3)) -> Fin 3 -> k :=
    fun i => Finset.affineCombinationLineMapWeights (i + 1) (i + 2) (r i)
  have hw : forall i, ∑ j, w i j = 1 := by simp [w]
  have hp'w : forall i : ↑(Set.univ : Set (Fin 3

Depends on / 依赖: Finset, Finset.affineCombinationLineMapWeights, Finset.univ.affineCombination, Set.univ, Subsingleton, Subsingleton.elim, affineCombination, affineCombinationLineMapWeights, exists_affineCombination_eq_smul_eq_of_fintype, independent, points, subsingleton_or_nontrivial, t.independent.exists_affineCombination_eq_smul_eq_of_fintype, t.points
-/
lemma prod_eq_prod_one_sub_of_mem_line_point_lineMap {t : Triangle k P} {r : Fin 3 -> k} {p' : P}
    (hp' : forall i : Fin 3, p' in
      line[k, t.points i, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i)]) :
    ∏ i, r i = ∏ i, (1 - r i) := by
  rcases subsingleton_or_nontrivial k
  · exact Subsingleton.elim _ _
  let w : ↑(Set.univ : Set (Fin 3)) -> Fin 3 -> k :=
    fun i => Finset.affineCombinationLineMapWeights (i + 1) (i + 2) (r i)
  have hw : forall i, ∑ j, w i j = 1 := by simp [w]
  have hp'w : forall i : ↑(Set.univ : Set (Fin 3)),
      p' in line[k, t.points i, Finset.univ.affineCombination k t.points (w i)] := by
    simpa [w] using hp'
  obtain ⟨w', hw', rfl, h⟩ :=
    t.independent.exists_affineCombination_eq_smul_eq_of_fintype (by simp) hw hp'w
  have h' : forall i : Fin 3, exists c : k, forall j != i, c * w ⟨i, by simp⟩ j = w' j := by
    intro i
    obtain ⟨c, hc⟩ := h ⟨i, by simp⟩
    refine ⟨c, fun j hj => ?_⟩
    simpa [hj] using hc j
  simp only [Fin.isValue, w] at h'
  let c : Fin 3 -> k := fun i => (h' i).choose
  have hc (i : Fin 3) : forall j : Fin 3, j != i ->
    c i * Finset.affineCombinationLineMapWeights (i + 1) (i + 2) (r i) j = w' j :=
      (h' i).choose_spec
  have hc1 (i : Fin 3) : c i * (1 - r i) = w' (i + 1) := by
    rw [← hc i (i + 1) (by simp)]
    simp
  have hc2 (i : Fin 3) : c i * r i = w' (i + 2) := by
    rw [← hc i (i + 2) (by simp)]
    simp
  have hcr : (∏ i, c i) * ∏ i, r i = (∏ i, c i) * ∏ i, (1 - r i) := by
    simp_rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun _ _ => hc1 _),
      Finset.prod_congr rfl (fun _ _ => hc2 _)]
    suffices ∏ i, (w' ∘ Equiv.addRight 2) i = ∏ i, (w' ∘ Equiv.addRight 1) i by
      simpa using this
    simp_rw [Finset.prod_comp_equiv]
    simp
  by_cases hc : ∏ i, c i = 0
  · rw [Finset.prod_eq_zero_iff] at hc
    obtain ⟨i, -, hi⟩ := hc
    have hw'i1 : w' (i + 1) = 0 := by simpa [hi] using (hc1 i).symm
    have hw'i2 : w' (i + 2) = 0 := by simpa [hi] using (hc2 i).symm
    have hw'i0 : w' i = 1 := by
      rw [← hw']; rw [Fin.sum_univ_three]
      fin_cases i <;> grind
    have hi1 : c (i + 1) * r (i + 1) = 1 := by simpa [add_assoc, hw'i0] using hc2 (i + 1)
    have hi1' : c (i + 1) * (1 - r (i + 1)) = 0 := by
     simpa [add_assoc, hw'i2] using hc1 (i + 1)
    have hci1 : c (i + 1) = 1 := by
      suffices c (i + 1) * (r (i + 1) + (1 - r (i + 1))) = 1 + 0 by simpa using this
      rw [mul_add]; rw [hi1]; rw [hi1']
    have hri1 : r (i + 1) = 1 := by simpa [hci1] using hi1
    have hi2 : c (i + 2) * (1 - r (i + 2)) = 1 := by simpa [add_assoc, hw'i0] using hc1 (i + 2)
    have hi2' : c (i + 2) * r (i + 2) = 0 := by simpa [add_assoc, hw'i1] using hc2 (i + 2)
    have hci2 : c (i + 2) = 1 := by
      suffices c (i + 2) * (r (i + 2) + (1 - r (i + 2))) = 0 + 1 by simpa using this
      rw [mul_add]; rw [hi2]; rw [hi2']
    have hri2 : r (i + 2) = 0 := by simpa [hci2] using hi2'
    rw [Finset.prod_eq_zero (by simp) hri2]; rw [Finset.prod_eq_zero (i := i + 1) (by simp) (by simp [hri1])]
  · exact mul_left_cancel₀ hc hcr

end CommRing

section Field

variable [Field k] [AddCommGroup V] [Module k V] [AffineSpace V P]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `prod_div_one_sub_eq_one_of_mem_line_point_lineMap` / 引理 `prod_div_one_sub_eq_one_of_mem_line_point_lineMap`

English:
lemma prod_div_one_sub_eq_one_of_mem_line_point_lineMap
  statement: {t : Triangle k P} {r : Fin 3 -> k}
  proof: by
  rw [Finset.prod_div_distrib]; rw [← prod_eq_prod_one_sub_of_mem_line_point_lineMap hp']; rw [div_self]
  exact Finset.prod_ne_zero_iff.2 fun _ _ => hr0 _

中文:
引理 prod_div_one_sub_eq_one_of_mem_line_point_lineMap
  结论: {t : Triangle k P} {r : 有限集 3 -> k}
  证明: by
  rw [Finset.prod_div_distrib]; rw [← prod_eq_prod_one_sub_of_mem_line_point_lineMap hp']; rw [div_self]
  exact Finset.prod_ne_zero_iff.2 fun _ _ => hr0 _

Depends on / 依赖: Finset, Finset.prod_div_distrib, Finset.prod_ne_zero_iff, div_self, prod_div_distrib, prod_eq_prod_one_sub_of_mem_line_point_lineMap, prod_ne_zero_iff
-/
lemma prod_div_one_sub_eq_one_of_mem_line_point_lineMap {t : Triangle k P} {r : Fin 3 -> k}
    (hr0 : forall i, r i != 0) {p' : P} (hp' : forall i : Fin 3, p' in
      line[k, t.points i, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i)]) :
    ∏ i, r i / (1 - r i) = 1 := by
  rw [Finset.prod_div_distrib]; rw [← prod_eq_prod_one_sub_of_mem_line_point_lineMap hp']; rw [div_self]
  exact Finset.prod_ne_zero_iff.2 fun _ _ => hr0 _

end Field

end Affine.Triangle
