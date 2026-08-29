/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.Ceva

/-!
# Ceva's theorem.

This file proves various versions of Ceva's theorem in a `NormedAddTorsor`.

## References

* https://en.wikipedia.org/wiki/Ceva%27s_theorem

-/

public section


open scoped Affine

variable {𝕜 V P : Type*} [SeminormedAddCommGroup V] [NormedField 𝕜] [NormedSpace 𝕜 V]

namespace Affine.Triangle

variable [PseudoMetricSpace P] [NormedAddTorsor V P] in
/--
lemma `prod_dist_eq_prod_dist_of_mem_line_of_mem_line` / 引理 `prod_dist_eq_prod_dist_of_mem_line_of_mem_line`

English:
lemma prod_dist_eq_prod_dist_of_mem_line_of_mem_line
  statement: {t : Triangle 𝕜 P} {p : Fin 3 -> P} {p' : P}
  proof: by
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  simp_rw [← hr] at hp'
  simp_rw [← hr, dist_lineMap_right, dist_left_lineMap, Finset.prod_mul_distrib, ← norm_prod,
    prod_eq_prod_one_sub_of_mem_line_point_lineMap hp']

中文:
引理 prod_dist_eq_prod_dist_of_mem_line_of_mem_line
  结论: {t : Triangle 𝕜 P} {p : 有限集 3 -> P} {p' : P}
  证明: by
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  simp_rw [← hr] at hp'
  simp_rw [← hr, dist_lineMap_right, dist_left_lineMap, Finset.prod_mul_distrib, ← norm_prod,
    prod_eq_prod_one_sub_of_mem_line_point_lineMap hp']

Depends on / 依赖: Finset, Finset.prod_mul_distrib, dist_left_lineMap, dist_lineMap_right, mem_affineSpan_pair_iff_exists_lineMap_eq, norm_prod, prod_eq_prod_one_sub_of_mem_line_point_lineMap, prod_mul_distrib, simp_rw
-/
lemma prod_dist_eq_prod_dist_of_mem_line_of_mem_line {t : Triangle 𝕜 P} {p : Fin 3 -> P} {p' : P}
    (hp : forall i : Fin 3, p i in line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hp' : forall i : Fin 3, p' in line[𝕜, t.points i, p i]) :
    ∏ i, dist (t.points (i + 1)) (p i) = ∏ i, dist (p i) (t.points (i + 2)) := by
  simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp
  choose r hr using hp
  simp_rw [← hr] at hp'
  simp_rw [← hr, dist_lineMap_right, dist_left_lineMap, Finset.prod_mul_distrib, ← norm_prod,
    prod_eq_prod_one_sub_of_mem_line_point_lineMap hp']

variable [MetricSpace P] [NormedAddTorsor V P] in
/--
lemma `prod_dist_div_dist_eq_one_of_mem_line_of_mem_line` / 引理 `prod_dist_div_dist_eq_one_of_mem_line_of_mem_line`

English:
lemma prod_dist_div_dist_eq_one_of_mem_line_of_mem_line
  statement: {t : Triangle 𝕜 P} {p : Fin 3 -> P} {p' : P}
  proof: by
  have aux (i) : dist (p i) (t.points (i + 2)) != 0 := by simpa using hp0 i
  have key := prod_dist_eq_prod_dist_of_mem_line_of_mem_line hp hp'
  rw [Fin.prod_univ_three] at key ⊢
  rw [Fin.prod_univ_three] at key
  have := aux 0
  have := aux 1
  have := aux 2
  field_simp
  exact key

中文:
引理 prod_dist_div_dist_eq_one_of_mem_line_of_mem_line
  结论: {t : Triangle 𝕜 P} {p : 有限集 3 -> P} {p' : P}
  证明: by
  have aux (i) : dist (p i) (t.points (i + 2)) != 0 := by simpa using hp0 i
  have key := prod_dist_eq_prod_dist_of_mem_line_of_mem_line hp hp'
  rw [Fin.prod_univ_three] at key ⊢
  rw [Fin.prod_univ_three] at key
  have := aux 0
  have := aux 1
  have := aux 2
  field_simp
  exact key

Depends on / 依赖: Fin.prod_univ_three, points, prod_dist_eq_prod_dist_of_mem_line_of_mem_line, prod_univ_three, t.points
-/
lemma prod_dist_div_dist_eq_one_of_mem_line_of_mem_line {t : Triangle 𝕜 P} {p : Fin 3 -> P} {p' : P}
    (hp0 : forall i, p i != t.points (i + 2))
    (hp : forall i : Fin 3, p i in line[𝕜, t.points (i + 1), t.points (i + 2)])
    (hp' : forall i : Fin 3, p' in line[𝕜, t.points i, p i]) :
    ∏ i, dist (t.points (i + 1)) (p i) / dist (p i) (t.points (i + 2)) = 1 := by
  have aux (i) : dist (p i) (t.points (i + 2)) != 0 := by simpa using hp0 i
  have key := prod_dist_eq_prod_dist_of_mem_line_of_mem_line hp hp'
  rw [Fin.prod_univ_three] at key ⊢
  rw [Fin.prod_univ_three] at key
  have := aux 0
  have := aux 1
  have := aux 2
  field_simp
  exact key

end Affine.Triangle
