/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Polynomial.UnitTrinomial
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Irreducibility of unit trinomials

## TODO

Develop more theory (e.g., it suffices to check that `aeval z p ≠ 0` for `z = 0` and `z` a root of
unity).
-/

public section

namespace Polynomial.IsUnitTrinomial
variable {p : Int[X]}

/--
theorem `irreducible_of_coprime'` / 定理 `irreducible_of_coprime'`

English:
theorem irreducible_of_coprime'
  statement: (hp : IsUnitTrinomial p)
  proof: by
  refine hp.irreducible_of_coprime fun q hq hq' => ?_
  suffices ¬0 < q.natDegree by
    rcases hq with ⟨p, rfl⟩
    replace hp := hp.leadingCoeff_isUnit
    rw [leadingCoeff_mul] at hp
    replace hp := isUnit_of_mul_isUnit_left hp
    rw [not_lt]; rw [Nat.le_zero] at this
    rwa [eq_C_of_natDe

中文:
定理 irreducible_of_coprime'
  结论: (hp : IsUnitTrinomial p)
  证明: by
  refine hp.irreducible_of_coprime fun q hq hq' => ?_
  suffices ¬0 < q.natDegree by
    rcases hq with ⟨p, rfl⟩
    replace hp := hp.leadingCoeff_isUnit
    rw [leadingCoeff_mul] at hp
    replace hp := isUnit_of_mul_isUnit_left hp
    rw [not_lt]; rw [Nat.le_zero] at this
    rwa [eq_C_of_natDe

Depends on / 依赖: Complex.exists_root, IsRoot, Nat.le_zero, algebraMap, degree_map_eq_of_injective, eq_C_of_natDegree_eq_zero, exists_root, hp.irreducible_of_coprime, hp.leadingCoeff_isUnit, injective_int, irreducible_of_coprime, isUnit_C, isUnit_of_mul_isUnit_left, le_zero, leadingCoeff_isUnit, leadingCoeff_mul, natDegree, natDegree_pos_iff_degree_pos, not_lt, q.natDegree
-/
theorem irreducible_of_coprime' (hp : IsUnitTrinomial p)
    (h : forall z : Complex, ¬(aeval z p = 0 ∧ aeval z (mirror p) = 0)) : Irreducible p := by
  refine hp.irreducible_of_coprime fun q hq hq' => ?_
  suffices ¬0 < q.natDegree by
    rcases hq with ⟨p, rfl⟩
    replace hp := hp.leadingCoeff_isUnit
    rw [leadingCoeff_mul] at hp
    replace hp := isUnit_of_mul_isUnit_left hp
    rw [not_lt]; rw [Nat.le_zero] at this
    rwa [eq_C_of_natDegree_eq_zero this, isUnit_C, ← this]
  intro hq''
  rw [natDegree_pos_iff_degree_pos] at hq''
  rw [← degree_map_eq_of_injective (algebraMap Int Complex).injective_int] at hq''
  obtain ⟨z, hz⟩ := Complex.exists_root hq''
  rw [IsRoot]; rw [eval_map_algebraMap] at hz
  refine h z ⟨?_, ?_⟩
  · obtain ⟨g', hg'⟩ := hq
    rw [hg']; rw [aeval_mul]; rw [hz]; rw [zero_mul]
  · obtain ⟨g', hg'⟩ := hq'
    rw [hg']; rw [aeval_mul]; rw [hz]; rw [zero_mul]

end Polynomial.IsUnitTrinomial
