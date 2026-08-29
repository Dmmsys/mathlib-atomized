/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Results about pointwise operations on sets with iteration.
-/

public section


open scoped Pointwise

open Set Function

/-- Let `n : ℤ` and `s` a subset of a commutative group `G` that is invariant under preimage for
the map `x ↦ x^n`. Then `s` is invariant under the pointwise action of the subgroup of elements
`g : G` such that `g^(n^j) = 1` for some `j : ℕ`. (This subgroup is called the Prüfer subgroup when
`G` is the `Circle` and `n` is prime.) -/
@[to_additive
      /-- Let `n : ℤ` and `s` a subset of an additive commutative group `G` that is invariant
      under preimage for the map `x ↦ n • x`. Then `s` is invariant under the pointwise action of
      the additive subgroup of elements `g : G` such that `(n^j) • g = 0` for some `j : ℕ`.
      (This additive subgroup is called the Prüfer subgroup when `G` is the `AddCircle` and `n` is
      prime.) -/]
/--
theorem `smul_eq_self_of_preimage_zpow_eq_self` / 定理 `smul_eq_self_of_preimage_zpow_eq_self`

English:
theorem smul_eq_self_of_preimage_zpow_eq_self
  statement: {G : Type*} [CommGroup G] {n : Int} {s : Set G}
  proof: by
  suffices forall {g' : G} (_ : g' ^ n ^ j = 1), g' • s subseteq s by
    refine le_antisymm (this hg) ?_
    conv_lhs => rw [← smul_inv_smul g s]
    replace hg : g⁻¹ ^ n ^ j = 1 := by rw [inv_zpow, hg, inv_one]
    simp only [smul_set_subset_smul_set_iff, this hg]
  rw [(IsFixedPt.preimage_iter

中文:
定理 smul_eq_self_of_preimage_zpow_eq_self
  结论: {G : 类型} [交换群 G] {n : 整数} {s : 集合 G}
  证明: by
  suffices forall {g' : G} (_ : g' ^ n ^ j = 1), g' • s subseteq s by
    refine le_antisymm (this hg) ?_
    conv_lhs => rw [← smul_inv_smul g s]
    replace hg : g⁻¹ ^ n ^ j = 1 := by rw [inv_zpow, hg, inv_one]
    simp only [smul_set_subset_smul_set_iff, this hg]
  rw [(IsFixedPt.preimage_iter

Depends on / 依赖: IsFixedPt, IsFixedPt.preimage_iterate, conv_lhs, inv_one, inv_zpow, iterate_map_mul, le_antisymm, one_, preimage_iterate, replace, smul_inv_smul, smul_set_subset_smul_set_iff, subseteq, zpowGroupHom
-/
theorem smul_eq_self_of_preimage_zpow_eq_self {G : Type*} [CommGroup G] {n : Int} {s : Set G}
    (hs : (fun x => x ^ n) ⁻¹' s = s) {g : G} {j : Nat} (hg : g ^ n ^ j = 1) : g • s = s := by
  suffices forall {g' : G} (_ : g' ^ n ^ j = 1), g' • s subseteq s by
    refine le_antisymm (this hg) ?_
    conv_lhs => rw [← smul_inv_smul g s]
    replace hg : g⁻¹ ^ n ^ j = 1 := by rw [inv_zpow, hg, inv_one]
    simp only [smul_set_subset_smul_set_iff, this hg]
  rw [(IsFixedPt.preimage_iterate hs j : (zpowGroupHom n)^[j] ⁻¹' s = s).symm]
  rintro g' hg' - ⟨y, hy, rfl⟩
  change (zpowGroupHom n)^[j] (g' * y) in s
  replace hg' : (zpowGroupHom n)^[j] g' = 1 := by simpa [zpowGroupHom]
  rwa [iterate_map_mul, hg', one_mul]
