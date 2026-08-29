/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Tactic.Tauto
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Nat.Units

/-!
# Units in the integers
-/

public section


open Nat

namespace Int

/-! #### Units -/

variable {u v : Int}

/--
lemma `units_natAbs` / 引理 `units_natAbs`

English:
lemma units_natAbs
  given: (u : Intˣ)
  statement: natAbs u = 1
  proof: Units.ext_iff.1
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← natAbs_mul, Units.mul_inv]; rfl, by
        rw [← natAbs_mul]; rw [Units.inv_mul]; rfl⟩

中文:
引理 units_natAbs
  条件: (u : 整数ˣ)
  结论: natAbs u = 1
  证明: Units.ext_iff.1
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← natAbs_mul, Units.mul_inv]; rfl, by
        rw [← natAbs_mul]; rw [Units.inv_mul]; rfl⟩

Depends on / 依赖: Nat.units_eq_one, Units.ext_iff, Units.inv_mul, Units.mul_inv, _image, ext_iff, inv_mul, mul_inv, natAbs, natAbs_mul, units_eq_one
-/
lemma units_natAbs (u : Intˣ) : natAbs u = 1 :=
Units.ext_iff.1
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← natAbs_mul, Units.mul_inv]; rfl, by
        rw [← natAbs_mul]; rw [Units.inv_mul]; rfl⟩

/--
lemma `natAbs_of_isUnit` / 引理 `natAbs_of_isUnit`

English:
lemma natAbs_of_isUnit
  given: (hu : IsUnit u)
  statement: natAbs u = 1
  proof: units_natAbs hu.unit

中文:
引理 natAbs_of_isUnit
  条件: (hu : 是单位 u)
  结论: natAbs u = 1
  证明: units_natAbs hu.unit
-/
@[simp] lemma natAbs_of_isUnit (hu : IsUnit u) : natAbs u = 1 := units_natAbs hu.unit

/--
lemma `isUnit_eq_one_or` / 引理 `isUnit_eq_one_or`

English:
lemma isUnit_eq_one_or
  given: (hu : IsUnit u)
  statement: u = 1 ∨ u = -1
  proof: by
  simpa only [natAbs_of_isUnit hu] using! natAbs_eq u

中文:
引理 isUnit_eq_one_or
  条件: (hu : 是单位 u)
  结论: u = 1 ∨ u = -1
  证明: by
  simpa only [natAbs_of_isUnit hu] using! natAbs_eq u

Depends on / 依赖: natAbs_eq, natAbs_of_isUnit
-/
lemma isUnit_eq_one_or (hu : IsUnit u) : u = 1 ∨ u = -1 := by
  simpa only [natAbs_of_isUnit hu] using! natAbs_eq u

/--
lemma `isUnit_ne_iff_eq_neg` / 引理 `isUnit_ne_iff_eq_neg`

English:
lemma isUnit_ne_iff_eq_neg
  given: (hu : IsUnit u) (hv : IsUnit v)
  statement: u != v ↔ u = -v
  proof: by
  obtain rfl | rfl := isUnit_eq_one_or hu <;> obtain rfl | rfl := isUnit_eq_one_or hv <;> decide

中文:
引理 isUnit_ne_iff_eq_neg
  条件: (hu : 是单位 u) (hv : 是单位 v)
  结论: u != v ↔ u = -v
  证明: by
  obtain rfl | rfl := isUnit_eq_one_or hu <;> obtain rfl | rfl := isUnit_eq_one_or hv <;> decide

Depends on / 依赖: isUnit_eq_one_or
-/
lemma isUnit_ne_iff_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u != v ↔ u = -v := by
  obtain rfl | rfl := isUnit_eq_one_or hu <;> obtain rfl | rfl := isUnit_eq_one_or hv <;> decide

/--
lemma `isUnit_eq_or_eq_neg` / 引理 `isUnit_eq_or_eq_neg`

English:
lemma isUnit_eq_or_eq_neg
  given: (hu : IsUnit u) (hv : IsUnit v)
  statement: u = v ∨ u = -v
  proof: or_iff_not_imp_left.2 (isUnit_ne_iff_eq_neg hu hv).1

中文:
引理 isUnit_eq_or_eq_neg
  条件: (hu : 是单位 u) (hv : 是单位 v)
  结论: u = v ∨ u = -v
  证明: or_iff_not_imp_left.2 (isUnit_ne_iff_eq_neg hu hv).1

Depends on / 依赖: isUnit_ne_iff_eq_neg, or_iff_not_imp_left
-/
lemma isUnit_eq_or_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u = v ∨ u = -v :=
  or_iff_not_imp_left.2 (isUnit_ne_iff_eq_neg hu hv).1

/--
lemma `isUnit_iff` / 引理 `isUnit_iff`

English:
lemma isUnit_iff
  statement: IsUnit u ↔ u = 1 ∨ u = -1
  proof: by
  refine ⟨fun h => isUnit_eq_one_or h, fun h => ?_⟩
  rcases h with (rfl | rfl)
  · exact isUnit_one
  · exact ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩

中文:
引理 isUnit_iff
  结论: 是单位 u ↔ u = 1 ∨ u = -1
  证明: by
  refine ⟨fun h => isUnit_eq_one_or h, fun h => ?_⟩
  rcases h with (rfl | rfl)
  · exact isUnit_one
  · exact ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩

Depends on / 依赖: isUnit_eq_one_or, isUnit_one
-/
lemma isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1 := by
  refine ⟨fun h => isUnit_eq_one_or h, fun h => ?_⟩
  rcases h with (rfl | rfl)
  · exact isUnit_one
  · exact ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩

/--
lemma `eq_one_or_neg_one_of_mul_eq_one` / 引理 `eq_one_or_neg_one_of_mul_eq_one`

English:
lemma eq_one_or_neg_one_of_mul_eq_one
  given: (h : u * v = 1)
  statement: u = 1 ∨ u = -1
  proof: isUnit_iff.1 (.of_mul_eq_one v h)

中文:
引理 eq_one_or_neg_one_of_mul_eq_one
  条件: (h : u * v = 1)
  结论: u = 1 ∨ u = -1
  证明: isUnit_iff.1 (.of_mul_eq_one v h)

Depends on / 依赖: isUnit_iff, of_mul_eq_one
-/
lemma eq_one_or_neg_one_of_mul_eq_one (h : u * v = 1) : u = 1 ∨ u = -1 :=
  isUnit_iff.1 (.of_mul_eq_one v h)

/--
lemma `eq_one_or_neg_one_of_mul_eq_one'` / 引理 `eq_one_or_neg_one_of_mul_eq_one'`

English:
lemma eq_one_or_neg_one_of_mul_eq_one'
  given: (h : u * v = 1)
  statement: u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1
  proof: by
  have h' : v * u = 1 := mul_comm u v ▸ h
  obtain rfl | rfl := eq_one_or_neg_one_of_mul_eq_one h <;>
      obtain rfl | rfl := eq_one_or_neg_one_of_mul_eq_one h' <;> tauto

中文:
引理 eq_one_or_neg_one_of_mul_eq_one'
  条件: (h : u * v = 1)
  结论: u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1
  证明: by
  have h' : v * u = 1 := mul_comm u v ▸ h
  obtain rfl | rfl := eq_one_or_neg_one_of_mul_eq_one h <;>
      obtain rfl | rfl := eq_one_or_neg_one_of_mul_eq_one h' <;> tauto

Depends on / 依赖: eq_one_or_neg_one_of_mul_eq_one, mul_comm
-/
lemma eq_one_or_neg_one_of_mul_eq_one' (h : u * v = 1) : u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  have h' : v * u = 1 := mul_comm u v ▸ h
  obtain rfl | rfl := eq_one_or_neg_one_of_mul_eq_one h <;>
      obtain rfl | rfl := eq_one_or_neg_one_of_mul_eq_one h' <;> tauto

/--
lemma `eq_of_mul_eq_one` / 引理 `eq_of_mul_eq_one`

English:
lemma eq_of_mul_eq_one
  given: (h : u * v = 1)
  statement: u = v
  proof: (eq_one_or_neg_one_of_mul_eq_one' h).elim
    (and_imp.2 (·.trans ·.symm)) (and_imp.2 (·.trans ·.symm))

中文:
引理 eq_of_mul_eq_one
  条件: (h : u * v = 1)
  结论: u = v
  证明: (eq_one_or_neg_one_of_mul_eq_one' h).elim
    (and_imp.2 (·.trans ·.symm)) (and_imp.2 (·.trans ·.symm))

Depends on / 依赖: and_imp, eq_one_or_neg_one_of_mul_eq_one
-/
lemma eq_of_mul_eq_one (h : u * v = 1) : u = v :=
  (eq_one_or_neg_one_of_mul_eq_one' h).elim
    (and_imp.2 (·.trans ·.symm)) (and_imp.2 (·.trans ·.symm))

/--
lemma `mul_eq_one_iff_eq_one_or_neg_one` / 引理 `mul_eq_one_iff_eq_one_or_neg_one`

English:
lemma mul_eq_one_iff_eq_one_or_neg_one
  statement: u * v = 1 ↔ u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1
  proof: by
  refine ⟨eq_one_or_neg_one_of_mul_eq_one', fun h => Or.elim h (fun H => ?_) fun H => ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl

中文:
引理 mul_eq_one_iff_eq_one_or_neg_one
  结论: u * v = 1 ↔ u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1
  证明: by
  refine ⟨eq_one_or_neg_one_of_mul_eq_one', fun h => Or.elim h (fun H => ?_) fun H => ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl

Depends on / 依赖: Or.elim, eq_one_or_neg_one_of_mul_eq_one
-/
lemma mul_eq_one_iff_eq_one_or_neg_one : u * v = 1 ↔ u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  refine ⟨eq_one_or_neg_one_of_mul_eq_one', fun h => Or.elim h (fun H => ?_) fun H => ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl

/--
lemma `eq_one_or_neg_one_of_mul_eq_neg_one'` / 引理 `eq_one_or_neg_one_of_mul_eq_neg_one'`

English:
lemma eq_one_or_neg_one_of_mul_eq_neg_one'
  given: (h : u * v = -1)
  statement: u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1
  proof: by
  obtain rfl | rfl := isUnit_eq_one_or (IsUnit.mul_iff.mp (Int.isUnit_iff.mpr (Or.inr h))).1
  · exact Or.inl ⟨rfl, one_mul v ▸ h⟩
  · simpa [Int.neg_mul] using h

中文:
引理 eq_one_or_neg_one_of_mul_eq_neg_one'
  条件: (h : u * v = -1)
  结论: u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1
  证明: by
  obtain rfl | rfl := isUnit_eq_one_or (IsUnit.mul_iff.mp (Int.isUnit_iff.mpr (Or.inr h))).1
  · exact Or.inl ⟨rfl, one_mul v ▸ h⟩
  · simpa [Int.neg_mul] using h

Depends on / 依赖: Int.isUnit_iff.mpr, Int.neg_mul, IsUnit, IsUnit.mul_iff.mp, Or.inl, Or.inr, isUnit_eq_one_or, isUnit_iff, mul_iff, neg_mul, one_mul
-/
lemma eq_one_or_neg_one_of_mul_eq_neg_one' (h : u * v = -1) : u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  obtain rfl | rfl := isUnit_eq_one_or (IsUnit.mul_iff.mp (Int.isUnit_iff.mpr (Or.inr h))).1
  · exact Or.inl ⟨rfl, one_mul v ▸ h⟩
  · simpa [Int.neg_mul] using h

/--
lemma `mul_eq_neg_one_iff_eq_one_or_neg_one` / 引理 `mul_eq_neg_one_iff_eq_one_or_neg_one`

English:
lemma mul_eq_neg_one_iff_eq_one_or_neg_one
  statement: u * v = -1 ↔ u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1
  proof: by
  refine ⟨eq_one_or_neg_one_of_mul_eq_neg_one', fun h => Or.elim h (fun H => ?_) fun H => ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl

中文:
引理 mul_eq_neg_one_iff_eq_one_or_neg_one
  结论: u * v = -1 ↔ u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1
  证明: by
  refine ⟨eq_one_or_neg_one_of_mul_eq_neg_one', fun h => Or.elim h (fun H => ?_) fun H => ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl

Depends on / 依赖: Or.elim, eq_one_or_neg_one_of_mul_eq_neg_one
-/
lemma mul_eq_neg_one_iff_eq_one_or_neg_one : u * v = -1 ↔ u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  refine ⟨eq_one_or_neg_one_of_mul_eq_neg_one', fun h => Or.elim h (fun H => ?_) fun H => ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl

/--
lemma `isUnit_iff_natAbs_eq` / 引理 `isUnit_iff_natAbs_eq`

English:
lemma isUnit_iff_natAbs_eq
  statement: IsUnit u ↔ u.natAbs = 1
  proof: by simp [natAbs_eq_iff, isUnit_iff]

alias ⟨IsUnit.natAbs_eq, _⟩ := isUnit_iff_natAbs_eq

@[norm_cast]

中文:
引理 isUnit_iff_natAbs_eq
  结论: 是单位 u ↔ u.natAbs = 1
  证明: by simp [natAbs_eq_iff, isUnit_iff]

alias ⟨IsUnit.natAbs_eq, _⟩ := isUnit_iff_natAbs_eq

@[norm_cast]

Depends on / 依赖: isUnit_iff, natAbs_eq_iff
-/
lemma isUnit_iff_natAbs_eq : IsUnit u ↔ u.natAbs = 1 := by simp [natAbs_eq_iff, isUnit_iff]

alias ⟨IsUnit.natAbs_eq, _⟩ := isUnit_iff_natAbs_eq

@[norm_cast]
/--
lemma `ofNat_isUnit` / 引理 `ofNat_isUnit`

English:
lemma ofNat_isUnit
  given: {n : Nat}
  statement: IsUnit (n : Int) ↔ IsUnit n
  proof: by simp [isUnit_iff_natAbs_eq]

中文:
引理 of自然数_isUnit
  条件: {n : 自然数}
  结论: 是单位 (n : 整数) ↔ 是单位 n
  证明: by simp [isUnit_iff_natAbs_eq]

Depends on / 依赖: isUnit_iff_natAbs_eq
-/
lemma ofNat_isUnit {n : Nat} : IsUnit (n : Int) ↔ IsUnit n := by simp [isUnit_iff_natAbs_eq]

/--
lemma `isUnit_mul_self` / 引理 `isUnit_mul_self`

English:
lemma isUnit_mul_self
  given: (hu : IsUnit u)
  statement: u * u = 1
  proof: (isUnit_eq_one_or hu).elim (fun h => h.symm ▸ rfl) fun h => h.symm ▸ rfl

中文:
引理 isUnit_mul_self
  条件: (hu : 是单位 u)
  结论: u * u = 1
  证明: (isUnit_eq_one_or hu).elim (fun h => h.symm ▸ rfl) fun h => h.symm ▸ rfl

Depends on / 依赖: h.symm, isUnit_eq_one_or
-/
lemma isUnit_mul_self (hu : IsUnit u) : u * u = 1 :=
  (isUnit_eq_one_or hu).elim (fun h => h.symm ▸ rfl) fun h => h.symm ▸ rfl

/--
lemma `isUnit_add_isUnit_eq_isUnit_add_isUnit` / 引理 `isUnit_add_isUnit_eq_isUnit_add_isUnit`

English:
lemma isUnit_add_isUnit_eq_isUnit_add_isUnit
  statement: {a b c d : Int} (ha : IsUnit a) (hb : IsUnit b)
  proof: by
  rw [isUnit_iff] at ha hb hc hd
  lia

中文:
引理 isUnit_add_isUnit_eq_isUnit_add_isUnit
  结论: {a b c d : 整数} (ha : 是单位 a) (hb : 是单位 b)
  证明: by
  rw [isUnit_iff] at ha hb hc hd
  lia

Depends on / 依赖: isUnit_iff
-/
lemma isUnit_add_isUnit_eq_isUnit_add_isUnit {a b c d : Int} (ha : IsUnit a) (hb : IsUnit b)
    (hc : IsUnit c) (hd : IsUnit d) : a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  rw [isUnit_iff] at ha hb hc hd
  lia

/--
lemma `eq_one_or_neg_one_of_mul_eq_neg_one` / 引理 `eq_one_or_neg_one_of_mul_eq_neg_one`

English:
lemma eq_one_or_neg_one_of_mul_eq_neg_one
  given: (h : u * v = -1)
  statement: u = 1 ∨ u = -1
  proof: Or.elim (eq_one_or_neg_one_of_mul_eq_neg_one' h) (fun H => Or.inl H.1) fun H => Or.inr H.1

中文:
引理 eq_one_or_neg_one_of_mul_eq_neg_one
  条件: (h : u * v = -1)
  结论: u = 1 ∨ u = -1
  证明: Or.elim (eq_one_or_neg_one_of_mul_eq_neg_one' h) (fun H => Or.inl H.1) fun H => Or.inr H.1

Depends on / 依赖: Or.elim, Or.inl, Or.inr, eq_one_or_neg_one_of_mul_eq_neg_one
-/
lemma eq_one_or_neg_one_of_mul_eq_neg_one (h : u * v = -1) : u = 1 ∨ u = -1 :=
  Or.elim (eq_one_or_neg_one_of_mul_eq_neg_one' h) (fun H => Or.inl H.1) fun H => Or.inr H.1

end Int
