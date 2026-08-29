/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!

# Cardinality of Ore localizations

This file contains some results on cardinality of Ore localizations.

## TODO

- Prove or disprove `OreLocalization.cardinalMk_le_lift_cardinalMk_of_commute`
  with `Commute` assumption removed.

-/

public section

universe u v

open Cardinal Function

namespace OreLocalization

variable {R : Type u} [Monoid R] (S : Submonoid R) [OreLocalization.OreSet S]
  (X : Type v) [MulAction R X]

@[to_additive]
/--
theorem `oreDiv_one_surjective_of_finite_left` / 定理 `oreDiv_one_surjective_of_finite_left`

English:
theorem oreDiv_one_surjective_of_finite_left
  given: [Finite S]
  proof: by
  refine OreLocalization.ind fun x s => ?_
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (α := Nat) (s ^ ·)
  wlog! hlt : j < i generalizing i j
  · exact this j i hne.symm heq.symm (hne.lt_of_le hlt)
  use s ^ (i - (j + 1)) • x
  rw [oreDiv_eq_iff]
  refine ⟨s ^ j, (s ^ (j + 1

中文:
定理 oreDiv_one_surjective_of_finite_left
  条件: [有限 S]
  证明: by
  refine OreLocalization.ind fun x s => ?_
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (α := Nat) (s ^ ·)
  wlog! hlt : j < i generalizing i j
  · exact this j i hne.symm heq.symm (hne.lt_of_le hlt)
  use s ^ (i - (j + 1)) • x
  rw [oreDiv_eq_iff]
  refine ⟨s ^ j, (s ^ (j + 1

Depends on / 依赖: Finite, Finite.exists_ne_map_eq_of_infinite, Nat.add_sub_cancel, OneMemClass, OneMemClass.coe_one, OreLocalization, OreLocalization.ind, SubmonoidClass, SubmonoidClass.coe_pow, add_sub_cancel, coe_one, coe_pow, exists_ne_map_eq_of_infinite, generalizing, heq.symm, hne.lt_of_le, hne.symm, lt_of_le, mul_one, mul_smul
-/
theorem oreDiv_one_surjective_of_finite_left [Finite S] :
    Surjective (fun x => x /ₒ (1 : ↥S) : X -> OreLocalization S X) := by
  refine OreLocalization.ind fun x s => ?_
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (α := Nat) (s ^ ·)
  wlog! hlt : j < i generalizing i j
  · exact this j i hne.symm heq.symm (hne.lt_of_le hlt)
  use s ^ (i - (j + 1)) • x
  rw [oreDiv_eq_iff]
  refine ⟨s ^ j, (s ^ (j + 1)).1, ?_, ?_⟩
  · change s ^ j • x = s ^ (j + 1) • s ^ (i - (j + 1)) • x
    rw [← mul_smul]; rw [← pow_add]; rw [Nat.add_sub_cancel' hlt]; rw [heq]
  · simp_rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, mul_one, pow_succ]

@[to_additive]
/--
theorem `oreDiv_one_surjective_of_finite_right` / 定理 `oreDiv_one_surjective_of_finite_right`

English:
theorem oreDiv_one_surjective_of_finite_right
  given: [Finite X]
  proof: by
  refine OreLocalization.ind fun x s => ?_
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (α := Nat) (s ^ · • x)
  wlog! hlt : j < i generalizing i j
  · exact this j i hne.symm heq.symm (hne.lt_of_le hlt)
  use s ^ (i - (j + 1)) • x
  rw [oreDiv_eq_iff]
  refine ⟨s ^ j, (s ^ (j

中文:
定理 oreDiv_one_surjective_of_finite_right
  条件: [有限 X]
  证明: by
  refine OreLocalization.ind fun x s => ?_
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (α := Nat) (s ^ · • x)
  wlog! hlt : j < i generalizing i j
  · exact this j i hne.symm heq.symm (hne.lt_of_le hlt)
  use s ^ (i - (j + 1)) • x
  rw [oreDiv_eq_iff]
  refine ⟨s ^ j, (s ^ (j

Depends on / 依赖: Finite, Finite.exists_ne_map_eq_of_infinite, Nat.add_sub_cancel, OneMemClass, OneMemClass.coe_one, OreLocalization, OreLocalization.ind, SubmonoidClass, SubmonoidClass.coe_pow, add_sub_cancel, coe_one, coe_pow, exists_ne_map_eq_of_infinite, generalizing, heq.symm, hne.lt_of_le, hne.symm, lt_of_le, mul_one, mul_smul
-/
theorem oreDiv_one_surjective_of_finite_right [Finite X] :
    Surjective (fun x => x /ₒ (1 : ↥S) : X -> OreLocalization S X) := by
  refine OreLocalization.ind fun x s => ?_
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (α := Nat) (s ^ · • x)
  wlog! hlt : j < i generalizing i j
  · exact this j i hne.symm heq.symm (hne.lt_of_le hlt)
  use s ^ (i - (j + 1)) • x
  rw [oreDiv_eq_iff]
  refine ⟨s ^ j, (s ^ (j + 1)).1, ?_, ?_⟩
  · change s ^ j • x = s ^ (j + 1) • s ^ (i - (j + 1)) • x
    rw [← mul_smul]; rw [← pow_add]; rw [Nat.add_sub_cancel' hlt]; rw [heq]
  · simp_rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, mul_one, pow_succ]

@[to_additive]
/--
theorem `numeratorHom_surjective_of_finite` / 定理 `numeratorHom_surjective_of_finite`

English:
theorem numeratorHom_surjective_of_finite
  given: [Finite S]
  statement: Surjective (numeratorHom (S := S))
  proof: oreDiv_one_surjective_of_finite_left S R

@[to_additive]

中文:
定理 numeratorHom_surjective_of_finite
  条件: [有限 S]
  结论: 满射 (numeratorHom (S := S))
  证明: oreDiv_one_surjective_of_finite_left S R

@[to_additive]
-/
theorem numeratorHom_surjective_of_finite [Finite S] : Surjective (numeratorHom (S := S)) :=
  oreDiv_one_surjective_of_finite_left S R

@[to_additive]
/--
theorem `cardinalMk_le_max` / 定理 `cardinalMk_le_max`

English:
theorem cardinalMk_le_max
  statement: #(OreLocalization S X) <= max (lift.{v} #S) (lift.{u} #X)
  proof: by
  rcases finite_or_infinite X with _ | _
  · have := lift_mk_le_lift_mk_of_surjective (oreDiv_one_surjective_of_finite_right S X)
    rw [lift_umax.{v]; rw [u}]; rw [lift_id'] at this
    exact le_max_of_le_right this
  rcases finite_or_infinite S with _ | _
  · have := lift_mk_le_lift_mk_of_surj

中文:
定理 cardinalMk_le_max
  结论: #(OreLocalization S X) <= 最大值 (lift.{v} #S) (lift.{u} #X)
  证明: by
  rcases finite_or_infinite X with _ | _
  · have := lift_mk_le_lift_mk_of_surjective (oreDiv_one_surjective_of_finite_right S X)
    rw [lift_umax.{v]; rw [u}]; rw [lift_id'] at this
    exact le_max_of_le_right this
  rcases finite_or_infinite S with _ | _
  · have := lift_mk_le_lift_mk_of_surj

Depends on / 依赖: Surjective, convert, finite_or_infinite, le_max_of_le_right, lift_id, lift_mk_le_lift_mk_of_surjective, lift_umax, mk_le_of_surjective, oreDiv_one_surjective_of_finite_left, oreDiv_one_surjective_of_finite_right
-/
theorem cardinalMk_le_max : #(OreLocalization S X) <= max (lift.{v} #S) (lift.{u} #X) := by
  rcases finite_or_infinite X with _ | _
  · have := lift_mk_le_lift_mk_of_surjective (oreDiv_one_surjective_of_finite_right S X)
    rw [lift_umax.{v]; rw [u}]; rw [lift_id'] at this
    exact le_max_of_le_right this
  rcases finite_or_infinite S with _ | _
  · have := lift_mk_le_lift_mk_of_surjective (oreDiv_one_surjective_of_finite_left S X)
    rw [lift_umax.{v]; rw [u}]; rw [lift_id'] at this
    exact le_max_of_le_right this
  convert! ←
    mk_le_of_surjective (show Surjective fun x : X × S => x.1 /ₒ x.2 from Quotient.mk''_surjective)
  rw [mk_prod]; rw [mul_comm]
  refine mul_eq_max ?_ ?_ <;> simp

@[to_additive]
/--
theorem `cardinalMk_le` / 定理 `cardinalMk_le`

English:
theorem cardinalMk_le
  statement: #(OreLocalization S R) <= #R
  proof: by
  convert! ← cardinalMk_le_max S R
  simp_rw [lift_id, max_eq_right_iff, mk_subtype_le]

中文:
定理 cardinalMk_le
  结论: #(OreLocalization S R) <= #R
  证明: by
  convert! ← cardinalMk_le_max S R
  simp_rw [lift_id, max_eq_right_iff, mk_subtype_le]

Depends on / 依赖: cardinalMk_le_max, convert, lift_id, max_eq_right_iff, mk_subtype_le, simp_rw
-/
theorem cardinalMk_le : #(OreLocalization S R) <= #R := by
  convert! ← cardinalMk_le_max S R
  simp_rw [lift_id, max_eq_right_iff, mk_subtype_le]

-- TODO: remove the `Commute` assumption
@[to_additive]
/--
theorem `cardinalMk_le_lift_cardinalMk_of_commute` / 定理 `cardinalMk_le_lift_cardinalMk_of_commute`

English:
theorem cardinalMk_le_lift_cardinalMk_of_commute
  given: (hc : forall s s' : S, Commute s s')
  proof: by
  rcases finite_or_infinite X with _ | _
  · have := lift_mk_le_lift_mk_of_surjective (oreDiv_one_surjective_of_finite_right S X)
    rwa [lift_umax.{v, u}, lift_id'] at this
  have key (x : X) (s s' : S) (h : s • x = s' • x) (hc : Commute s s') : x /ₒ s = x /ₒ s' := by
    rw [oreDiv_eq_iff]
   

中文:
定理 cardinalMk_le_lift_cardinalMk_of_commute
  条件: (hc : 对任意 s s' : S, Commute s s')
  证明: by
  rcases finite_or_infinite X with _ | _
  · have := lift_mk_le_lift_mk_of_surjective (oreDiv_one_surjective_of_finite_right S X)
    rwa [lift_umax.{v, u}, lift_id'] at this
  have key (x : X) (s s' : S) (h : s • x = s' • x) (hc : Commute s s') : x /ₒ s = x /ₒ s' := by
    rw [oreDiv_eq_iff]
   

Depends on / 依赖: Commute, Quotient, Quotient.mk, Surjective, _surjective, finite_or_infinite, lift_id, lift_mk_le_lift_mk_of_surjective, lift_umax, oreDiv_eq_iff, oreDiv_one_surjective_of_finite_right, rightInverse_surjInv
-/
theorem cardinalMk_le_lift_cardinalMk_of_commute (hc : forall s s' : S, Commute s s') :
    #(OreLocalization S X) <= lift.{u} #X := by
  rcases finite_or_infinite X with _ | _
  · have := lift_mk_le_lift_mk_of_surjective (oreDiv_one_surjective_of_finite_right S X)
    rwa [lift_umax.{v, u}, lift_id'] at this
  have key (x : X) (s s' : S) (h : s • x = s' • x) (hc : Commute s s') : x /ₒ s = x /ₒ s' := by
    rw [oreDiv_eq_iff]
    refine ⟨s, s'.1, h, ?_⟩
    · exact_mod_cast hc
  let i (x : X × S) := x.1 /ₒ x.2
  have hsurj : Surjective i := Quotient.mk''_surjective
  have hi := rightInverse_surjInv hsurj
  let j := (fun x : X × S => (x.1, x.2 • x.1)) ∘ surjInv hsurj
  suffices Injective j by
    have := lift_mk_le_lift_mk_of_injective this
    rwa [lift_umax.{v, u}, lift_id', mk_prod, lift_id, lift_mul, mul_eq_self (by simp)] at this
  intro
  grind

end OreLocalization
