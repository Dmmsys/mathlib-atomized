/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Polynomial.Cardinal
public import Mathlib.RingTheory.Algebraic.Basic

/-!
### Cardinality of algebraic numbers

In this file, we prove variants of the following result: the cardinality of algebraic numbers under
an R-algebra is at most `#R[X] * ℵ₀`.

Although this can be used to prove that real or complex transcendental numbers exist, a more direct
proof is given by `Liouville.transcendental`.
-/

public section


universe u v

open Cardinal Polynomial Set

open Cardinal Polynomial

namespace Algebraic

/--
theorem `infinite_of_charZero` / 定理 `infinite_of_charZero`

English:
theorem infinite_of_charZero
  statement: (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
  proof: by
  let := MulActionWithZero.nontrivial R A
  exact infinite_of_injective_forall_mem Nat.cast_injective isAlgebraic_natCast

中文:
定理 infinite_of_charZero
  结论: (R A : 类型) [CommRing R] [Ring A] [Algebra R A]
  证明: by
  let := MulActionWithZero.nontrivial R A
  exact infinite_of_injective_forall_mem Nat.cast_injective isAlgebraic_natCast

Depends on / 依赖: MulActionWithZero, MulActionWithZero.nontrivial, Nat.cast_injective, cast_injective, infinite_of_injective_forall_mem, isAlgebraic_natCast, nontrivial
-/
theorem infinite_of_charZero (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    [CharZero A] : { x : A | IsAlgebraic R x }.Infinite := by
  let := MulActionWithZero.nontrivial R A
  exact infinite_of_injective_forall_mem Nat.cast_injective isAlgebraic_natCast

/--
theorem `aleph0_le_cardinalMk_of_charZero` / 定理 `aleph0_le_cardinalMk_of_charZero`

English:
theorem aleph0_le_cardinalMk_of_charZero
  statement: (R A : Type*) [CommRing R] [Ring A]
  proof: infinite_iff.1 (Set.infinite_coe_iff.2 <| infinite_of_charZero R A)

中文:
定理 aleph0_le_cardinalMk_of_charZero
  结论: (R A : 类型) [CommRing R] [Ring A]
  证明: infinite_iff.1 (Set.infinite_coe_iff.2 <| infinite_of_charZero R A)

Depends on / 依赖: Set.infinite_coe_iff, infinite_coe_iff, infinite_iff, infinite_of_charZero
-/
theorem aleph0_le_cardinalMk_of_charZero (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] [CharZero A] : ℵ₀ <= #{ x : A // IsAlgebraic R x } :=
  infinite_iff.1 (Set.infinite_coe_iff.2 <| infinite_of_charZero R A)

section lift

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

/--
theorem `cardinalMk_lift_le_mul` / 定理 `cardinalMk_lift_le_mul`

English:
theorem cardinalMk_lift_le_mul
  proof: by
  rw [← mk_uLift]; rw [← mk_uLift]
  choose g hg₁ hg₂ using fun x : { x : A | IsAlgebraic R x } => x.coe_prop
  refine lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le g fun f => ?_
  rw [lift_le_aleph0]; rw [le_aleph0_iff_set_countable]
  suffices MapsTo (↑) (g ⁻¹' {f}) (f.rootSet A) from
    this.

中文:
定理 cardinalMk_lift_le_mul
  证明: by
  rw [← mk_uLift]; rw [← mk_uLift]
  choose g hg₁ hg₂ using fun x : { x : A | IsAlgebraic R x } => x.coe_prop
  refine lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le g fun f => ?_
  rw [lift_le_aleph0]; rw [le_aleph0_iff_set_countable]
  suffices MapsTo (↑) (g ⁻¹' {f}) (f.rootSet A) from
    this.

Depends on / 依赖: IsAlgebraic, MapsTo, Subtype, Subtype.coe_injective.injOn, coe_injective, coe_prop, countable, countable_of_injOn, f.rootSet, f.rootSet_finite, le_aleph0_iff_set_countable, lift_le_aleph0, lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le, mem_rootSet, mk_uLift, rootSet, rootSet_finite, this.countable_of_injOn, x.coe_prop
-/
theorem cardinalMk_lift_le_mul :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } <= Cardinal.lift.{v} #R[X] * ℵ₀ := by
  rw [← mk_uLift]; rw [← mk_uLift]
  choose g hg₁ hg₂ using fun x : { x : A | IsAlgebraic R x } => x.coe_prop
  refine lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le g fun f => ?_
  rw [lift_le_aleph0]; rw [le_aleph0_iff_set_countable]
  suffices MapsTo (↑) (g ⁻¹' {f}) (f.rootSet A) from
    this.countable_of_injOn Subtype.coe_injective.injOn (f.rootSet_finite A).countable
  rintro x (rfl : g x = f)
  exact mem_rootSet.2 ⟨hg₁ x, hg₂ x⟩

/--
theorem `cardinalMk_lift_le_max` / 定理 `cardinalMk_lift_le_max`

English:
theorem cardinalMk_lift_le_max
  proof: (cardinalMk_lift_le_mul R A).trans by grw [lift_le.2 cardinalMk_le_max]; simp

@[simp]

中文:
定理 cardinalMk_lift_le_max
  证明: (cardinalMk_lift_le_mul R A).trans by grw [lift_le.2 cardinalMk_le_max]; simp

@[simp]

Depends on / 依赖: cardinalMk_le_max, cardinalMk_lift_le_mul, lift_le
-/
theorem cardinalMk_lift_le_max :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } <= max (Cardinal.lift.{v} #R) ℵ₀ :=
(cardinalMk_lift_le_mul R A).trans by grw [lift_le.2 cardinalMk_le_max]; simp

@[simp]
/--
theorem `cardinalMk_lift_of_infinite` / 定理 `cardinalMk_lift_of_infinite`

English:
theorem cardinalMk_lift_of_infinite
  given: [Infinite R]
  proof: ((cardinalMk_lift_le_max R A).trans_eq (max_eq_left <| aleph0_le_mk _)).antisymm
    lift_mk_le'.2 ⟨⟨fun x => ⟨algebraMap R A x, isAlgebraic_algebraMap _⟩, fun _ _ h =>
      FaithfulSMul.algebraMap_injective R A (Subtype.ext_iff.1 h)⟩⟩

中文:
定理 cardinalMk_lift_of_infinite
  条件: [Infinite R]
  证明: ((cardinalMk_lift_le_max R A).trans_eq (max_eq_left <| aleph0_le_mk _)).antisymm
    lift_mk_le'.2 ⟨⟨fun x => ⟨algebraMap R A x, isAlgebraic_algebraMap _⟩, fun _ _ h =>
      FaithfulSMul.algebraMap_injective R A (Subtype.ext_iff.1 h)⟩⟩

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Subtype, Subtype.ext_iff, aleph0_le_mk, algebraMap, algebraMap_injective, antisymm, cardinalMk_lift_le_max, ext_iff, isAlgebraic_algebraMap, lift_mk_le, max_eq_left, trans_eq
-/
theorem cardinalMk_lift_of_infinite [Infinite R] :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } = Cardinal.lift.{v} #R :=
((cardinalMk_lift_le_max R A).trans_eq (max_eq_left <| aleph0_le_mk _)).antisymm
    lift_mk_le'.2 ⟨⟨fun x => ⟨algebraMap R A x, isAlgebraic_algebraMap _⟩, fun _ _ h =>
      FaithfulSMul.algebraMap_injective R A (Subtype.ext_iff.1 h)⟩⟩

variable [Countable R]

@[simp]
/--
theorem `countable` / 定理 `countable`

English:
theorem countable
  statement: Set.Countable { x : A | IsAlgebraic R x }
  proof: by
  rw [← le_aleph0_iff_set_countable]; rw [← lift_le_aleph0]
  apply (cardinalMk_lift_le_max R A).trans
  simp

@[simp]

中文:
定理 countable
  结论: Set.Countable { x : A | IsAlgebraic R x }
  证明: by
  rw [← le_aleph0_iff_set_countable]; rw [← lift_le_aleph0]
  apply (cardinalMk_lift_le_max R A).trans
  simp

@[simp]
-/
protected theorem countable : Set.Countable { x : A | IsAlgebraic R x } := by
  rw [← le_aleph0_iff_set_countable]; rw [← lift_le_aleph0]
  apply (cardinalMk_lift_le_max R A).trans
  simp

@[simp]
/--
theorem `cardinalMk_of_countable_of_charZero` / 定理 `cardinalMk_of_countable_of_charZero`

English:
theorem cardinalMk_of_countable_of_charZero
  given: [CharZero A]
  proof: (Algebraic.countable R A).le_aleph0.antisymm (aleph0_le_cardinalMk_of_charZero R A)

中文:
定理 cardinalMk_of_countable_of_charZero
  条件: [CharZero A]
  证明: (Algebraic.countable R A).le_aleph0.antisymm (aleph0_le_cardinalMk_of_charZero R A)

Depends on / 依赖: Algebraic, Algebraic.countable, aleph0_le_cardinalMk_of_charZero, antisymm, countable, le_aleph0, le_aleph0.antisymm
-/
theorem cardinalMk_of_countable_of_charZero [CharZero A] :
    #{ x : A // IsAlgebraic R x } = ℵ₀ :=
  (Algebraic.countable R A).le_aleph0.antisymm (aleph0_le_cardinalMk_of_charZero R A)

end lift

section NonLift

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

/--
theorem `cardinalMk_le_mul` / 定理 `cardinalMk_le_mul`

English:
theorem cardinalMk_le_mul
  statement: #{ x : A // IsAlgebraic R x } <= #R[X] * ℵ₀
  proof: by
  rw [← lift_id #_]; rw [← lift_id #R[X]]
  exact cardinalMk_lift_le_mul R A

@[stacks 09GK]

中文:
定理 cardinalMk_le_mul
  结论: #{ x : A // IsAlgebraic R x } <= #R[X] * ℵ₀
  证明: by
  rw [← lift_id #_]; rw [← lift_id #R[X]]
  exact cardinalMk_lift_le_mul R A

@[stacks 09GK]

Depends on / 依赖: cardinalMk_lift_le_mul, lift_id
-/
theorem cardinalMk_le_mul : #{ x : A // IsAlgebraic R x } <= #R[X] * ℵ₀ := by
  rw [← lift_id #_]; rw [← lift_id #R[X]]
  exact cardinalMk_lift_le_mul R A

@[stacks 09GK]
/--
theorem `cardinalMk_le_max` / 定理 `cardinalMk_le_max`

English:
theorem cardinalMk_le_max
  statement: #{ x : A // IsAlgebraic R x } <= max #R ℵ₀
  proof: by
  rw [← lift_id #_]; rw [← lift_id #R]
  exact cardinalMk_lift_le_max R A

@[simp]

中文:
定理 cardinalMk_le_max
  结论: #{ x : A // IsAlgebraic R x } <= max #R ℵ₀
  证明: by
  rw [← lift_id #_]; rw [← lift_id #R]
  exact cardinalMk_lift_le_max R A

@[simp]

Depends on / 依赖: cardinalMk_lift_le_max, lift_id
-/
theorem cardinalMk_le_max : #{ x : A // IsAlgebraic R x } <= max #R ℵ₀ := by
  rw [← lift_id #_]; rw [← lift_id #R]
  exact cardinalMk_lift_le_max R A

@[simp]
/--
theorem `cardinalMk_of_infinite` / 定理 `cardinalMk_of_infinite`

English:
theorem cardinalMk_of_infinite
  given: [Infinite R]
  statement: #{ x : A // IsAlgebraic R x } = #R
  proof: lift_inj.1 cardinalMk_lift_of_infinite R A

中文:
定理 cardinalMk_of_infinite
  条件: [Infinite R]
  结论: #{ x : A // IsAlgebraic R x } = #R
  证明: lift_inj.1 cardinalMk_lift_of_infinite R A

Depends on / 依赖: cardinalMk_lift_of_infinite, lift_inj
-/
theorem cardinalMk_of_infinite [Infinite R] : #{ x : A // IsAlgebraic R x } = #R :=
lift_inj.1 cardinalMk_lift_of_infinite R A

end NonLift

end Algebraic
