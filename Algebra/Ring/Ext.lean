/-
Copyright (c) 2024 Raghuram Sundararajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raghuram Sundararajan
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Ext

/-!
# Extensionality lemmas for rings and similar structures

In this file we prove extensionality lemmas for the ring-like structures defined in
`Mathlib/Algebra/Ring/Defs.lean`, ranging from `NonUnitalNonAssocSemiring` to `CommRing`. These
extensionality lemmas take the form of asserting that two algebraic structures on a type are equal
whenever the addition and multiplication defined by them are both the same.

## Implementation details

We follow `Mathlib/Algebra/Group/Ext.lean` in using the term `(letI := i; HMul.hMul : R → R → R)` to
refer to the multiplication specified by a typeclass instance `i` on a type `R` (and similarly for
addition). We abbreviate these using some local notations.

Since `Mathlib/Algebra/Group/Ext.lean` proved several injectivity lemmas, we do so as well — even if
sometimes we don't need them to prove extensionality.

## Tags
semiring, ring, extensionality
-/

public section

local macro:max "local_hAdd[" type:term ", " inst:term "]" : term =>
  `(term| (letI := $inst; HAdd.hAdd : $type -> $type -> $type))
local macro:max "local_hMul[" type:term ", " inst:term "]" : term =>
  `(term| (letI := $inst; HMul.hMul : $type -> $type -> $type))

universe u

variable {R : Type u}

/-! ### Distrib -/
namespace Distrib

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: Distrib R⦄
  proof: by
  -- Split into `add` and `mul` functions and properties.
  rcases inst₁ with @⟨⟨⟩, ⟨⟩⟩
  rcases inst₂ with @⟨⟨⟩, ⟨⟩⟩
  -- Prove equality of parts using function extensionality.
  congr

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: Distrib R⦄
  证明: by
  -- Split into `add` and `mul` functions and properties.
  rcases inst₁ with @⟨⟨⟩, ⟨⟩⟩
  rcases inst₂ with @⟨⟨⟩, ⟨⟩⟩
  -- Prove equality of parts using function extensionality.
  congr
-/
@[ext] theorem ext ⦃inst₁ inst₂ : Distrib R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `add` and `mul` functions and properties.
  rcases inst₁ with @⟨⟨⟩, ⟨⟩⟩
  rcases inst₂ with @⟨⟨⟩, ⟨⟩⟩
  -- Prove equality of parts using function extensionality.
  congr

end Distrib

/-! ### NonUnitalNonAssocSemiring -/
namespace NonUnitalNonAssocSemiring

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: NonUnitalNonAssocSemiring R⦄
  proof: by
  -- Split into `AddMonoid` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩
  rcases inst₂ with @⟨_, ⟨⟩⟩
  -- Prove equality of parts using already-proved extensionality lemmas.
  congr; ext : 1; assumption

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: NonUnitalNonAssocSemiring R⦄
  证明: by
  -- Split into `AddMonoid` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩
  rcases inst₂ with @⟨_, ⟨⟩⟩
  -- Prove equality of parts using already-proved extensionality lemmas.
  congr; ext : 1; assumption
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `AddMonoid` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩
  rcases inst₂ with @⟨_, ⟨⟩⟩
  -- Prove equality of parts using already-proved extensionality lemmas.
  congr; ext : 1; assumption

/--
theorem `toDistrib_injective` / 定理 `toDistrib_injective`

English:
theorem toDistrib_injective
  statement: Function.Injective (@toDistrib R)
  proof: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

中文:
定理 toDistrib_injective
  结论: Function.Injective (@toDistrib R)
  证明: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, MorphismProperty, MorphismProperty.pullback_snd, QuasiCompact, f.fiberToSpecResidueField, fiberToSpecResidueField, iff_of_isAffine, pullback_snd, toAdd.add, toMul.mul
-/
theorem toDistrib_injective : Function.Injective (@toDistrib R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end NonUnitalNonAssocSemiring

/-! ### NonUnitalSemiring -/
namespace NonUnitalSemiring

/--
theorem `toNonUnitalNonAssocSemiring_injective` / 定理 `toNonUnitalNonAssocSemiring_injective`

English:
theorem toNonUnitalNonAssocSemiring_injective
  proof: by
  rintro ⟨⟩ ⟨⟩ _; congr

中文:
定理 toNonUnitalNonAssocSemiring_injective
  证明: by
  rintro ⟨⟩ ⟨⟩ _; congr
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: NonUnitalSemiring R⦄
  proof: toNonUnitalNonAssocSemiring_injective
    NonUnitalNonAssocSemiring.ext h_add h_mul

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: NonUnitalSemiring R⦄
  证明: toNonUnitalNonAssocSemiring_injective
    NonUnitalNonAssocSemiring.ext h_add h_mul

Depends on / 依赖: IsAffineHom, MorphismProperty, MorphismProperty.pullback_snd, f.fiberToSpecResidueField, fiberToSpecResidueField, isAffine_of_isAffineHom, pullback_snd
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
toNonUnitalNonAssocSemiring_injective
    NonUnitalNonAssocSemiring.ext h_add h_mul

end NonUnitalSemiring

/--
theorem `AddMonoidWithOne.ext` / 定理 `AddMonoidWithOne.ext`

English:
theorem AddMonoidWithOne.ext
  given: ⦃inst₁ inst₂
  statement: AddMonoidWithOne R⦄
  proof: by
  have h_monoid : inst₁.toAddMonoid = inst₂.toAddMonoid := by ext : 1; exact h_add
  have h_zero' : inst₁.toZero = inst₂.toZero := congrArg (·.toZero) h_monoid
  have h_one' : inst₁.toOne = inst₂.toOne :=
    congrArg One.mk h_one
  have h_natCast : inst₁.toNatCast.natCast = inst₂.toNatCast.natCa

中文:
定理 AddMonoidWithOne.ext
  条件: ⦃inst₁ inst₂
  结论: AddMonoidWithOne R⦄
  证明: by
  have h_monoid : inst₁.toAddMonoid = inst₂.toAddMonoid := by ext : 1; exact h_add
  have h_zero' : inst₁.toZero = inst₂.toZero := congrArg (·.toZero) h_monoid
  have h_one' : inst₁.toOne = inst₂.toOne :=
    congrArg One.mk h_one
  have h_natCast : inst₁.toNatCast.natCast = inst₂.toNatCast.natCa

Depends on / 依赖: LocallyOfFiniteType, LocallyOfFiniteType.jacobsonSpace, MorphismProperty, MorphismProperty.pullback_snd, f.fiberToSpecResidueField, fiberToSpecResidueField, jacobsonSpace, pullback_snd
-/
@[ext] theorem AddMonoidWithOne.ext ⦃inst₁ inst₂ : AddMonoidWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one : R)) :
    inst₁ = inst₂ := by
  have h_monoid : inst₁.toAddMonoid = inst₂.toAddMonoid := by ext : 1; exact h_add
  have h_zero' : inst₁.toZero = inst₂.toZero := congrArg (·.toZero) h_monoid
  have h_one' : inst₁.toOne = inst₂.toOne :=
    congrArg One.mk h_one
  have h_natCast : inst₁.toNatCast.natCast = inst₂.toNatCast.natCast := by
    funext n; induction n with
    | zero => rewrite [inst₁.natCast_zero, inst₂.natCast_zero]
              exact congrArg (@Zero.zero R) h_zero'
    | succ n h => rw [inst₁.natCast_succ, inst₂.natCast_succ, h_add]
                  exact congrArg₂ _ h h_one
  rcases inst₁ with @⟨⟨⟩⟩; rcases inst₂ with @⟨⟨⟩⟩
  congr

/--
theorem `AddCommMonoidWithOne.toAddMonoidWithOne_injective` / 定理 `AddCommMonoidWithOne.toAddMonoidWithOne_injective`

English:
theorem AddCommMonoidWithOne.toAddMonoidWithOne_injective
  proof: by
  rintro ⟨⟩ ⟨⟩ _; congr

中文:
定理 AddCommMonoidWithOne.toAddMonoidWithOne_injective
  证明: by
  rintro ⟨⟩ ⟨⟩ _; congr
-/
theorem AddCommMonoidWithOne.toAddMonoidWithOne_injective :
    Function.Injective (@AddCommMonoidWithOne.toAddMonoidWithOne R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
theorem `AddCommMonoidWithOne.ext` / 定理 `AddCommMonoidWithOne.ext`

English:
theorem AddCommMonoidWithOne.ext
  given: ⦃inst₁ inst₂
  statement: AddCommMonoidWithOne R⦄
  proof: AddCommMonoidWithOne.toAddMonoidWithOne_injective
    AddMonoidWithOne.ext h_add h_one

中文:
定理 AddCommMonoidWithOne.ext
  条件: ⦃inst₁ inst₂
  结论: AddCommMonoidWithOne R⦄
  证明: AddCommMonoidWithOne.toAddMonoidWithOne_injective
    AddMonoidWithOne.ext h_add h_one
-/
@[ext] theorem AddCommMonoidWithOne.ext ⦃inst₁ inst₂ : AddCommMonoidWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one : R)) :
    inst₁ = inst₂ :=
AddCommMonoidWithOne.toAddMonoidWithOne_injective
    AddMonoidWithOne.ext h_add h_one

namespace NonAssocSemiring

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: NonAssocSemiring R⦄
  proof: by
  have h : inst₁.toNonUnitalNonAssocSemiring = inst₂.toNonUnitalNonAssocSemiring := by
    ext : 1 <;> assumption
  have h_zero : (inst₁.toMulZeroClass).toZero.zero = (inst₂.toMulZeroClass).toZero.zero :=
    congrArg (fun inst => (inst.toMulZeroClass).toZero.zero) h
  have h_one' : (inst₁.toMulZ

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: NonAssocSemiring R⦄
  证明: by
  have h : inst₁.toNonUnitalNonAssocSemiring = inst₂.toNonUnitalNonAssocSemiring := by
    ext : 1 <;> assumption
  have h_zero : (inst₁.toMulZeroClass).toZero.zero = (inst₂.toMulZeroClass).toZero.zero :=
    congrArg (fun inst => (inst.toMulZeroClass).toZero.zero) h
  have h_one' : (inst₁.toMulZ
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonAssocSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have h : inst₁.toNonUnitalNonAssocSemiring = inst₂.toNonUnitalNonAssocSemiring := by
    ext : 1 <;> assumption
  have h_zero : (inst₁.toMulZeroClass).toZero.zero = (inst₂.toMulZeroClass).toZero.zero :=
    congrArg (fun inst => (inst.toMulZeroClass).toZero.zero) h
  have h_one' : (inst₁.toMulZeroOneClass).toMulOneClass.toOne
                = (inst₂.toMulZeroOneClass).toMulOneClass.toOne := by
    congr 2; ext : 1; exact h_mul
  have h_one : (inst₁.toMulZeroOneClass).toMulOneClass.toOne.one
               = (inst₂.toMulZeroOneClass).toMulOneClass.toOne.one :=
    congrArg (@One.one R) h_one'
  have : inst₁.toAddCommMonoidWithOne = inst₂.toAddCommMonoidWithOne := by
    ext : 1 <;> assumption
  have : inst₁.toNatCast = inst₂.toNatCast :=
    congrArg (·.toNatCast) this
  -- Split into `NonUnitalNonAssocSemiring`, `One` and `natCast` instances.
  cases inst₁; cases inst₂
  congr

/--
theorem `toNonUnitalNonAssocSemiring_injective` / 定理 `toNonUnitalNonAssocSemiring_injective`

English:
theorem toNonUnitalNonAssocSemiring_injective
  proof: by
  intro _ _ _
  ext <;> congr

中文:
定理 toNonUnitalNonAssocSemiring_injective
  证明: by
  intro _ _ _
  ext <;> congr
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ _
  ext <;> congr

end NonAssocSemiring

/-! ### NonUnitalNonAssocRing -/
namespace NonUnitalNonAssocRing

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: NonUnitalNonAssocRing R⦄
  proof: by
  -- Split into `AddCommGroup` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩; rcases inst₂ with @⟨_, ⟨⟩⟩
  congr; (ext : 1; assumption)

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: NonUnitalNonAssocRing R⦄
  证明: by
  -- Split into `AddCommGroup` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩; rcases inst₂ with @⟨_, ⟨⟩⟩
  congr; (ext : 1; assumption)
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `AddCommGroup` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩; rcases inst₂ with @⟨_, ⟨⟩⟩
  congr; (ext : 1; assumption)

/--
theorem `toNonUnitalNonAssocSemiring_injective` / 定理 `toNonUnitalNonAssocSemiring_injective`

English:
theorem toNonUnitalNonAssocSemiring_injective
  proof: by
  intro _ _ h
  -- Use above extensionality lemma to prove injectivity by showing that `h_add` and `h_mul` hold.
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

中文:
定理 toNonUnitalNonAssocSemiring_injective
  证明: by
  intro _ _ h
  -- Use above extensionality lemma to prove injectivity by showing that `h_add` and `h_mul` hold.
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

Depends on / 依赖: IsPreimmersion, asFiberHom, f.asFiberHom, f.asFiberHom_fiber, f.fiber, of_comp
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ h
  -- Use above extensionality lemma to prove injectivity by showing that `h_add` and `h_mul` hold.
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end NonUnitalNonAssocRing

/-! ### NonUnitalRing -/
namespace NonUnitalRing

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: NonUnitalRing R⦄
  proof: by
  have : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: NonUnitalRing R⦄
  证明: by
  have : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr

/--
theorem `toNonUnitalSemiring_injective` / 定理 `toNonUnitalSemiring_injective`

English:
theorem toNonUnitalSemiring_injective
  proof: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

中文:
定理 toNonUnitalSemiring_injective
  证明: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

Depends on / 依赖: toAdd.add, toMul.mul
-/
theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

/--
theorem `toNonUnitalNonAssocring_injective` / 定理 `toNonUnitalNonAssocring_injective`

English:
theorem toNonUnitalNonAssocring_injective
  proof: by
  intro _ _ _
  ext <;> congr

中文:
定理 toNonUnitalNonAssocring_injective
  证明: by
  intro _ _ _
  ext <;> congr
-/
theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

end NonUnitalRing

/--
theorem `AddGroupWithOne.ext` / 定理 `AddGroupWithOne.ext`

English:
theorem AddGroupWithOne.ext
  given: ⦃inst₁ inst₂
  statement: AddGroupWithOne R⦄
  proof: by
  have : inst₁.toAddMonoidWithOne = inst₂.toAddMonoidWithOne :=
    AddMonoidWithOne.ext h_add h_one
  have : inst₁.toNatCast = inst₂.toNatCast := congrArg (·.toNatCast) this
  have h_group : inst₁.toAddGroup = inst₂.toAddGroup := by ext : 1; exact h_add
  -- Extract equality of necessary substru

中文:
定理 AddGroupWithOne.ext
  条件: ⦃inst₁ inst₂
  结论: AddGroupWithOne R⦄
  证明: by
  have : inst₁.toAddMonoidWithOne = inst₂.toAddMonoidWithOne :=
    AddMonoidWithOne.ext h_add h_one
  have : inst₁.toNatCast = inst₂.toNatCast := congrArg (·.toNatCast) this
  have h_group : inst₁.toAddGroup = inst₂.toAddGroup := by ext : 1; exact h_add
  -- Extract equality of necessary substru
-/
@[ext] theorem AddGroupWithOne.ext ⦃inst₁ inst₂ : AddGroupWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one)) :
    inst₁ = inst₂ := by
  have : inst₁.toAddMonoidWithOne = inst₂.toAddMonoidWithOne :=
    AddMonoidWithOne.ext h_add h_one
  have : inst₁.toNatCast = inst₂.toNatCast := congrArg (·.toNatCast) this
  have h_group : inst₁.toAddGroup = inst₂.toAddGroup := by ext : 1; exact h_add
  -- Extract equality of necessary substructures from h_group
  injection h_group with h_group; injection h_group
  have : inst₁.toIntCast.intCast = inst₂.toIntCast.intCast := by
    funext n; cases n with
    | ofNat n => rewrite [Int.ofNat_eq_natCast, inst₁.intCast_ofNat, inst₂.intCast_ofNat]; congr
    | negSucc n => rewrite [inst₁.intCast_negSucc, inst₂.intCast_negSucc]; congr
  rcases inst₁ with @⟨⟨⟩⟩; rcases inst₂ with @⟨⟨⟩⟩
  congr

/--
theorem `AddCommGroupWithOne.ext` / 定理 `AddCommGroupWithOne.ext`

English:
theorem AddCommGroupWithOne.ext
  given: ⦃inst₁ inst₂
  statement: AddCommGroupWithOne R⦄
  proof: by
  have : inst₁.toAddCommGroup = inst₂.toAddCommGroup :=
    AddCommGroup.ext h_add
  have : inst₁.toAddGroupWithOne = inst₂.toAddGroupWithOne :=
    AddGroupWithOne.ext h_add h_one
  injection this with _ h_addMonoidWithOne; injection h_addMonoidWithOne
  cases inst₁; cases inst₂
  congr

中文:
定理 AddCommGroupWithOne.ext
  条件: ⦃inst₁ inst₂
  结论: AddCommGroupWithOne R⦄
  证明: by
  have : inst₁.toAddCommGroup = inst₂.toAddCommGroup :=
    AddCommGroup.ext h_add
  have : inst₁.toAddGroupWithOne = inst₂.toAddGroupWithOne :=
    AddGroupWithOne.ext h_add h_one
  injection this with _ h_addMonoidWithOne; injection h_addMonoidWithOne
  cases inst₁; cases inst₂
  congr
-/
@[ext] theorem AddCommGroupWithOne.ext ⦃inst₁ inst₂ : AddCommGroupWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one)) :
    inst₁ = inst₂ := by
  have : inst₁.toAddCommGroup = inst₂.toAddCommGroup :=
    AddCommGroup.ext h_add
  have : inst₁.toAddGroupWithOne = inst₂.toAddGroupWithOne :=
    AddGroupWithOne.ext h_add h_one
  injection this with _ h_addMonoidWithOne; injection h_addMonoidWithOne
  cases inst₁; cases inst₂
  congr

namespace NonAssocRing

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: NonAssocRing R⦄
  proof: by
  have h₁ : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext : 1 <;> assumption
  -- Mathematically non-trivial fact: `intCast` is determined by the rest.
  have h₃ : inst₁.

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: NonAssocRing R⦄
  证明: by
  have h₁ : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext : 1 <;> assumption
  -- Mathematically non-trivial fact: `intCast` is determined by the rest.
  have h₃ : inst₁.
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonAssocRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have h₁ : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext : 1 <;> assumption
  -- Mathematically non-trivial fact: `intCast` is determined by the rest.
  have h₃ : inst₁.toAddCommGroupWithOne = inst₂.toAddCommGroupWithOne :=
    AddCommGroupWithOne.ext h_add (congrArg (·.toOne.one) h₂)
  cases inst₁; cases inst₂
  congr <;> solve | injection h₁ | injection h₂ | injection h₃

/--
theorem `toNonAssocSemiring_injective` / 定理 `toNonAssocSemiring_injective`

English:
theorem toNonAssocSemiring_injective
  proof: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

中文:
定理 toNonAssocSemiring_injective
  证明: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

Depends on / 依赖: toAdd.add, toMul.mul
-/
theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

/--
theorem `toNonUnitalNonAssocring_injective` / 定理 `toNonUnitalNonAssocring_injective`

English:
theorem toNonUnitalNonAssocring_injective
  proof: by
  intro _ _ _
  ext <;> congr

中文:
定理 toNonUnitalNonAssocring_injective
  证明: by
  intro _ _ _
  ext <;> congr
-/
theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

end NonAssocRing

/-! ### Semiring -/
namespace Semiring

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: Semiring R⦄
  proof: by
  -- Show that enough substructures are equal.
  have h₀ : inst₁.toAddCommMonoid = inst₂.toAddCommMonoid := by
    ext : 1 <;> assumption
  have h₁ : inst₁.toNonUnitalSemiring = inst₂.toNonUnitalSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemir

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: Semiring R⦄
  证明: by
  -- Show that enough substructures are equal.
  have h₀ : inst₁.toAddCommMonoid = inst₂.toAddCommMonoid := by
    ext : 1 <;> assumption
  have h₁ : inst₁.toNonUnitalSemiring = inst₂.toNonUnitalSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemir
-/
@[ext] theorem ext ⦃inst₁ inst₂ : Semiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Show that enough substructures are equal.
  have h₀ : inst₁.toAddCommMonoid = inst₂.toAddCommMonoid := by
    ext : 1 <;> assumption
  have h₁ : inst₁.toNonUnitalSemiring = inst₂.toNonUnitalSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext : 1 <;> assumption
  have h₃ : (inst₁.toMonoidWithZero).toMonoid = (inst₂.toMonoidWithZero).toMonoid := by
    ext : 1; exact h_mul
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve | injection h₁ | injection h₂

/--
theorem `toNonUnitalSemiring_injective` / 定理 `toNonUnitalSemiring_injective`

English:
theorem toNonUnitalSemiring_injective
  proof: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

中文:
定理 toNonUnitalSemiring_injective
  证明: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

Depends on / 依赖: toAdd.add, toMul.mul
-/
theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

/--
theorem `toNonAssocSemiring_injective` / 定理 `toNonAssocSemiring_injective`

English:
theorem toNonAssocSemiring_injective
  proof: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

中文:
定理 toNonAssocSemiring_injective
  证明: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

Depends on / 依赖: toAdd.add, toMul.mul
-/
theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end Semiring

/-! ### Ring -/
namespace Ring

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: Ring R⦄
  proof: by
  -- Show that enough substructures are equal.
  have h₁ : inst₁.toSemiring = inst₂.toSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocRing = inst₂.toNonAssocRing := by
    ext : 1 <;> assumption
  /- We prove that the `SubNegMonoid`s are equal because they are one
  field aw

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: Ring R⦄
  证明: by
  -- Show that enough substructures are equal.
  have h₁ : inst₁.toSemiring = inst₂.toSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocRing = inst₂.toNonAssocRing := by
    ext : 1 <;> assumption
  /- We prove that the `SubNegMonoid`s are equal because they are one
  field aw
-/
@[ext] theorem ext ⦃inst₁ inst₂ : Ring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Show that enough substructures are equal.
  have h₁ : inst₁.toSemiring = inst₂.toSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocRing = inst₂.toNonAssocRing := by
    ext : 1 <;> assumption
  /- We prove that the `SubNegMonoid`s are equal because they are one
  field away from `Sub` and `Neg`, enabling use of `injection`. -/
  have h₃ : (inst₁.toAddCommGroup).toAddGroup.toSubNegMonoid
            = (inst₂.toAddCommGroup).toAddGroup.toSubNegMonoid :=
congrArg (@AddGroup.toSubNegMonoid R) by ext : 1; exact h_add
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve | injection h₂ | injection h₃

/--
theorem `toNonUnitalRing_injective` / 定理 `toNonUnitalRing_injective`

English:
theorem toNonUnitalRing_injective
  proof: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

中文:
定理 toNonUnitalRing_injective
  证明: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

Depends on / 依赖: toAdd.add, toMul.mul
-/
theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

/--
theorem `toNonAssocRing_injective` / 定理 `toNonAssocRing_injective`

English:
theorem toNonAssocRing_injective
  proof: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

中文:
定理 toNonAssocRing_injective
  证明: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

Depends on / 依赖: isIntegral_of_isOpenImmersion, toAdd.add, toMul.mul
-/
theorem toNonAssocRing_injective :
    Function.Injective (@toNonAssocRing R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

/--
theorem `toSemiring_injective` / 定理 `toSemiring_injective`

English:
theorem toSemiring_injective
  proof: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

中文:
定理 toSemiring_injective
  证明: by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

Depends on / 依赖: toAdd.add, toMul.mul
-/
theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end Ring

/-! ### NonUnitalNonAssocCommSemiring -/
namespace NonUnitalNonAssocCommSemiring

/--
theorem `toNonUnitalNonAssocSemiring_injective` / 定理 `toNonUnitalNonAssocSemiring_injective`

English:
theorem toNonUnitalNonAssocSemiring_injective
  proof: by
  rintro ⟨⟩ ⟨⟩ _; congr

中文:
定理 toNonUnitalNonAssocSemiring_injective
  证明: by
  rintro ⟨⟩ ⟨⟩ _; congr
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: NonUnitalNonAssocCommSemiring R⦄
  proof: toNonUnitalNonAssocSemiring_injective
    NonUnitalNonAssocSemiring.ext h_add h_mul

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: NonUnitalNonAssocCommSemiring R⦄
  证明: toNonUnitalNonAssocSemiring_injective
    NonUnitalNonAssocSemiring.ext h_add h_mul

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.isAffine_Spec, isAffine_Spec
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocCommSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
toNonUnitalNonAssocSemiring_injective
    NonUnitalNonAssocSemiring.ext h_add h_mul

end NonUnitalNonAssocCommSemiring

/-! ### NonUnitalCommSemiring -/
namespace NonUnitalCommSemiring

/--
theorem `toNonUnitalSemiring_injective` / 定理 `toNonUnitalSemiring_injective`

English:
theorem toNonUnitalSemiring_injective
  proof: by
  rintro ⟨⟩ ⟨⟩ _; congr

中文:
定理 toNonUnitalSemiring_injective
  证明: by
  rintro ⟨⟩ ⟨⟩ _; congr
-/
theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: NonUnitalCommSemiring R⦄
  proof: toNonUnitalSemiring_injective
    NonUnitalSemiring.ext h_add h_mul

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: NonUnitalCommSemiring R⦄
  证明: toNonUnitalSemiring_injective
    NonUnitalSemiring.ext h_add h_mul
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalCommSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
toNonUnitalSemiring_injective
    NonUnitalSemiring.ext h_add h_mul

end NonUnitalCommSemiring

-- At present, there is no `NonAssocCommSemiring` in Mathlib.

/-! ### NonUnitalNonAssocCommRing -/
namespace NonUnitalNonAssocCommRing

/--
theorem `toNonUnitalNonAssocRing_injective` / 定理 `toNonUnitalNonAssocRing_injective`

English:
theorem toNonUnitalNonAssocRing_injective
  proof: by
  rintro ⟨⟩ ⟨⟩ _; congr

中文:
定理 toNonUnitalNonAssocRing_injective
  证明: by
  rintro ⟨⟩ ⟨⟩ _; congr
-/
theorem toNonUnitalNonAssocRing_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: NonUnitalNonAssocCommRing R⦄
  proof: toNonUnitalNonAssocRing_injective
    NonUnitalNonAssocRing.ext h_add h_mul

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: NonUnitalNonAssocCommRing R⦄
  证明: toNonUnitalNonAssocRing_injective
    NonUnitalNonAssocRing.ext h_add h_mul
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocCommRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
toNonUnitalNonAssocRing_injective
    NonUnitalNonAssocRing.ext h_add h_mul

end NonUnitalNonAssocCommRing

/-! ### NonUnitalCommRing -/
namespace NonUnitalCommRing

/--
theorem `toNonUnitalRing_injective` / 定理 `toNonUnitalRing_injective`

English:
theorem toNonUnitalRing_injective
  proof: by
  rintro ⟨⟩ ⟨⟩ _; congr

中文:
定理 toNonUnitalRing_injective
  证明: by
  rintro ⟨⟩ ⟨⟩ _; congr
-/
theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: NonUnitalCommRing R⦄
  proof: toNonUnitalRing_injective
    NonUnitalRing.ext h_add h_mul

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: NonUnitalCommRing R⦄
  证明: toNonUnitalRing_injective
    NonUnitalRing.ext h_add h_mul
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalCommRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
toNonUnitalRing_injective
    NonUnitalRing.ext h_add h_mul

end NonUnitalCommRing

-- At present, there is no `NonAssocCommRing` in Mathlib.

/-! ### CommSemiring -/
namespace CommSemiring

/--
theorem `toSemiring_injective` / 定理 `toSemiring_injective`

English:
theorem toSemiring_injective
  proof: by
  rintro ⟨⟩ ⟨⟩ _; congr

中文:
定理 toSemiring_injective
  证明: by
  rintro ⟨⟩ ⟨⟩ _; congr
-/
theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: CommSemiring R⦄
  proof: toSemiring_injective
    Semiring.ext h_add h_mul

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: CommSemiring R⦄
  证明: toSemiring_injective
    Semiring.ext h_add h_mul
-/
@[ext] theorem ext ⦃inst₁ inst₂ : CommSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
toSemiring_injective
    Semiring.ext h_add h_mul

end CommSemiring

/-! ### CommRing -/
namespace CommRing

/--
theorem `toRing_injective` / 定理 `toRing_injective`

English:
theorem toRing_injective
  statement: Function.Injective (@toRing R)
  proof: by
  rintro ⟨⟩ ⟨⟩ _; congr

中文:
定理 toRing_injective
  结论: Function.Injective (@toRing R)
  证明: by
  rintro ⟨⟩ ⟨⟩ _; congr
-/
theorem toRing_injective : Function.Injective (@toRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃inst₁ inst₂
  statement: CommRing R⦄
  proof: toRing_injective Ring.ext h_add h_mul

中文:
定理 ext
  条件: ⦃inst₁ inst₂
  结论: CommRing R⦄
  证明: toRing_injective Ring.ext h_add h_mul
-/
@[ext] theorem ext ⦃inst₁ inst₂ : CommRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
toRing_injective Ring.ext h_add h_mul

end CommRing
