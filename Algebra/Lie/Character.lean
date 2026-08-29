/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Characters of Lie algebras

A character of a Lie algebra `L` over a commutative ring `R` is a morphism of Lie algebras `L → R`,
where `R` is regarded as a Lie algebra over itself via the ring commutator. For an Abelian Lie
algebra (e.g., a Cartan subalgebra of a semisimple Lie algebra) a character is just a linear form.

## Main definitions

  * `LieAlgebra.LieCharacter`
  * `LieAlgebra.lieCharacterEquivLinearDual`

## Tags

lie algebra, lie character
-/

@[expose] public section


universe u v w w₁

namespace LieAlgebra

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
attribute [local instance 100] LieRing.ofAssociativeRing

/--
Definition of `LieCharacter` / `LieCharacter` 的定义

English:
abbreviation LieCharacter
  body: L ->ₗ⁅R⁆ R

中文:
缩写 LieCharacter
  定义体: L ->ₗ⁅R⁆ R
-/
abbrev LieCharacter :=
  L ->ₗ⁅R⁆ R

variable {R L}

/--
theorem `lieCharacter_apply_lie` / 定理 `lieCharacter_apply_lie`

English:
theorem lieCharacter_apply_lie
  given: (χ : LieCharacter R L) (x y : L)
  statement: χ ⁅x, y⁆ = 0
  proof: by
  rw [LieHom.map_lie]; rw [LieRing.of_associative_ring_bracket]; rw [mul_comm]; rw [sub_self]

@[simp]

中文:
定理 lieCharacter_apply_lie
  条件: (χ : LieCharacter R L) (x y : L)
  结论: χ ⁅x, y⁆ = 0
  证明: by
  rw [LieHom.map_lie]; rw [LieRing.of_associative_ring_bracket]; rw [mul_comm]; rw [sub_self]

@[simp]

Depends on / 依赖: LieHom, LieHom.map_lie, LieRing, LieRing.of_associative_ring_bracket, map_lie, mul_comm, of_associative_ring_bracket, sub_self
-/
theorem lieCharacter_apply_lie (χ : LieCharacter R L) (x y : L) : χ ⁅x, y⁆ = 0 := by
  rw [LieHom.map_lie]; rw [LieRing.of_associative_ring_bracket]; rw [mul_comm]; rw [sub_self]

@[simp]
/--
theorem `lieCharacter_apply_lie'` / 定理 `lieCharacter_apply_lie'`

English:
theorem lieCharacter_apply_lie'
  given: (χ : LieCharacter R L) (x y : L)
  statement: ⁅χ x, χ y⁆ = 0
  proof: by
  rw [LieRing.of_associative_ring_bracket]; rw [mul_comm]; rw [sub_self]

中文:
定理 lieCharacter_apply_lie'
  条件: (χ : LieCharacter R L) (x y : L)
  结论: ⁅χ x, χ y⁆ = 0
  证明: by
  rw [LieRing.of_associative_ring_bracket]; rw [mul_comm]; rw [sub_self]

Depends on / 依赖: LieRing, LieRing.of_associative_ring_bracket, mul_comm, of_associative_ring_bracket, sub_self
-/
theorem lieCharacter_apply_lie' (χ : LieCharacter R L) (x y : L) : ⁅χ x, χ y⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket]; rw [mul_comm]; rw [sub_self]

/--
theorem `lieCharacter_apply_of_mem_derived` / 定理 `lieCharacter_apply_of_mem_derived`

English:
theorem lieCharacter_apply_of_mem_derived
  statement: (χ : LieCharacter R L) {x : L}
  proof: by
  rw [derivedSeries_def]; rw [derivedSeriesOfIdeal_succ]; rw [derivedSeriesOfIdeal_zero]; rw [←
    LieSubmodule.mem_toSubmodule]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span] at h
  induction h using Submodule.span_induction with
  | mem y h =>
    simp only [Subtype.exists, LieSubmodule.mem_top, exists_const, Set.mem_ofPred_eq] at h
    obtain ⟨z, w, rfl⟩ := h
    exact lieCharacter_apply_lie ..
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul t y _ hy => rw [map_smul, hy, smul_zero]

中文:
定理 lieCharacter_apply_of_mem_derived
  结论: (χ : LieCharacter R L) {x : L}
  证明: by
  rw [derivedSeries_def]; rw [derivedSeriesOfIdeal_succ]; rw [derivedSeriesOfIdeal_zero]; rw [←
    LieSubmodule.mem_toSubmodule]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span] at h
  induction h using Submodule.span_induction with
  | mem y h =>
    simp only [Subtype.exists, LieSubmodule.mem_top, exists_const, Set.mem_ofPred_eq] at h
    obtain ⟨z, w, rfl⟩ := h
    exact lieCharacter_apply_lie ..
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul t y _ hy => rw [map_smul, hy, smul_zero]

Depends on / 依赖: LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top, Set.mem_ofPred_eq, Submodule, Submodule.span_induction, Subtype, Subtype.exists, add_zero, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, derivedSeries_def, exists_const, lieCharacter_apply_lie, lieIdeal_oper_eq_linear_span, map_add, map_smul, map_zero, mem_ofPred_eq
-/
theorem lieCharacter_apply_of_mem_derived (χ : LieCharacter R L) {x : L}
    (h : x in derivedSeries R L 1) : χ x = 0 := by
  rw [derivedSeries_def]; rw [derivedSeriesOfIdeal_succ]; rw [derivedSeriesOfIdeal_zero]; rw [←
    LieSubmodule.mem_toSubmodule]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span] at h
  induction h using Submodule.span_induction with
  | mem y h =>
    simp only [Subtype.exists, LieSubmodule.mem_top, exists_const, Set.mem_ofPred_eq] at h
    obtain ⟨z, w, rfl⟩ := h
    exact lieCharacter_apply_lie ..
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul t y _ hy => rw [map_smul, hy, smul_zero]

/-- For an Abelian Lie algebra, characters are just linear forms. -/
@[simps! apply symm_apply]
/--
Definition of `lieCharacterEquivLinearDual` / `lieCharacterEquivLinearDual` 的定义

English:
definition lieCharacterEquivLinearDual
  signature: [IsLieAbelian L]
  body: (χ : L ->ₗ[R] R)
  invFun ψ :=
    { ψ with
      map_lie' := fun {x y} => by
        rw [LieModule.IsTrivial.trivial]; rw [LieRing.of_associative_ring_bracket]; rw [mul_comm]; rw [sub_self]; rw [LinearMap.toFun_eq_coe]; rw [map_zero] }

中文:
定义 lieCharacterEquivLinearDual
  签名: [IsLieAbelian L]
  定义体: (χ : L ->ₗ[R] R)
  invFun ψ :=
    { ψ with
      map_lie' := fun {x y} => by
        rw [LieModule.IsTrivial.trivial]; rw [LieRing.of_associative_ring_bracket]; rw [mul_comm]; rw [sub_self]; rw [LinearMap.toFun_eq_coe]; rw [map_zero] }
-/
def lieCharacterEquivLinearDual [IsLieAbelian L] : LieCharacter R L ≃ Module.Dual R L where
  toFun χ := (χ : L ->ₗ[R] R)
  invFun ψ :=
    { ψ with
      map_lie' := fun {x y} => by
        rw [LieModule.IsTrivial.trivial]; rw [LieRing.of_associative_ring_bracket]; rw [mul_comm]; rw [sub_self]; rw [LinearMap.toFun_eq_coe]; rw [map_zero] }

end LieAlgebra
