/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.SetTheory.Cardinal.Free

import Mathlib.Algebra.MonoidAlgebra.Cardinal

/-!
# Cardinality of free algebras

This file contains some results about the cardinality of `FreeAlgebra`,
parallel to that of `MvPolynomial`.
-/

public section

universe u v

variable (R : Type u) [CommSemiring R]

open Cardinal

namespace FreeAlgebra

variable (X : Type v)

@[simp]
/--
theorem `cardinalMk_eq_max_lift` / 定理 `cardinalMk_eq_max_lift`

English:
theorem cardinalMk_eq_max_lift
  given: [Nonempty X] [Nontrivial R]
  proof: by
  have hX := mk_freeMonoid X
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq]; rw [MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite]; rw [hX]; rw [lift_max]; rw [lift_aleph0]; rw [sup_assoc]

@[simp]

中文:
定理 cardinalMk_eq_max_lift
  条件: [非空 X] [非平凡 R]
  证明: by
  have hX := mk_freeMonoid X
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq]; rw [MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite]; rw [hX]; rw [lift_max]; rw [lift_aleph0]; rw [sup_assoc]

@[simp]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite, cardinalMk_eq_max_lift_of_infinite, cardinal_eq, equivMonoidAlgebraFreeMonoid, equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, lift_aleph0, lift_max, mk_freeMonoid, sup_assoc, toEquiv
-/
theorem cardinalMk_eq_max_lift [Nonempty X] [Nontrivial R] :
    #(FreeAlgebra R X) = Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀ := by
  have hX := mk_freeMonoid X
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq]; rw [MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite]; rw [hX]; rw [lift_max]; rw [lift_aleph0]; rw [sup_assoc]

@[simp]
/--
theorem `cardinalMk_eq_lift` / 定理 `cardinalMk_eq_lift`

English:
theorem cardinalMk_eq_lift
  given: [IsEmpty X]
  statement: #(FreeAlgebra R X) = Cardinal.lift.{v} #R
  proof: by
  simp [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq,
    MonoidAlgebra.cardinalMk_eq_lift_of_fintype]

@[nontriviality]

中文:
定理 cardinalMk_eq_lift
  条件: [是空 X]
  结论: #(FreeAlgebra R X) = 基数.lift.{v} #R
  证明: by
  simp [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq,
    MonoidAlgebra.cardinalMk_eq_lift_of_fintype]

@[nontriviality]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.cardinalMk_eq_lift_of_fintype, cardinalMk_eq_lift_of_fintype, cardinal_eq, equivMonoidAlgebraFreeMonoid, equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, toEquiv
-/
theorem cardinalMk_eq_lift [IsEmpty X] : #(FreeAlgebra R X) = Cardinal.lift.{v} #R := by
  simp [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq,
    MonoidAlgebra.cardinalMk_eq_lift_of_fintype]

@[nontriviality]
/--
theorem `cardinalMk_eq_one` / 定理 `cardinalMk_eq_one`

English:
theorem cardinalMk_eq_one
  given: [Subsingleton R]
  statement: #(FreeAlgebra R X) = 1
  proof: by
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq]; rw [mk_eq_one]

中文:
定理 cardinalMk_eq_one
  条件: [子单例 R]
  结论: #(FreeAlgebra R X) = 1
  证明: by
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq]; rw [mk_eq_one]

Depends on / 依赖: cardinal_eq, equivMonoidAlgebraFreeMonoid, equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, mk_eq_one, toEquiv
-/
theorem cardinalMk_eq_one [Subsingleton R] : #(FreeAlgebra R X) = 1 := by
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq]; rw [mk_eq_one]

/--
theorem `cardinalMk_le_max_lift` / 定理 `cardinalMk_le_max_lift`

English:
theorem cardinalMk_le_max_lift
  proof: by
  cases subsingleton_or_nontrivial R
  · exact (cardinalMk_eq_one R X).trans_le (le_max_of_le_right one_le_aleph0)
  cases isEmpty_or_nonempty X
  · exact (cardinalMk_eq_lift R X).trans_le (le_max_of_le_left <| le_max_left _ _)
  · exact (cardinalMk_eq_max_lift R X).le

中文:
定理 cardinalMk_le_max_lift
  证明: by
  cases subsingleton_or_nontrivial R
  · exact (cardinalMk_eq_one R X).trans_le (le_max_of_le_right one_le_aleph0)
  cases isEmpty_or_nonempty X
  · exact (cardinalMk_eq_lift R X).trans_le (le_max_of_le_left <| le_max_left _ _)
  · exact (cardinalMk_eq_max_lift R X).le

Depends on / 依赖: cardinalMk_eq_lift, cardinalMk_eq_max_lift, cardinalMk_eq_one, isEmpty_or_nonempty, le_max_left, le_max_of_le_left, le_max_of_le_right, one_le_aleph0, subsingleton_or_nontrivial, trans_le
-/
theorem cardinalMk_le_max_lift :
    #(FreeAlgebra R X) <= Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (cardinalMk_eq_one R X).trans_le (le_max_of_le_right one_le_aleph0)
  cases isEmpty_or_nonempty X
  · exact (cardinalMk_eq_lift R X).trans_le (le_max_of_le_left <| le_max_left _ _)
  · exact (cardinalMk_eq_max_lift R X).le

variable (X : Type u)

/--
theorem `cardinalMk_eq_max` / 定理 `cardinalMk_eq_max`

English:
theorem cardinalMk_eq_max
  given: [Nonempty X] [Nontrivial R]
  statement: #(FreeAlgebra R X) = #R ⊔ #X ⊔ ℵ₀
  proof: by
  simp

中文:
定理 cardinalMk_eq_max
  条件: [非空 X] [非平凡 R]
  结论: #(FreeAlgebra R X) = #R ⊔ #X ⊔ ℵ₀
  证明: by
  simp
-/
theorem cardinalMk_eq_max [Nonempty X] [Nontrivial R] : #(FreeAlgebra R X) = #R ⊔ #X ⊔ ℵ₀ := by
  simp

/--
theorem `cardinalMk_eq` / 定理 `cardinalMk_eq`

English:
theorem cardinalMk_eq
  given: [IsEmpty X]
  statement: #(FreeAlgebra R X) = #R
  proof: by
  simp

中文:
定理 cardinalMk_eq
  条件: [是空 X]
  结论: #(FreeAlgebra R X) = #R
  证明: by
  simp
-/
theorem cardinalMk_eq [IsEmpty X] : #(FreeAlgebra R X) = #R := by
  simp

/--
theorem `cardinalMk_le_max` / 定理 `cardinalMk_le_max`

English:
theorem cardinalMk_le_max
  statement: #(FreeAlgebra R X) <= #R ⊔ #X ⊔ ℵ₀
  proof: by
  simpa using cardinalMk_le_max_lift R X

中文:
定理 cardinalMk_le_max
  结论: #(FreeAlgebra R X) <= #R ⊔ #X ⊔ ℵ₀
  证明: by
  simpa using cardinalMk_le_max_lift R X

Depends on / 依赖: cardinalMk_le_max_lift
-/
theorem cardinalMk_le_max : #(FreeAlgebra R X) <= #R ⊔ #X ⊔ ℵ₀ := by
  simpa using cardinalMk_le_max_lift R X

end FreeAlgebra

namespace Algebra

/--
theorem `lift_cardinalMk_adjoin_le` / 定理 `lift_cardinalMk_adjoin_le`

English:
theorem lift_cardinalMk_adjoin_le
  given: {A : Type v} [Semiring A] [Algebra R A] (s : Set A)
  proof: by
  have H := mk_range_le_lift (f := FreeAlgebra.lift R ((↑) : s -> A))
  rw [lift_umax]; rw [lift_id'.{v]; rw [u}] at H
  rw [Algebra.adjoin_eq_range_freeAlgebra_lift]
  exact H.trans (FreeAlgebra.cardinalMk_le_max_lift R s)

中文:
定理 lift_cardinalMk_adjoin_le
  条件: {A : 类型v} [半环 A] [代数 R A] (s : 集合 A)
  证明: by
  have H := mk_range_le_lift (f := FreeAlgebra.lift R ((↑) : s -> A))
  rw [lift_umax]; rw [lift_id'.{v]; rw [u}] at H
  rw [Algebra.adjoin_eq_range_freeAlgebra_lift]
  exact H.trans (FreeAlgebra.cardinalMk_le_max_lift R s)

Depends on / 依赖: Algebra, Algebra.adjoin_eq_range_freeAlgebra_lift, FreeAlgebra, FreeAlgebra.cardinalMk_le_max_lift, FreeAlgebra.lift, H.trans, adjoin_eq_range_freeAlgebra_lift, cardinalMk_le_max_lift, lift_id, lift_umax, mk_range_le_lift
-/
theorem lift_cardinalMk_adjoin_le {A : Type v} [Semiring A] [Algebra R A] (s : Set A) :
    lift.{u} #(adjoin R s) <= lift.{v} #R ⊔ lift.{u} #s ⊔ ℵ₀ := by
  have H := mk_range_le_lift (f := FreeAlgebra.lift R ((↑) : s -> A))
  rw [lift_umax]; rw [lift_id'.{v]; rw [u}] at H
  rw [Algebra.adjoin_eq_range_freeAlgebra_lift]
  exact H.trans (FreeAlgebra.cardinalMk_le_max_lift R s)

/--
theorem `cardinalMk_adjoin_le` / 定理 `cardinalMk_adjoin_le`

English:
theorem cardinalMk_adjoin_le
  given: {A : Type u} [Semiring A] [Algebra R A] (s : Set A)
  proof: by
  simpa using lift_cardinalMk_adjoin_le R s

中文:
定理 cardinalMk_adjoin_le
  条件: {A : 类型u} [半环 A] [代数 R A] (s : 集合 A)
  证明: by
  simpa using lift_cardinalMk_adjoin_le R s

Depends on / 依赖: lift_cardinalMk_adjoin_le
-/
theorem cardinalMk_adjoin_le {A : Type u} [Semiring A] [Algebra R A] (s : Set A) :
    #(adjoin R s) <= #R ⊔ #s ⊔ ℵ₀ := by
  simpa using lift_cardinalMk_adjoin_le R s

end Algebra
