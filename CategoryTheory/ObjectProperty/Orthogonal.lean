/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Orthogonal of a property of objects

Let `P` be a property of objects in a category with zero morphisms.
We define `P.rightOrthogonal` as the property of objects `Y` such that
any map `f : X ⟶ Y` vanishes when `P X` holds. Similarly, we define
`P.leftOrthogonal` as the property of objects `X` such that
any map `f : X ⟶ Y` vanishes when `P Y` holds.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- In a category with zero morphisms, the right orthogonal of a property of objects `P`
is the property of objects `Y` such that any map `X ⟶ Y` vanishes when `P X` holds. -/
@[stacks 0FXB]
/--
Definition of `rightOrthogonal` / `rightOrthogonal` 的定义

English:
definition rightOrthogonal
  signature: : ObjectProperty C
  body: fun Y => forall ⦃X : C⦄ (f : X ⟶ Y), P X -> f = 0

中文:
定义 rightOrthogonal
  签名: : Object命题erty C
  定义体: fun Y => forall ⦃X : C⦄ (f : X ⟶ Y), P X -> f = 0
-/
def rightOrthogonal : ObjectProperty C :=
  fun Y => forall ⦃X : C⦄ (f : X ⟶ Y), P X -> f = 0

/--
lemma `rightOrthogonal_iff` / 引理 `rightOrthogonal_iff`

English:
lemma rightOrthogonal_iff
  given: (Y : C)
  proof: Iff.rfl

中文:
引理 rightOrthogonal_iff
  条件: (Y : C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma rightOrthogonal_iff (Y : C) :
    P.rightOrthogonal Y ↔ forall ⦃X : C⦄ (f : X ⟶ Y), P X -> f = 0 := Iff.rfl

/-- In a category with zero morphisms, the left orthogonal of a property of objects `P`
is the property of objects `X` such that any map `X ⟶ Y` vanishes when `P Y` holds. -/
@[stacks 0FXB]
/--
Definition of `leftOrthogonal` / `leftOrthogonal` 的定义

English:
definition leftOrthogonal
  signature: : ObjectProperty C
  body: fun X => forall ⦃Y : C⦄ (f : X ⟶ Y), P Y -> f = 0

中文:
定义 leftOrthogonal
  签名: : Object命题erty C
  定义体: fun X => forall ⦃Y : C⦄ (f : X ⟶ Y), P Y -> f = 0
-/
def leftOrthogonal : ObjectProperty C :=
  fun X => forall ⦃Y : C⦄ (f : X ⟶ Y), P Y -> f = 0

/--
lemma `leftOrthogonal_iff` / 引理 `leftOrthogonal_iff`

English:
lemma leftOrthogonal_iff
  given: (X : C)
  proof: Iff.rfl

中文:
引理 leftOrthogonal_iff
  条件: (X : C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma leftOrthogonal_iff (X : C) :
    P.leftOrthogonal X ↔ forall ⦃Y : C⦄ (f : X ⟶ Y), P Y -> f = 0 := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.rightOrthogonal.IsClosedUnderIsomorphisms
  body: by
    rw [← cancel_mono e.inv]; rw [zero_comp]
    exact h _ hX

中文:
实例 :
  签名: P.rightOrthogonal.IsClosedUnderIsomorphisms
  定义体: by
    rw [← cancel_mono e.inv]; rw [zero_comp]
    exact h _ hX

Depends on / 依赖: cancel_mono, e.inv, zero_comp
-/
instance : P.rightOrthogonal.IsClosedUnderIsomorphisms where
  of_iso e h X f hX := by
    rw [← cancel_mono e.inv]; rw [zero_comp]
    exact h _ hX

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.leftOrthogonal.IsClosedUnderIsomorphisms
  body: by
    rw [← cancel_epi e.hom]; rw [comp_zero]
    exact h _ hY

中文:
实例 :
  签名: P.leftOrthogonal.IsClosedUnderIsomorphisms
  定义体: by
    rw [← cancel_epi e.hom]; rw [comp_zero]
    exact h _ hY

Depends on / 依赖: cancel_epi, comp_zero, e.hom
-/
instance : P.leftOrthogonal.IsClosedUnderIsomorphisms where
  of_iso e h Y f hY := by
    rw [← cancel_epi e.hom]; rw [comp_zero]
    exact h _ hY

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : P.rightOrthogonal.ContainsZero where
  body: ⟨0, isZero_zero _, fun _ _ _ => by ext⟩

中文:
实例 [HasZeroObject
  签名: C] : P.rightOrthogonal.ContainsZero where
  定义体: ⟨0, isZero_zero _, fun _ _ _ => by ext⟩

Depends on / 依赖: isZero_zero
-/
instance [HasZeroObject C] : P.rightOrthogonal.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun _ _ _ => by ext⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : P.leftOrthogonal.ContainsZero where
  body: ⟨0, isZero_zero _, fun _ _ _ => by ext⟩

中文:
实例 [HasZeroObject
  签名: C] : P.leftOrthogonal.ContainsZero where
  定义体: ⟨0, isZero_zero _, fun _ _ _ => by ext⟩

Depends on / 依赖: isZero_zero
-/
instance [HasZeroObject C] : P.leftOrthogonal.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun _ _ _ => by ext⟩

end ObjectProperty

end CategoryTheory
