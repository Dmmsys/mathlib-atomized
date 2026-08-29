/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
-/
module

public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Tactic.GRewrite

/-!
# Basic properties of Boolean algebras

This file provides some basic definitions, functions as well as lemmas for functions and type
classes related to Boolean algebras as defined in `Mathlib/Order/BooleanAlgebra/Defs.lean`.

## References

* <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations>
* [*Postulates for Boolean Algebras and Generalized Boolean Algebras*, M.H. Stone][Stone1935]
* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]

## Tags

generalized Boolean algebras, Boolean algebras, lattices, sdiff, compl

-/

public section

universe u v

variable {α : Type u} {β : Type*} {x y z : α}

/-!
### Generalized Boolean algebras

Some of the lemmas in this section are from:

* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]
* <https://ncatlab.org/nlab/show/relative+complement>
* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

-/

-- We might want an `IsCompl_of` predicate (for relative complements) generalizing `IsCompl`,
-- however we'd need another type class for lattices with bot, and all the API for that.
section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

@[simp]
/--
theorem `sup_inf_sdiff` / 定理 `sup_inf_sdiff`

English:
theorem sup_inf_sdiff
  given: (x y : α)
  statement: x ⊓ y ⊔ x \ y = x
  proof: GeneralizedBooleanAlgebra.sup_inf_sdiff _ _

@[simp]

中文:
定理 sup_inf_sdiff
  条件: (x y : α)
  结论: x ⊓ y ⊔ x \ y = x
  证明: GeneralizedBooleanAlgebra.sup_inf_sdiff _ _

@[simp]

Depends on / 依赖: GeneralizedBooleanAlgebra, GeneralizedBooleanAlgebra.sup_inf_sdiff, sup_inf_sdiff
-/
theorem sup_inf_sdiff (x y : α) : x ⊓ y ⊔ x \ y = x :=
  GeneralizedBooleanAlgebra.sup_inf_sdiff _ _

@[simp]
/--
theorem `inf_inf_sdiff` / 定理 `inf_inf_sdiff`

English:
theorem inf_inf_sdiff
  given: (x y : α)
  statement: x ⊓ y ⊓ x \ y = ⊥
  proof: GeneralizedBooleanAlgebra.inf_inf_sdiff _ _

@[simp]

中文:
定理 inf_inf_sdiff
  条件: (x y : α)
  结论: x ⊓ y ⊓ x \ y = ⊥
  证明: GeneralizedBooleanAlgebra.inf_inf_sdiff _ _

@[simp]

Depends on / 依赖: GeneralizedBooleanAlgebra, GeneralizedBooleanAlgebra.inf_inf_sdiff, inf_inf_sdiff
-/
theorem inf_inf_sdiff (x y : α) : x ⊓ y ⊓ x \ y = ⊥ :=
  GeneralizedBooleanAlgebra.inf_inf_sdiff _ _

@[simp]
/--
theorem `sup_sdiff_inf` / 定理 `sup_sdiff_inf`

English:
theorem sup_sdiff_inf
  given: (x y : α)
  statement: x \ y ⊔ x ⊓ y = x
  proof: by rw [sup_comm, sup_inf_sdiff]

@[simp]

中文:
定理 sup_sdiff_inf
  条件: (x y : α)
  结论: x \ y ⊔ x ⊓ y = x
  证明: by rw [sup_comm, sup_inf_sdiff]

@[simp]

Depends on / 依赖: sup_comm, sup_inf_sdiff
-/
theorem sup_sdiff_inf (x y : α) : x \ y ⊔ x ⊓ y = x := by rw [sup_comm, sup_inf_sdiff]

@[simp]
/--
theorem `inf_sdiff_inf` / 定理 `inf_sdiff_inf`

English:
theorem inf_sdiff_inf
  given: (x y : α)
  statement: x \ y ⊓ (x ⊓ y) = ⊥
  proof: by rw [inf_comm, inf_inf_sdiff]

中文:
定理 inf_sdiff_inf
  条件: (x y : α)
  结论: x \ y ⊓ (x ⊓ y) = ⊥
  证明: by rw [inf_comm, inf_inf_sdiff]

Depends on / 依赖: inf_comm, inf_inf_sdiff
-/
theorem inf_sdiff_inf (x y : α) : x \ y ⊓ (x ⊓ y) = ⊥ := by rw [inf_comm, inf_inf_sdiff]

-- see Note [lower instance priority]
instance (priority := 100) GeneralizedBooleanAlgebra.toOrderBot : OrderBot α where
  __ := GeneralizedBooleanAlgebra.toBot
  bot_le a := by
    rw [← inf_inf_sdiff a a]; rw [inf_assoc]
    exact inf_le_left

/--
theorem `disjoint_inf_sdiff` / 定理 `disjoint_inf_sdiff`

English:
theorem disjoint_inf_sdiff
  statement: Disjoint (x ⊓ y) (x \ y)
  proof: disjoint_iff_inf_le.mpr (inf_inf_sdiff x y).le

中文:
定理 disjoint_inf_sdiff
  结论: Disjoint (x ⊓ y) (x \ y)
  证明: disjoint_iff_inf_le.mpr (inf_inf_sdiff x y).le

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, inf_inf_sdiff
-/
theorem disjoint_inf_sdiff : Disjoint (x ⊓ y) (x \ y) :=
  disjoint_iff_inf_le.mpr (inf_inf_sdiff x y).le

-- TODO: in distributive lattices, relative complements are unique when they exist
/--
theorem `sdiff_unique` / 定理 `sdiff_unique`

English:
theorem sdiff_unique
  given: (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥)
  statement: x \ y = z
  proof: by
  conv_rhs at s => rw [← sup_inf_sdiff x y, sup_comm]
  rw [sup_comm] at s
  conv_rhs at i => rw [← inf_inf_sdiff x y, inf_comm]
  rw [inf_comm] at i
  exact (eq_of_inf_eq_sup_eq i s).symm

中文:
定理 sdiff_unique
  条件: (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥)
  结论: x \ y = z
  证明: by
  conv_rhs at s => rw [← sup_inf_sdiff x y, sup_comm]
  rw [sup_comm] at s
  conv_rhs at i => rw [← inf_inf_sdiff x y, inf_comm]
  rw [inf_comm] at i
  exact (eq_of_inf_eq_sup_eq i s).symm

Depends on / 依赖: conv_rhs, eq_of_inf_eq_sup_eq, inf_comm, inf_inf_sdiff, sup_comm, sup_inf_sdiff
-/
theorem sdiff_unique (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \ y = z := by
  conv_rhs at s => rw [← sup_inf_sdiff x y, sup_comm]
  rw [sup_comm] at s
  conv_rhs at i => rw [← inf_inf_sdiff x y, inf_comm]
  rw [inf_comm] at i
  exact (eq_of_inf_eq_sup_eq i s).symm

-- Use `sdiff_le`
/--
theorem `sdiff_le'` / 定理 `sdiff_le'`

English:
theorem sdiff_le'
  statement: x \ y <= x
  proof: calc
    x \ y <= x ⊓ y ⊔ x \ y := le_sup_right
    _ = x := sup_inf_sdiff x y

中文:
定理 sdiff_le'
  结论: x \ y <= x
  证明: calc
    x \ y <= x ⊓ y ⊔ x \ y := le_sup_right
    _ = x := sup_inf_sdiff x y
-/
private theorem sdiff_le' : x \ y <= x :=
  calc
    x \ y <= x ⊓ y ⊔ x \ y := le_sup_right
    _ = x := sup_inf_sdiff x y

set_option backward.privateInPublic true in
-- Use `sdiff_sup_self`
/--
theorem `sdiff_sup_self'` / 定理 `sdiff_sup_self'`

English:
theorem sdiff_sup_self'
  statement: y \ x ⊔ x = y ⊔ x
  proof: calc
    y \ x ⊔ x = y \ x ⊔ (x ⊔ x ⊓ y) := by rw [sup_inf_self]
    _ = y ⊓ x ⊔ y \ x ⊔ x := by ac_rfl
    _ = y ⊔ x := by rw [sup_inf_sdiff]

@[simp]

中文:
定理 sdiff_sup_self'
  结论: y \ x ⊔ x = y ⊔ x
  证明: calc
    y \ x ⊔ x = y \ x ⊔ (x ⊔ x ⊓ y) := by rw [sup_inf_self]
    _ = y ⊓ x ⊔ y \ x ⊔ x := by ac_rfl
    _ = y ⊔ x := by rw [sup_inf_sdiff]

@[simp]
-/
private theorem sdiff_sup_self' : y \ x ⊔ x = y ⊔ x :=
  calc
    y \ x ⊔ x = y \ x ⊔ (x ⊔ x ⊓ y) := by rw [sup_inf_self]
    _ = y ⊓ x ⊔ y \ x ⊔ x := by ac_rfl
    _ = y ⊔ x := by rw [sup_inf_sdiff]

@[simp]
/--
theorem `sdiff_inf_sdiff` / 定理 `sdiff_inf_sdiff`

English:
theorem sdiff_inf_sdiff
  statement: x \ y ⊓ y \ x = ⊥
  proof: Eq.symm
    calc
      ⊥ = x ⊓ (y ⊓ x ⊔ y \ x) ⊓ x \ y := by rw [← inf_inf_sdiff, sup_inf_sdiff]
      _ = (x ⊓ (y ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by rw [inf_sup_left]
      _ = (y ⊓ (x ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by ac_rfl
      _ = x ⊓ y \ x ⊓ x \ y := by
          rw [inf_idem]; rw [inf_sup_right];

中文:
定理 sdiff_inf_sdiff
  结论: x \ y ⊓ y \ x = ⊥
  证明: Eq.symm
    calc
      ⊥ = x ⊓ (y ⊓ x ⊔ y \ x) ⊓ x \ y := by rw [← inf_inf_sdiff, sup_inf_sdiff]
      _ = (x ⊓ (y ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by rw [inf_sup_left]
      _ = (y ⊓ (x ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by ac_rfl
      _ = x ⊓ y \ x ⊓ x \ y := by
          rw [inf_idem]; rw [inf_sup_right];

Depends on / 依赖: Eq.symm, bot_sup_eq, inf_comm, inf_idem, inf_inf_sdiff, inf_of_le_right, inf_sup_left, inf_sup_right, sdiff_le, sup_inf_sdiff
-/
theorem sdiff_inf_sdiff : x \ y ⊓ y \ x = ⊥ :=
Eq.symm
    calc
      ⊥ = x ⊓ (y ⊓ x ⊔ y \ x) ⊓ x \ y := by rw [← inf_inf_sdiff, sup_inf_sdiff]
      _ = (x ⊓ (y ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by rw [inf_sup_left]
      _ = (y ⊓ (x ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y := by ac_rfl
      _ = x ⊓ y \ x ⊓ x \ y := by
          rw [inf_idem]; rw [inf_sup_right]; rw [← inf_comm x y]; rw [inf_inf_sdiff]; rw [bot_sup_eq]
      _ = x ⊓ x \ y ⊓ y \ x := by ac_rfl
      _ = x \ y ⊓ y \ x := by rw [inf_of_le_right sdiff_le']

/--
theorem `disjoint_sdiff_sdiff` / 定理 `disjoint_sdiff_sdiff`

English:
theorem disjoint_sdiff_sdiff
  statement: Disjoint (x \ y) (y \ x)
  proof: disjoint_iff_inf_le.mpr sdiff_inf_sdiff.le

@[simp]

中文:
定理 disjoint_sdiff_sdiff
  结论: Disjoint (x \ y) (y \ x)
  证明: disjoint_iff_inf_le.mpr sdiff_inf_sdiff.le

@[simp]

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, sdiff_inf_sdiff, sdiff_inf_sdiff.le
-/
theorem disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x) :=
  disjoint_iff_inf_le.mpr sdiff_inf_sdiff.le

@[simp]
/--
theorem `inf_sdiff_self_right` / 定理 `inf_sdiff_self_right`

English:
theorem inf_sdiff_self_right
  statement: x ⊓ y \ x = ⊥
  proof: calc
    x ⊓ y \ x = (x ⊓ y ⊔ x \ y) ⊓ y \ x := by rw [sup_inf_sdiff]
    _ = ⊥ := by rw [inf_sup_right, inf_comm x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]

@[simp]

中文:
定理 inf_sdiff_self_right
  结论: x ⊓ y \ x = ⊥
  证明: calc
    x ⊓ y \ x = (x ⊓ y ⊔ x \ y) ⊓ y \ x := by rw [sup_inf_sdiff]
    _ = ⊥ := by rw [inf_sup_right, inf_comm x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]

@[simp]

Depends on / 依赖: bot_sup_eq, inf_comm, inf_inf_sdiff, inf_sup_right, sdiff_inf_sdiff, sup_inf_sdiff
-/
theorem inf_sdiff_self_right : x ⊓ y \ x = ⊥ :=
  calc
    x ⊓ y \ x = (x ⊓ y ⊔ x \ y) ⊓ y \ x := by rw [sup_inf_sdiff]
    _ = ⊥ := by rw [inf_sup_right, inf_comm x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]

@[simp]
/--
theorem `inf_sdiff_self_left` / 定理 `inf_sdiff_self_left`

English:
theorem inf_sdiff_self_left
  statement: y \ x ⊓ x = ⊥
  proof: by rw [inf_comm, inf_sdiff_self_right]

中文:
定理 inf_sdiff_self_left
  结论: y \ x ⊓ x = ⊥
  证明: by rw [inf_comm, inf_sdiff_self_right]

Depends on / 依赖: inf_comm, inf_sdiff_self_right
-/
theorem inf_sdiff_self_left : y \ x ⊓ x = ⊥ := by rw [inf_comm, inf_sdiff_self_right]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
-- see Note [lower instance priority]
instance (priority := 100) GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra :
    GeneralizedCoheytingAlgebra α where
  __ := ‹GeneralizedBooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toOrderBot
  sdiff := (· \ ·)
  sdiff_le_iff y x z :=
    ⟨fun h =>
      le_of_inf_le_sup_le
        (le_of_eq
          (by grind [sdiff_le', inf_of_le_right, inf_eq_right, inf_sdiff_self_right, bot_sup_eq,
            inf_sup_right]))
        (calc
          y ⊔ y \ x <= y \ x ⊔ x ⊔ z := by
            grind [sup_of_le_left, sdiff_le', le_sup_left, sdiff_sup_self']
          _ = x ⊔ z ⊔ y \ x := by ac_rfl),
      fun h => le_of_inf_le_sup_le (inf_sdiff_self_left.trans_le bot_le) (calc
        y \ x ⊔ x = y ⊔ x := sdiff_sup_self'
        _ <= x ⊔ z ⊔ x := sup_le_sup_right h x
        _ <= z ⊔ x := by rw [sup_assoc, sup_comm, sup_assoc, sup_idem])⟩

/--
theorem `disjoint_sdiff_self_left` / 定理 `disjoint_sdiff_self_left`

English:
theorem disjoint_sdiff_self_left
  statement: Disjoint (y \ x) x
  proof: disjoint_iff_inf_le.mpr inf_sdiff_self_left.le

中文:
定理 disjoint_sdiff_self_left
  结论: Disjoint (y \ x) x
  证明: disjoint_iff_inf_le.mpr inf_sdiff_self_left.le

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, inf_sdiff_self_left, inf_sdiff_self_left.le
-/
theorem disjoint_sdiff_self_left : Disjoint (y \ x) x :=
  disjoint_iff_inf_le.mpr inf_sdiff_self_left.le

/--
theorem `disjoint_sdiff_self_right` / 定理 `disjoint_sdiff_self_right`

English:
theorem disjoint_sdiff_self_right
  statement: Disjoint x (y \ x)
  proof: disjoint_iff_inf_le.mpr inf_sdiff_self_right.le

中文:
定理 disjoint_sdiff_self_right
  结论: Disjoint x (y \ x)
  证明: disjoint_iff_inf_le.mpr inf_sdiff_self_right.le

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, inf_sdiff_self_right, inf_sdiff_self_right.le
-/
theorem disjoint_sdiff_self_right : Disjoint x (y \ x) :=
  disjoint_iff_inf_le.mpr inf_sdiff_self_right.le

/--
lemma `le_sdiff` / 引理 `le_sdiff`

English:
lemma le_sdiff
  statement: x <= y \ z ↔ x <= y ∧ Disjoint x z
  proof: ⟨fun h => ⟨h.trans sdiff_le, disjoint_sdiff_self_left.mono_left h⟩, fun h =>
    by rw [← h.2.sdiff_eq_left]; exact sdiff_le_sdiff_right h.1⟩

中文:
引理 le_sdiff
  结论: x <= y \ z ↔ x <= y ∧ Disjoint x z
  证明: ⟨fun h => ⟨h.trans sdiff_le, disjoint_sdiff_self_left.mono_left h⟩, fun h =>
    by rw [← h.2.sdiff_eq_left]; exact sdiff_le_sdiff_right h.1⟩

Depends on / 依赖: disjoint_sdiff_self_left, disjoint_sdiff_self_left.mono_left, h.trans, mono_left, sdiff_eq_left, sdiff_le, sdiff_le_sdiff_right
-/
lemma le_sdiff : x <= y \ z ↔ x <= y ∧ Disjoint x z :=
  ⟨fun h => ⟨h.trans sdiff_le, disjoint_sdiff_self_left.mono_left h⟩, fun h =>
    by rw [← h.2.sdiff_eq_left]; exact sdiff_le_sdiff_right h.1⟩

/--
lemma `sdiff_eq_left` / 引理 `sdiff_eq_left`

English:
lemma sdiff_eq_left
  statement: x \ y = x ↔ Disjoint x y
  proof: ⟨fun h => disjoint_sdiff_self_left.mono_left h.ge, Disjoint.sdiff_eq_left⟩

中文:
引理 sdiff_eq_left
  结论: x \ y = x ↔ Disjoint x y
  证明: ⟨fun h => disjoint_sdiff_self_left.mono_left h.ge, Disjoint.sdiff_eq_left⟩
-/
@[simp] lemma sdiff_eq_left : x \ y = x ↔ Disjoint x y :=
  ⟨fun h => disjoint_sdiff_self_left.mono_left h.ge, Disjoint.sdiff_eq_left⟩

/--
theorem `Disjoint.sdiff_eq_of_sup_eq` / 定理 `Disjoint.sdiff_eq_of_sup_eq`

English:
theorem Disjoint.sdiff_eq_of_sup_eq
  given: (hi : Disjoint x z) (hs : x ⊔ z = y)
  statement: y \ x = z
  proof: have h : y ⊓ x = x := inf_eq_right.2 le_sup_left.trans hs.le
  sdiff_unique (by rw [h, hs]) (by rw [h, hi.eq_bot])

中文:
定理 Disjoint.sdiff_eq_of_sup_eq
  条件: (hi : Disjoint x z) (hs : x ⊔ z = y)
  结论: y \ x = z
  证明: have h : y ⊓ x = x := inf_eq_right.2 le_sup_left.trans hs.le
  sdiff_unique (by rw [h, hs]) (by rw [h, hi.eq_bot])

Depends on / 依赖: eq_bot, hi.eq_bot, hs.le, inf_eq_right, le_sup_left, le_sup_left.trans, sdiff_unique
-/
theorem Disjoint.sdiff_eq_of_sup_eq (hi : Disjoint x z) (hs : x ⊔ z = y) : y \ x = z :=
have h : y ⊓ x = x := inf_eq_right.2 le_sup_left.trans hs.le
  sdiff_unique (by rw [h, hs]) (by rw [h, hi.eq_bot])

/--
theorem `Disjoint.sdiff_unique` / 定理 `Disjoint.sdiff_unique`

English:
theorem Disjoint.sdiff_unique
  given: (hd : Disjoint x z) (hz : z <= y) (hs : y <= x ⊔ z)
  proof: sdiff_unique
    (by
      rw [← inf_eq_right] at hs
      rwa [sup_inf_right, inf_sup_right, sup_comm x, inf_sup_self, inf_comm, sup_comm z,
        hs, sup_eq_left])
    (by rw [inf_assoc, hd.eq_bot, inf_bot_eq])

中文:
定理 Disjoint.sdiff_unique
  条件: (hd : Disjoint x z) (hz : z <= y) (hs : y <= x ⊔ z)
  证明: sdiff_unique
    (by
      rw [← inf_eq_right] at hs
      rwa [sup_inf_right, inf_sup_right, sup_comm x, inf_sup_self, inf_comm, sup_comm z,
        hs, sup_eq_left])
    (by rw [inf_assoc, hd.eq_bot, inf_bot_eq])
-/
protected theorem Disjoint.sdiff_unique (hd : Disjoint x z) (hz : z <= y) (hs : y <= x ⊔ z) :
    y \ x = z :=
  sdiff_unique
    (by
      rw [← inf_eq_right] at hs
      rwa [sup_inf_right, inf_sup_right, sup_comm x, inf_sup_self, inf_comm, sup_comm z,
        hs, sup_eq_left])
    (by rw [inf_assoc, hd.eq_bot, inf_bot_eq])

-- cf. `IsCompl.disjoint_left_iff` and `IsCompl.disjoint_right_iff`
/--
theorem `disjoint_sdiff_iff_le` / 定理 `disjoint_sdiff_iff_le`

English:
theorem disjoint_sdiff_iff_le
  given: (hz : z <= y) (hx : x <= y)
  statement: Disjoint z (y \ x) ↔ z <= x
  proof: ⟨fun H =>
    le_of_inf_le_sup_le (le_trans H.le_bot bot_le)
      (by
        rw [sup_sdiff_cancel_right hx]
        grw [sdiff_le]
        rw [sup_eq_right.2 hz]),
    fun H => disjoint_sdiff_self_right.mono_left H⟩

中文:
定理 disjoint_sdiff_iff_le
  条件: (hz : z <= y) (hx : x <= y)
  结论: Disjoint z (y \ x) ↔ z <= x
  证明: ⟨fun H =>
    le_of_inf_le_sup_le (le_trans H.le_bot bot_le)
      (by
        rw [sup_sdiff_cancel_right hx]
        grw [sdiff_le]
        rw [sup_eq_right.2 hz]),
    fun H => disjoint_sdiff_self_right.mono_left H⟩

Depends on / 依赖: H.le_bot, bot_le, disjoint_sdiff_self_right, disjoint_sdiff_self_right.mono_left, le_bot, le_of_inf_le_sup_le, le_trans, mono_left, sdiff_le, sup_eq_right, sup_sdiff_cancel_right
-/
theorem disjoint_sdiff_iff_le (hz : z <= y) (hx : x <= y) : Disjoint z (y \ x) ↔ z <= x :=
  ⟨fun H =>
    le_of_inf_le_sup_le (le_trans H.le_bot bot_le)
      (by
        rw [sup_sdiff_cancel_right hx]
        grw [sdiff_le]
        rw [sup_eq_right.2 hz]),
    fun H => disjoint_sdiff_self_right.mono_left H⟩

-- cf. `IsCompl.le_left_iff` and `IsCompl.le_right_iff`
/--
theorem `le_iff_disjoint_sdiff` / 定理 `le_iff_disjoint_sdiff`

English:
theorem le_iff_disjoint_sdiff
  given: (hz : z <= y) (hx : x <= y)
  statement: z <= x ↔ Disjoint z (y \ x)
  proof: (disjoint_sdiff_iff_le hz hx).symm

中文:
定理 le_iff_disjoint_sdiff
  条件: (hz : z <= y) (hx : x <= y)
  结论: z <= x ↔ Disjoint z (y \ x)
  证明: (disjoint_sdiff_iff_le hz hx).symm

Depends on / 依赖: disjoint_sdiff_iff_le
-/
theorem le_iff_disjoint_sdiff (hz : z <= y) (hx : x <= y) : z <= x ↔ Disjoint z (y \ x) :=
  (disjoint_sdiff_iff_le hz hx).symm

-- cf. `IsCompl.inf_left_eq_bot_iff` and `IsCompl.inf_right_eq_bot_iff`
/--
theorem `inf_sdiff_eq_bot_iff` / 定理 `inf_sdiff_eq_bot_iff`

English:
theorem inf_sdiff_eq_bot_iff
  given: (hz : z <= y) (hx : x <= y)
  statement: z ⊓ y \ x = ⊥ ↔ z <= x
  proof: by
  rw [← disjoint_iff]
  exact disjoint_sdiff_iff_le hz hx

中文:
定理 inf_sdiff_eq_bot_iff
  条件: (hz : z <= y) (hx : x <= y)
  结论: z ⊓ y \ x = ⊥ ↔ z <= x
  证明: by
  rw [← disjoint_iff]
  exact disjoint_sdiff_iff_le hz hx

Depends on / 依赖: disjoint_iff, disjoint_sdiff_iff_le
-/
theorem inf_sdiff_eq_bot_iff (hz : z <= y) (hx : x <= y) : z ⊓ y \ x = ⊥ ↔ z <= x := by
  rw [← disjoint_iff]
  exact disjoint_sdiff_iff_le hz hx

-- cf. `IsCompl.left_le_iff` and `IsCompl.right_le_iff`
/--
theorem `le_iff_eq_sup_sdiff` / 定理 `le_iff_eq_sup_sdiff`

English:
theorem le_iff_eq_sup_sdiff
  given: (hz : z <= y) (hx : x <= y)
  statement: x <= z ↔ y = z ⊔ y \ x
  proof: ⟨fun H => (sup_sdiff_cancel' H hz).symm,
    fun H => by
    conv_lhs at H => rw [← sup_sdiff_cancel_right hx]
    refine le_of_inf_le_sup_le ?_ H.le
    rw [inf_sdiff_self_right]
    exact bot_le⟩

中文:
定理 le_iff_eq_sup_sdiff
  条件: (hz : z <= y) (hx : x <= y)
  结论: x <= z ↔ y = z ⊔ y \ x
  证明: ⟨fun H => (sup_sdiff_cancel' H hz).symm,
    fun H => by
    conv_lhs at H => rw [← sup_sdiff_cancel_right hx]
    refine le_of_inf_le_sup_le ?_ H.le
    rw [inf_sdiff_self_right]
    exact bot_le⟩

Depends on / 依赖: H.le, bot_le, conv_lhs, inf_sdiff_self_right, le_of_inf_le_sup_le, sup_sdiff_cancel, sup_sdiff_cancel_right
-/
theorem le_iff_eq_sup_sdiff (hz : z <= y) (hx : x <= y) : x <= z ↔ y = z ⊔ y \ x :=
  ⟨fun H => (sup_sdiff_cancel' H hz).symm,
    fun H => by
    conv_lhs at H => rw [← sup_sdiff_cancel_right hx]
    refine le_of_inf_le_sup_le ?_ H.le
    rw [inf_sdiff_self_right]
    exact bot_le⟩

-- cf. `IsCompl.sup_inf`
/--
theorem `sdiff_sup` / 定理 `sdiff_sup`

English:
theorem sdiff_sup
  statement: y \ (x ⊔ z) = y \ x ⊓ y \ z
  proof: sdiff_unique
    (calc
      y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_left]; rw [inf_sup_left y]
      _ = (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) := by ac_rfl
      _ = (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y) := by rw [sup_inf_sdiff

中文:
定理 sdiff_sup
  结论: y \ (x ⊔ z) = y \ x ⊓ y \ z
  证明: sdiff_unique
    (calc
      y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_left]; rw [inf_sup_left y]
      _ = (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) := by ac_rfl
      _ = (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y) := by rw [sup_inf_sdiff

Depends on / 依赖: inf_idem, inf_sup_left, sdiff_unique, sup_inf_left, sup_inf_sdiff, sup_inf_self
-/
theorem sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z :=
  sdiff_unique
    (calc
      y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_left]; rw [inf_sup_left y]
      _ = (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) := by ac_rfl
      _ = (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y) := by rw [sup_inf_sdiff, sup_inf_sdiff]
      _ = (y ⊔ y ⊓ z) ⊓ (y ⊔ y ⊓ x) := by ac_rfl
      _ = y := by rw [sup_inf_self, sup_inf_self, inf_idem])
    (calc
      y ⊓ (x ⊔ z) ⊓ (y \ x ⊓ y \ z) = y ⊓ x ⊓ (y \ x ⊓ y \ z) ⊔ y ⊓ z ⊓ (y \ x ⊓ y \ z) := by
          rw [inf_sup_left]; rw [inf_sup_right]
      _ = y ⊓ x ⊓ y \ x ⊓ y \ z ⊔ y \ x ⊓ (y \ z ⊓ (y ⊓ z)) := by ac_rfl
      _ = ⊥ := by simp)

/--
theorem `sdiff_eq_sdiff_iff_inf_eq_inf` / 定理 `sdiff_eq_sdiff_iff_inf_eq_inf`

English:
theorem sdiff_eq_sdiff_iff_inf_eq_inf
  statement: y \ x = y \ z ↔ y ⊓ x = y ⊓ z
  proof: ⟨fun h => eq_of_inf_eq_sup_eq (a := y \ x) (by rw [inf_inf_sdiff, h, inf_inf_sdiff])
    (by rw [sup_inf_sdiff, h, sup_inf_sdiff]),
    fun h => by rw [← sdiff_inf_self_right, ← sdiff_inf_self_right z y, inf_comm, h, inf_comm]⟩

中文:
定理 sdiff_eq_sdiff_iff_inf_eq_inf
  结论: y \ x = y \ z ↔ y ⊓ x = y ⊓ z
  证明: ⟨fun h => eq_of_inf_eq_sup_eq (a := y \ x) (by rw [inf_inf_sdiff, h, inf_inf_sdiff])
    (by rw [sup_inf_sdiff, h, sup_inf_sdiff]),
    fun h => by rw [← sdiff_inf_self_right, ← sdiff_inf_self_right z y, inf_comm, h, inf_comm]⟩

Depends on / 依赖: eq_of_inf_eq_sup_eq, inf_comm, inf_inf_sdiff, sdiff_inf_self_right, sup_inf_sdiff
-/
theorem sdiff_eq_sdiff_iff_inf_eq_inf : y \ x = y \ z ↔ y ⊓ x = y ⊓ z :=
  ⟨fun h => eq_of_inf_eq_sup_eq (a := y \ x) (by rw [inf_inf_sdiff, h, inf_inf_sdiff])
    (by rw [sup_inf_sdiff, h, sup_inf_sdiff]),
    fun h => by rw [← sdiff_inf_self_right, ← sdiff_inf_self_right z y, inf_comm, h, inf_comm]⟩

/--
theorem `sdiff_eq_self_iff_disjoint` / 定理 `sdiff_eq_self_iff_disjoint`

English:
theorem sdiff_eq_self_iff_disjoint
  statement: x \ y = x ↔ Disjoint y x
  proof: sdiff_eq_left.trans disjoint_comm

中文:
定理 sdiff_eq_self_iff_disjoint
  结论: x \ y = x ↔ Disjoint y x
  证明: sdiff_eq_left.trans disjoint_comm

Depends on / 依赖: disjoint_comm, sdiff_eq_left, sdiff_eq_left.trans
-/
theorem sdiff_eq_self_iff_disjoint : x \ y = x ↔ Disjoint y x := sdiff_eq_left.trans disjoint_comm

/--
theorem `sdiff_lt` / 定理 `sdiff_lt`

English:
theorem sdiff_lt
  given: (hx : y <= x) (hy : y != ⊥)
  statement: x \ y < x
  proof: by
  refine sdiff_le.lt_of_ne fun h => hy ?_
  rw [sdiff_eq_left]; rw [disjoint_iff] at h
  rw [← h]; rw [inf_eq_right.mpr hx]

中文:
定理 sdiff_lt
  条件: (hx : y <= x) (hy : y != ⊥)
  结论: x \ y < x
  证明: by
  refine sdiff_le.lt_of_ne fun h => hy ?_
  rw [sdiff_eq_left]; rw [disjoint_iff] at h
  rw [← h]; rw [inf_eq_right.mpr hx]

Depends on / 依赖: disjoint_iff, inf_eq_right, inf_eq_right.mpr, lt_of_ne, sdiff_eq_left, sdiff_le, sdiff_le.lt_of_ne
-/
theorem sdiff_lt (hx : y <= x) (hy : y != ⊥) : x \ y < x := by
  refine sdiff_le.lt_of_ne fun h => hy ?_
  rw [sdiff_eq_left]; rw [disjoint_iff] at h
  rw [← h]; rw [inf_eq_right.mpr hx]

/--
theorem `sdiff_lt_left` / 定理 `sdiff_lt_left`

English:
theorem sdiff_lt_left
  statement: x \ y < x ↔ ¬ Disjoint y x
  proof: by
  rw [lt_iff_le_and_ne]; rw [Ne]; rw [sdiff_eq_self_iff_disjoint]; rw [and_iff_right sdiff_le]

@[simp]

中文:
定理 sdiff_lt_left
  结论: x \ y < x ↔ ¬ Disjoint y x
  证明: by
  rw [lt_iff_le_and_ne]; rw [Ne]; rw [sdiff_eq_self_iff_disjoint]; rw [and_iff_right sdiff_le]

@[simp]

Depends on / 依赖: and_iff_right, lt_iff_le_and_ne, sdiff_eq_self_iff_disjoint, sdiff_le
-/
theorem sdiff_lt_left : x \ y < x ↔ ¬ Disjoint y x := by
  rw [lt_iff_le_and_ne]; rw [Ne]; rw [sdiff_eq_self_iff_disjoint]; rw [and_iff_right sdiff_le]

@[simp]
/--
theorem `le_sdiff_right` / 定理 `le_sdiff_right`

English:
theorem le_sdiff_right
  statement: x <= y \ x ↔ x = ⊥
  proof: ⟨fun h => disjoint_self.1 (disjoint_sdiff_self_right.mono_right h), fun h => h.le.trans bot_le⟩

中文:
定理 le_sdiff_right
  结论: x <= y \ x ↔ x = ⊥
  证明: ⟨fun h => disjoint_self.1 (disjoint_sdiff_self_right.mono_right h), fun h => h.le.trans bot_le⟩

Depends on / 依赖: bot_le, disjoint_sdiff_self_right, disjoint_sdiff_self_right.mono_right, disjoint_self, h.le.trans, mono_right
-/
theorem le_sdiff_right : x <= y \ x ↔ x = ⊥ :=
  ⟨fun h => disjoint_self.1 (disjoint_sdiff_self_right.mono_right h), fun h => h.le.trans bot_le⟩

/--
lemma `sdiff_eq_right` / 引理 `sdiff_eq_right`

English:
lemma sdiff_eq_right
  statement: x \ y = y ↔ x = ⊥ ∧ y = ⊥
  proof: by
  rw [disjoint_sdiff_self_left.eq_iff]; simp_all

中文:
引理 sdiff_eq_right
  结论: x \ y = y ↔ x = ⊥ ∧ y = ⊥
  证明: by
  rw [disjoint_sdiff_self_left.eq_iff]; simp_all
-/
@[simp] lemma sdiff_eq_right : x \ y = y ↔ x = ⊥ ∧ y = ⊥ := by
  rw [disjoint_sdiff_self_left.eq_iff]; simp_all

/--
lemma `sdiff_ne_right` / 引理 `sdiff_ne_right`

English:
lemma sdiff_ne_right
  statement: x \ y != y ↔ x != ⊥ ∨ y != ⊥
  proof: sdiff_eq_right.not.trans not_and_or

中文:
引理 sdiff_ne_right
  结论: x \ y != y ↔ x != ⊥ ∨ y != ⊥
  证明: sdiff_eq_right.not.trans not_and_or

Depends on / 依赖: not_and_or, sdiff_eq_right, sdiff_eq_right.not.trans
-/
lemma sdiff_ne_right : x \ y != y ↔ x != ⊥ ∨ y != ⊥ := sdiff_eq_right.not.trans not_and_or

/--
theorem `sdiff_lt_sdiff_right` / 定理 `sdiff_lt_sdiff_right`

English:
theorem sdiff_lt_sdiff_right
  given: (h : x < y) (hz : z <= x)
  statement: x \ z < y \ z
  proof: (sdiff_le_sdiff_right h.le).lt_of_not_ge
fun h' => h.not_ge le_sdiff_sup.trans sup_le_of_le_sdiff_right h' hz

中文:
定理 sdiff_lt_sdiff_right
  条件: (h : x < y) (hz : z <= x)
  结论: x \ z < y \ z
  证明: (sdiff_le_sdiff_right h.le).lt_of_not_ge
fun h' => h.not_ge le_sdiff_sup.trans sup_le_of_le_sdiff_right h' hz

Depends on / 依赖: h.le, h.not_ge, le_sdiff_sup, le_sdiff_sup.trans, lt_of_not_ge, not_ge, sdiff_le_sdiff_right, sup_le_of_le_sdiff_right
-/
theorem sdiff_lt_sdiff_right (h : x < y) (hz : z <= x) : x \ z < y \ z :=
  (sdiff_le_sdiff_right h.le).lt_of_not_ge
fun h' => h.not_ge le_sdiff_sup.trans sup_le_of_le_sdiff_right h' hz

/--
theorem `sup_inf_inf_sdiff` / 定理 `sup_inf_inf_sdiff`

English:
theorem sup_inf_inf_sdiff
  statement: x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z
  proof: by
  rw [inf_assoc]; rw [sup_inf_right]; rw [sup_inf_sdiff]; rw [inf_sup_right]; rw [inf_sdiff_left]

中文:
定理 sup_inf_inf_sdiff
  结论: x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z
  证明: by
  rw [inf_assoc]; rw [sup_inf_right]; rw [sup_inf_sdiff]; rw [inf_sup_right]; rw [inf_sdiff_left]

Depends on / 依赖: inf_assoc, inf_sdiff_left, inf_sup_right, sup_inf_right, sup_inf_sdiff
-/
theorem sup_inf_inf_sdiff : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z := by
  rw [inf_assoc]; rw [sup_inf_right]; rw [sup_inf_sdiff]; rw [inf_sup_right]; rw [inf_sdiff_left]

/--
theorem `sdiff_sdiff_right` / 定理 `sdiff_sdiff_right`

English:
theorem sdiff_sdiff_right
  statement: x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z
  proof: by
  rw [sup_comm]; rw [inf_comm]; rw [← inf_assoc]; rw [sup_inf_inf_sdiff]
  apply sdiff_unique
  · calc
      x ⊓ y \ z ⊔ (z ⊓ x ⊔ x \ y) = (x ⊔ (z ⊓ x ⊔ x \ y)) ⊓ (y \ z ⊔ (z ⊓ x ⊔ x \ y)) := by
          rw [sup_inf_right]
      _ = (x ⊔ x ⊓ z ⊔ x \ y) ⊓ (y \ z ⊔ (x ⊓ z ⊔ x \ y)) := by ac_rfl
  

中文:
定理 sdiff_sdiff_right
  结论: x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z
  证明: by
  rw [sup_comm]; rw [inf_comm]; rw [← inf_assoc]; rw [sup_inf_inf_sdiff]
  apply sdiff_unique
  · calc
      x ⊓ y \ z ⊔ (z ⊓ x ⊔ x \ y) = (x ⊔ (z ⊓ x ⊔ x \ y)) ⊓ (y \ z ⊔ (z ⊓ x ⊔ x \ y)) := by
          rw [sup_inf_right]
      _ = (x ⊔ x ⊓ z ⊔ x \ y) ⊓ (y \ z ⊔ (x ⊓ z ⊔ x \ y)) := by ac_rfl
  

Depends on / 依赖: inf_assoc, inf_comm, inf_sdiff_sup_right, inf_sup_left, inf_sup_right, sdiff_sup_self, sdiff_unique, sup_assoc, sup_comm, sup_inf_inf_sdiff, sup_inf_left, sup_inf_right, sup_inf_self, sup_sdiff_left
-/
theorem sdiff_sdiff_right : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := by
  rw [sup_comm]; rw [inf_comm]; rw [← inf_assoc]; rw [sup_inf_inf_sdiff]
  apply sdiff_unique
  · calc
      x ⊓ y \ z ⊔ (z ⊓ x ⊔ x \ y) = (x ⊔ (z ⊓ x ⊔ x \ y)) ⊓ (y \ z ⊔ (z ⊓ x ⊔ x \ y)) := by
          rw [sup_inf_right]
      _ = (x ⊔ x ⊓ z ⊔ x \ y) ⊓ (y \ z ⊔ (x ⊓ z ⊔ x \ y)) := by ac_rfl
      _ = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ x ⊓ y) ⊔ x \ y) := by
          rw [sup_inf_self]; rw [sup_sdiff_left]; rw [← sup_assoc]; rw [sup_inf_left]; rw [sdiff_sup_self']; rw [inf_sup_right]; rw [sup_comm y]; rw [inf_sdiff_sup_right]; rw [inf_sup_left x z y]
      _ = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ (x ⊓ y ⊔ x \ y))) := by ac_rfl
      _ = x := by simp
  · calc
      x ⊓ y \ z ⊓ (z ⊓ x ⊔ x \ y) = x ⊓ y \ z ⊓ (z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y := by rw [inf_sup_left]
      _ = x ⊓ (y \ z ⊓ z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y := by ac_rfl
      _ = x ⊓ y \ z ⊓ x \ y := by rw [inf_sdiff_self_left, bot_inf_eq, inf_bot_eq, bot_sup_eq]
      _ = x ⊓ (y \ z ⊓ y) ⊓ x \ y := by conv_lhs => rw [← inf_sdiff_left]
      _ = x ⊓ (y \ z ⊓ (y ⊓ x \ y)) := by ac_rfl
      _ = ⊥ := by rw [inf_sdiff_self_right, inf_bot_eq, inf_bot_eq]

/--
theorem `sdiff_sdiff_right'` / 定理 `sdiff_sdiff_right'`

English:
theorem sdiff_sdiff_right'
  statement: x \ (y \ z) = x \ y ⊔ x ⊓ z
  proof: calc
    x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := sdiff_sdiff_right
    _ = z ⊓ x ⊓ y ⊔ x \ y := by ac_rfl
    _ = x \ y ⊔ x ⊓ z := by rw [sup_inf_inf_sdiff, sup_comm, inf_comm]

中文:
定理 sdiff_sdiff_right'
  结论: x \ (y \ z) = x \ y ⊔ x ⊓ z
  证明: calc
    x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := sdiff_sdiff_right
    _ = z ⊓ x ⊓ y ⊔ x \ y := by ac_rfl
    _ = x \ y ⊔ x ⊓ z := by rw [sup_inf_inf_sdiff, sup_comm, inf_comm]

Depends on / 依赖: inf_comm, sdiff_sdiff_right, sup_comm, sup_inf_inf_sdiff
-/
theorem sdiff_sdiff_right' : x \ (y \ z) = x \ y ⊔ x ⊓ z :=
  calc
    x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := sdiff_sdiff_right
    _ = z ⊓ x ⊓ y ⊔ x \ y := by ac_rfl
    _ = x \ y ⊔ x ⊓ z := by rw [sup_inf_inf_sdiff, sup_comm, inf_comm]

/--
theorem `sdiff_sdiff_eq_sdiff_sup` / 定理 `sdiff_sdiff_eq_sdiff_sup`

English:
theorem sdiff_sdiff_eq_sdiff_sup
  given: (h : z <= x)
  statement: x \ (y \ z) = x \ y ⊔ z
  proof: by
  rw [sdiff_sdiff_right']; rw [inf_eq_right.2 h]

@[simp]

中文:
定理 sdiff_sdiff_eq_sdiff_sup
  条件: (h : z <= x)
  结论: x \ (y \ z) = x \ y ⊔ z
  证明: by
  rw [sdiff_sdiff_right']; rw [inf_eq_right.2 h]

@[simp]

Depends on / 依赖: inf_eq_right, sdiff_sdiff_right
-/
theorem sdiff_sdiff_eq_sdiff_sup (h : z <= x) : x \ (y \ z) = x \ y ⊔ z := by
  rw [sdiff_sdiff_right']; rw [inf_eq_right.2 h]

@[simp]
/--
theorem `sdiff_sdiff_right_self` / 定理 `sdiff_sdiff_right_self`

English:
theorem sdiff_sdiff_right_self
  statement: x \ (x \ y) = x ⊓ y
  proof: by
  rw [sdiff_sdiff_right]; rw [inf_idem]; rw [sdiff_self]; rw [bot_sup_eq]

中文:
定理 sdiff_sdiff_right_self
  结论: x \ (x \ y) = x ⊓ y
  证明: by
  rw [sdiff_sdiff_right]; rw [inf_idem]; rw [sdiff_self]; rw [bot_sup_eq]

Depends on / 依赖: bot_sup_eq, inf_idem, sdiff_sdiff_right, sdiff_self
-/
theorem sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y := by
  rw [sdiff_sdiff_right]; rw [inf_idem]; rw [sdiff_self]; rw [bot_sup_eq]

/--
theorem `sdiff_sdiff_eq_self` / 定理 `sdiff_sdiff_eq_self`

English:
theorem sdiff_sdiff_eq_self
  given: (h : y <= x)
  statement: x \ (x \ y) = y
  proof: by
  rw [sdiff_sdiff_right_self]; rw [inf_of_le_right h]

中文:
定理 sdiff_sdiff_eq_self
  条件: (h : y <= x)
  结论: x \ (x \ y) = y
  证明: by
  rw [sdiff_sdiff_right_self]; rw [inf_of_le_right h]

Depends on / 依赖: inf_of_le_right, sdiff_sdiff_right_self
-/
theorem sdiff_sdiff_eq_self (h : y <= x) : x \ (x \ y) = y := by
  rw [sdiff_sdiff_right_self]; rw [inf_of_le_right h]

/--
theorem `sdiff_eq_symm` / 定理 `sdiff_eq_symm`

English:
theorem sdiff_eq_symm
  given: (hy : y <= x) (h : x \ y = z)
  statement: x \ z = y
  proof: by
  rw [← h]; rw [sdiff_sdiff_eq_self hy]

中文:
定理 sdiff_eq_symm
  条件: (hy : y <= x) (h : x \ y = z)
  结论: x \ z = y
  证明: by
  rw [← h]; rw [sdiff_sdiff_eq_self hy]

Depends on / 依赖: sdiff_sdiff_eq_self
-/
theorem sdiff_eq_symm (hy : y <= x) (h : x \ y = z) : x \ z = y := by
  rw [← h]; rw [sdiff_sdiff_eq_self hy]

/--
theorem `sdiff_eq_comm` / 定理 `sdiff_eq_comm`

English:
theorem sdiff_eq_comm
  given: (hy : y <= x) (hz : z <= x)
  statement: x \ y = z ↔ x \ z = y
  proof: ⟨sdiff_eq_symm hy, sdiff_eq_symm hz⟩

中文:
定理 sdiff_eq_comm
  条件: (hy : y <= x) (hz : z <= x)
  结论: x \ y = z ↔ x \ z = y
  证明: ⟨sdiff_eq_symm hy, sdiff_eq_symm hz⟩

Depends on / 依赖: sdiff_eq_symm
-/
theorem sdiff_eq_comm (hy : y <= x) (hz : z <= x) : x \ y = z ↔ x \ z = y :=
  ⟨sdiff_eq_symm hy, sdiff_eq_symm hz⟩

/--
theorem `sdiff_right_inj` / 定理 `sdiff_right_inj`

English:
theorem sdiff_right_inj
  given: (hxz : x <= z) (hyz : y <= z)
  statement: z \ x = z \ y ↔ x = y
  proof: ⟨fun h => by rw [← sdiff_sdiff_eq_self hxz, h, sdiff_sdiff_eq_self hyz], congrArg (z \ ·)⟩

@[deprecated sdiff_right_inj (since := "2026-04-16")]

中文:
定理 sdiff_right_inj
  条件: (hxz : x <= z) (hyz : y <= z)
  结论: z \ x = z \ y ↔ x = y
  证明: ⟨fun h => by rw [← sdiff_sdiff_eq_self hxz, h, sdiff_sdiff_eq_self hyz], congrArg (z \ ·)⟩

@[deprecated sdiff_right_inj (since := "2026-04-16")]

Depends on / 依赖: sdiff_sdiff_eq_self
-/
theorem sdiff_right_inj (hxz : x <= z) (hyz : y <= z) : z \ x = z \ y ↔ x = y :=
  ⟨fun h => by rw [← sdiff_sdiff_eq_self hxz, h, sdiff_sdiff_eq_self hyz], congrArg (z \ ·)⟩

@[deprecated sdiff_right_inj (since := "2026-04-16")]
/--
theorem `eq_of_sdiff_eq_sdiff` / 定理 `eq_of_sdiff_eq_sdiff`

English:
theorem eq_of_sdiff_eq_sdiff
  given: (hxz : x <= z) (hyz : y <= z) (h : z \ x = z \ y)
  statement: x = y
  proof: (sdiff_right_inj hxz hyz).mp h

中文:
定理 eq_of_sdiff_eq_sdiff
  条件: (hxz : x <= z) (hyz : y <= z) (h : z \ x = z \ y)
  结论: x = y
  证明: (sdiff_right_inj hxz hyz).mp h

Depends on / 依赖: sdiff_right_inj
-/
theorem eq_of_sdiff_eq_sdiff (hxz : x <= z) (hyz : y <= z) (h : z \ x = z \ y) : x = y :=
  (sdiff_right_inj hxz hyz).mp h

/--
theorem `sdiff_le_sdiff_iff_le` / 定理 `sdiff_le_sdiff_iff_le`

English:
theorem sdiff_le_sdiff_iff_le
  given: (hx : x <= z) (hy : y <= z)
  statement: z \ x <= z \ y ↔ y <= x
  proof: by
  refine ⟨fun h => ?_, sdiff_le_sdiff_left⟩
  rw [← sdiff_sdiff_eq_self hx]; rw [← sdiff_sdiff_eq_self hy]
  exact sdiff_le_sdiff_left h

中文:
定理 sdiff_le_sdiff_iff_le
  条件: (hx : x <= z) (hy : y <= z)
  结论: z \ x <= z \ y ↔ y <= x
  证明: by
  refine ⟨fun h => ?_, sdiff_le_sdiff_left⟩
  rw [← sdiff_sdiff_eq_self hx]; rw [← sdiff_sdiff_eq_self hy]
  exact sdiff_le_sdiff_left h

Depends on / 依赖: sdiff_le_sdiff_left, sdiff_sdiff_eq_self
-/
theorem sdiff_le_sdiff_iff_le (hx : x <= z) (hy : y <= z) : z \ x <= z \ y ↔ y <= x := by
  refine ⟨fun h => ?_, sdiff_le_sdiff_left⟩
  rw [← sdiff_sdiff_eq_self hx]; rw [← sdiff_sdiff_eq_self hy]
  exact sdiff_le_sdiff_left h

/--
theorem `sdiff_sdiff_left'` / 定理 `sdiff_sdiff_left'`

English:
theorem sdiff_sdiff_left'
  statement: (x \ y) \ z = x \ y ⊓ x \ z
  proof: by rw [sdiff_sdiff_left, sdiff_sup]

中文:
定理 sdiff_sdiff_left'
  结论: (x \ y) \ z = x \ y ⊓ x \ z
  证明: by rw [sdiff_sdiff_left, sdiff_sup]

Depends on / 依赖: sdiff_sdiff_left, sdiff_sup
-/
theorem sdiff_sdiff_left' : (x \ y) \ z = x \ y ⊓ x \ z := by rw [sdiff_sdiff_left, sdiff_sup]

/--
theorem `sdiff_sdiff_sup_sdiff` / 定理 `sdiff_sdiff_sup_sdiff`

English:
theorem sdiff_sdiff_sup_sdiff
  statement: z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)
  proof: calc
    z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z ⊓ (z \ y ⊔ x)) := by
        rw [sdiff_sup]; rw [sdiff_sdiff_right]; rw [sdiff_sdiff_right]; rw [sup_inf_left]; rw [sup_comm]; rw [sup_inf_sdiff]; rw [sup_inf_left]; rw [sup_comm (z \ y)]; rw [sup_inf_sdiff]
    _ = z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x

中文:
定理 sdiff_sdiff_sup_sdiff
  结论: z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)
  证明: calc
    z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z ⊓ (z \ y ⊔ x)) := by
        rw [sdiff_sup]; rw [sdiff_sdiff_right]; rw [sdiff_sdiff_right]; rw [sup_inf_left]; rw [sup_comm]; rw [sup_inf_sdiff]; rw [sup_inf_left]; rw [sup_comm (z \ y)]; rw [sup_inf_sdiff]
    _ = z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x

Depends on / 依赖: inf_idem, sdiff_sdiff_right, sdiff_sup, sup_comm, sup_inf_left, sup_inf_sdiff
-/
theorem sdiff_sdiff_sup_sdiff : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) :=
  calc
    z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z ⊓ (z \ y ⊔ x)) := by
        rw [sdiff_sup]; rw [sdiff_sdiff_right]; rw [sdiff_sdiff_right]; rw [sup_inf_left]; rw [sup_comm]; rw [sup_inf_sdiff]; rw [sup_inf_left]; rw [sup_comm (z \ y)]; rw [sup_inf_sdiff]
    _ = z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by ac_rfl
    _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by rw [inf_idem]

/--
theorem `sdiff_sdiff_sup_sdiff'` / 定理 `sdiff_sdiff_sup_sdiff'`

English:
theorem sdiff_sdiff_sup_sdiff'
  statement: z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y
  proof: calc
    z \ (x \ y ⊔ y \ x) = z \ (x \ y) ⊓ z \ (y \ x) := sdiff_sup
    _ = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by rw [sdiff_sdiff_right, sdiff_sdiff_right]
    _ = (z \ x ⊔ z ⊓ y ⊓ x) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by ac_rfl
    _ = z \ x ⊓ z \ y ⊔ z ⊓ y ⊓ x := by rw [← sup_inf_right]
    _ = 

中文:
定理 sdiff_sdiff_sup_sdiff'
  结论: z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y
  证明: calc
    z \ (x \ y ⊔ y \ x) = z \ (x \ y) ⊓ z \ (y \ x) := sdiff_sup
    _ = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by rw [sdiff_sdiff_right, sdiff_sdiff_right]
    _ = (z \ x ⊔ z ⊓ y ⊓ x) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by ac_rfl
    _ = z \ x ⊓ z \ y ⊔ z ⊓ y ⊓ x := by rw [← sup_inf_right]
    _ = 

Depends on / 依赖: sdiff_sdiff_right, sdiff_sup, sup_inf_right
-/
theorem sdiff_sdiff_sup_sdiff' : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y :=
  calc
    z \ (x \ y ⊔ y \ x) = z \ (x \ y) ⊓ z \ (y \ x) := sdiff_sup
    _ = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by rw [sdiff_sdiff_right, sdiff_sdiff_right]
    _ = (z \ x ⊔ z ⊓ y ⊓ x) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by ac_rfl
    _ = z \ x ⊓ z \ y ⊔ z ⊓ y ⊓ x := by rw [← sup_inf_right]
    _ = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y := by ac_rfl

/--
lemma `sdiff_sdiff_sdiff_cancel_left` / 引理 `sdiff_sdiff_sdiff_cancel_left`

English:
lemma sdiff_sdiff_sdiff_cancel_left
  given: (hca : z <= x)
  statement: (x \ y) \ (x \ z) = z \ y
  proof: sdiff_sdiff_sdiff_le_sdiff.antisymm
(disjoint_sdiff_self_right.mono_left sdiff_le).le_sdiff_of_le_left sdiff_le_sdiff_right hca

中文:
引理 sdiff_sdiff_sdiff_cancel_left
  条件: (hca : z <= x)
  结论: (x \ y) \ (x \ z) = z \ y
  证明: sdiff_sdiff_sdiff_le_sdiff.antisymm
(disjoint_sdiff_self_right.mono_left sdiff_le).le_sdiff_of_le_left sdiff_le_sdiff_right hca

Depends on / 依赖: antisymm, disjoint_sdiff_self_right, disjoint_sdiff_self_right.mono_left, le_sdiff_of_le_left, mono_left, sdiff_le, sdiff_le_sdiff_right, sdiff_sdiff_sdiff_le_sdiff, sdiff_sdiff_sdiff_le_sdiff.antisymm
-/
lemma sdiff_sdiff_sdiff_cancel_left (hca : z <= x) : (x \ y) \ (x \ z) = z \ y :=
sdiff_sdiff_sdiff_le_sdiff.antisymm
(disjoint_sdiff_self_right.mono_left sdiff_le).le_sdiff_of_le_left sdiff_le_sdiff_right hca

/--
lemma `sdiff_sdiff_sdiff_cancel_right` / 引理 `sdiff_sdiff_sdiff_cancel_right`

English:
lemma sdiff_sdiff_sdiff_cancel_right
  given: (hcb : z <= y)
  statement: (x \ z) \ (y \ z) = x \ y
  proof: by
  rw [le_antisymm_iff]; rw [sdiff_le_comm]
  exact ⟨sdiff_sdiff_sdiff_le_sdiff,
(disjoint_sdiff_self_left.mono_right sdiff_le).le_sdiff_of_le_left sdiff_le_sdiff_left hcb⟩

中文:
引理 sdiff_sdiff_sdiff_cancel_right
  条件: (hcb : z <= y)
  结论: (x \ z) \ (y \ z) = x \ y
  证明: by
  rw [le_antisymm_iff]; rw [sdiff_le_comm]
  exact ⟨sdiff_sdiff_sdiff_le_sdiff,
(disjoint_sdiff_self_left.mono_right sdiff_le).le_sdiff_of_le_left sdiff_le_sdiff_left hcb⟩

Depends on / 依赖: disjoint_sdiff_self_left, disjoint_sdiff_self_left.mono_right, le_antisymm_iff, le_sdiff_of_le_left, mono_right, sdiff_le, sdiff_le_comm, sdiff_le_sdiff_left, sdiff_sdiff_sdiff_le_sdiff
-/
lemma sdiff_sdiff_sdiff_cancel_right (hcb : z <= y) : (x \ z) \ (y \ z) = x \ y := by
  rw [le_antisymm_iff]; rw [sdiff_le_comm]
  exact ⟨sdiff_sdiff_sdiff_le_sdiff,
(disjoint_sdiff_self_left.mono_right sdiff_le).le_sdiff_of_le_left sdiff_le_sdiff_left hcb⟩

/--
theorem `inf_sdiff` / 定理 `inf_sdiff`

English:
theorem inf_sdiff
  statement: (x ⊓ y) \ z = x \ z ⊓ y \ z
  proof: sdiff_unique
    (calc
      _ = (x ⊓ y ⊓ (z ⊔ x) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_left]; rw [sup_inf_right]; rw [sup_sdiff_self_right]; rw [inf_sup_right]; rw [inf_sdiff_sup_right]
      _ = (y ⊓ (x ⊓ (x ⊔ z)) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by ac_rfl
      _ = x ⊓ y ⊔ x

中文:
定理 inf_sdiff
  结论: (x ⊓ y) \ z = x \ z ⊓ y \ z
  证明: sdiff_unique
    (calc
      _ = (x ⊓ y ⊓ (z ⊔ x) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_left]; rw [sup_inf_right]; rw [sup_sdiff_self_right]; rw [inf_sup_right]; rw [inf_sdiff_sup_right]
      _ = (y ⊓ (x ⊓ (x ⊔ z)) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by ac_rfl
      _ = x ⊓ y ⊔ x

Depends on / 依赖: inf_comm, inf_le_inf, inf_sdiff_sup_right, inf_sup_right, inf_sup_self, sdiff_le, sdiff_unique, sup_eq_left, sup_inf_inf_sdiff, sup_inf_left, sup_inf_right, sup_sdiff_self_right
-/
theorem inf_sdiff : (x ⊓ y) \ z = x \ z ⊓ y \ z :=
  sdiff_unique
    (calc
      _ = (x ⊓ y ⊓ (z ⊔ x) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by
          rw [sup_inf_left]; rw [sup_inf_right]; rw [sup_sdiff_self_right]; rw [inf_sup_right]; rw [inf_sdiff_sup_right]
      _ = (y ⊓ (x ⊓ (x ⊔ z)) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z) := by ac_rfl
      _ = x ⊓ y ⊔ x \ z ⊓ y \ z := by rw [inf_sup_self, sup_inf_inf_sdiff, inf_comm y, sup_inf_left]
      _ = x ⊓ y := sup_eq_left.2 (inf_le_inf sdiff_le sdiff_le))
    (calc
      x ⊓ y ⊓ z ⊓ (x \ z ⊓ y \ z) = x ⊓ y ⊓ (z ⊓ x \ z) ⊓ y \ z := by ac_rfl
      _ = ⊥ := by rw [inf_sdiff_self_right, inf_bot_eq, bot_inf_eq])

/--
theorem `inf_sdiff_assoc` / 定理 `inf_sdiff_assoc`

English:
theorem inf_sdiff_assoc
  given: (x y z : α)
  statement: (x ⊓ y) \ z = x ⊓ y \ z
  proof: sdiff_unique (by rw [inf_assoc, ← inf_sup_left, sup_inf_sdiff]) calc
    x ⊓ y ⊓ z ⊓ (x ⊓ y \ z) = x ⊓ x ⊓ (y ⊓ z ⊓ y \ z) := by ac_rfl
    _ = ⊥ := by rw [inf_inf_sdiff, inf_bot_eq]

中文:
定理 inf_sdiff_assoc
  条件: (x y z : α)
  结论: (x ⊓ y) \ z = x ⊓ y \ z
  证明: sdiff_unique (by rw [inf_assoc, ← inf_sup_left, sup_inf_sdiff]) calc
    x ⊓ y ⊓ z ⊓ (x ⊓ y \ z) = x ⊓ x ⊓ (y ⊓ z ⊓ y \ z) := by ac_rfl
    _ = ⊥ := by rw [inf_inf_sdiff, inf_bot_eq]

Depends on / 依赖: inf_assoc, inf_bot_eq, inf_inf_sdiff, inf_sup_left, sdiff_unique, sup_inf_sdiff
-/
theorem inf_sdiff_assoc (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z :=
sdiff_unique (by rw [inf_assoc, ← inf_sup_left, sup_inf_sdiff]) calc
    x ⊓ y ⊓ z ⊓ (x ⊓ y \ z) = x ⊓ x ⊓ (y ⊓ z ⊓ y \ z) := by ac_rfl
    _ = ⊥ := by rw [inf_inf_sdiff, inf_bot_eq]

/--
theorem `sdiff_inf_right_comm` / 定理 `sdiff_inf_right_comm`

English:
theorem sdiff_inf_right_comm
  given: (x y z : α)
  statement: x \ z ⊓ y = (x ⊓ y) \ z
  proof: by
  rw [inf_comm x]; rw [inf_comm]; rw [inf_sdiff_assoc]

中文:
定理 sdiff_inf_right_comm
  条件: (x y z : α)
  结论: x \ z ⊓ y = (x ⊓ y) \ z
  证明: by
  rw [inf_comm x]; rw [inf_comm]; rw [inf_sdiff_assoc]

Depends on / 依赖: inf_comm, inf_sdiff_assoc
-/
theorem sdiff_inf_right_comm (x y z : α) : x \ z ⊓ y = (x ⊓ y) \ z := by
  rw [inf_comm x]; rw [inf_comm]; rw [inf_sdiff_assoc]

/--
lemma `inf_sdiff_left_comm` / 引理 `inf_sdiff_left_comm`

English:
lemma inf_sdiff_left_comm
  given: (a b c : α)
  statement: a ⊓ (b \ c) = b ⊓ (a \ c)
  proof: by
  simp_rw [← inf_sdiff_assoc, inf_comm]

中文:
引理 inf_sdiff_left_comm
  条件: (a b c : α)
  结论: a ⊓ (b \ c) = b ⊓ (a \ c)
  证明: by
  simp_rw [← inf_sdiff_assoc, inf_comm]

Depends on / 依赖: inf_comm, inf_sdiff_assoc, simp_rw
-/
lemma inf_sdiff_left_comm (a b c : α) : a ⊓ (b \ c) = b ⊓ (a \ c) := by
  simp_rw [← inf_sdiff_assoc, inf_comm]

/--
theorem `inf_sdiff_distrib_left` / 定理 `inf_sdiff_distrib_left`

English:
theorem inf_sdiff_distrib_left
  given: (a b c : α)
  statement: a ⊓ b \ c = (a ⊓ b) \ (a ⊓ c)
  proof: by
  rw [sdiff_inf]; rw [(sdiff_eq_bot_iff (α := α)).2 inf_le_left]; rw [bot_sup_eq]; rw [inf_sdiff_assoc]

中文:
定理 inf_sdiff_distrib_left
  条件: (a b c : α)
  结论: a ⊓ b \ c = (a ⊓ b) \ (a ⊓ c)
  证明: by
  rw [sdiff_inf]; rw [(sdiff_eq_bot_iff (α := α)).2 inf_le_left]; rw [bot_sup_eq]; rw [inf_sdiff_assoc]

Depends on / 依赖: bot_sup_eq, inf_le_left, inf_sdiff_assoc, sdiff_eq_bot_iff, sdiff_inf
-/
theorem inf_sdiff_distrib_left (a b c : α) : a ⊓ b \ c = (a ⊓ b) \ (a ⊓ c) := by
  rw [sdiff_inf]; rw [(sdiff_eq_bot_iff (α := α)).2 inf_le_left]; rw [bot_sup_eq]; rw [inf_sdiff_assoc]

/--
theorem `inf_sdiff_distrib_right` / 定理 `inf_sdiff_distrib_right`

English:
theorem inf_sdiff_distrib_right
  given: (a b c : α)
  statement: a \ b ⊓ c = (a ⊓ c) \ (b ⊓ c)
  proof: by
  simp_rw [inf_comm _ c, inf_sdiff_distrib_left]

中文:
定理 inf_sdiff_distrib_right
  条件: (a b c : α)
  结论: a \ b ⊓ c = (a ⊓ c) \ (b ⊓ c)
  证明: by
  simp_rw [inf_comm _ c, inf_sdiff_distrib_left]

Depends on / 依赖: inf_comm, inf_sdiff_distrib_left, simp_rw
-/
theorem inf_sdiff_distrib_right (a b c : α) : a \ b ⊓ c = (a ⊓ c) \ (b ⊓ c) := by
  simp_rw [inf_comm _ c, inf_sdiff_distrib_left]

/--
theorem `disjoint_sdiff_comm` / 定理 `disjoint_sdiff_comm`

English:
theorem disjoint_sdiff_comm
  statement: Disjoint (x \ z) y ↔ Disjoint x (y \ z)
  proof: by
  simp_rw [disjoint_iff, sdiff_inf_right_comm, inf_sdiff_assoc]

中文:
定理 disjoint_sdiff_comm
  结论: Disjoint (x \ z) y ↔ Disjoint x (y \ z)
  证明: by
  simp_rw [disjoint_iff, sdiff_inf_right_comm, inf_sdiff_assoc]

Depends on / 依赖: disjoint_iff, inf_sdiff_assoc, sdiff_inf_right_comm, simp_rw
-/
theorem disjoint_sdiff_comm : Disjoint (x \ z) y ↔ Disjoint x (y \ z) := by
  simp_rw [disjoint_iff, sdiff_inf_right_comm, inf_sdiff_assoc]

/--
theorem `sup_eq_sdiff_sup_sdiff_sup_inf` / 定理 `sup_eq_sdiff_sup_sdiff_sup_inf`

English:
theorem sup_eq_sdiff_sup_sdiff_sup_inf
  statement: x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y
  proof: Eq.symm
    calc
      x \ y ⊔ y \ x ⊔ x ⊓ y = (x \ y ⊔ y \ x ⊔ x) ⊓ (x \ y ⊔ y \ x ⊔ y) := by rw [sup_inf_left]
      _ = (x \ y ⊔ x ⊔ y \ x) ⊓ (x \ y ⊔ (y \ x ⊔ y)) := by ac_rfl
      _ = x ⊔ y := by simp

中文:
定理 sup_eq_sdiff_sup_sdiff_sup_inf
  结论: x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y
  证明: Eq.symm
    calc
      x \ y ⊔ y \ x ⊔ x ⊓ y = (x \ y ⊔ y \ x ⊔ x) ⊓ (x \ y ⊔ y \ x ⊔ y) := by rw [sup_inf_left]
      _ = (x \ y ⊔ x ⊔ y \ x) ⊓ (x \ y ⊔ (y \ x ⊔ y)) := by ac_rfl
      _ = x ⊔ y := by simp

Depends on / 依赖: Eq.symm, sup_inf_left
-/
theorem sup_eq_sdiff_sup_sdiff_sup_inf : x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y :=
Eq.symm
    calc
      x \ y ⊔ y \ x ⊔ x ⊓ y = (x \ y ⊔ y \ x ⊔ x) ⊓ (x \ y ⊔ y \ x ⊔ y) := by rw [sup_inf_left]
      _ = (x \ y ⊔ x ⊔ y \ x) ⊓ (x \ y ⊔ (y \ x ⊔ y)) := by ac_rfl
      _ = x ⊔ y := by simp

/--
theorem `sup_lt_of_lt_sdiff_left` / 定理 `sup_lt_of_lt_sdiff_left`

English:
theorem sup_lt_of_lt_sdiff_left
  given: (h : y < z \ x) (hxz : x <= z)
  statement: x ⊔ y < z
  proof: by
  rw [← sup_sdiff_cancel_right hxz]
  refine (sup_le_sup_left h.le _).lt_of_not_ge fun h' => h.not_ge ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_left h').trans sdiff_le

中文:
定理 sup_lt_of_lt_sdiff_left
  条件: (h : y < z \ x) (hxz : x <= z)
  结论: x ⊔ y < z
  证明: by
  rw [← sup_sdiff_cancel_right hxz]
  refine (sup_le_sup_left h.le _).lt_of_not_ge fun h' => h.not_ge ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_left h').trans sdiff_le

Depends on / 依赖: h.le, h.not_ge, lt_of_not_ge, not_ge, sdiff_idem, sdiff_le, sdiff_le_sdiff_of_sup_le_sup_left, sup_le_sup_left, sup_sdiff_cancel_right
-/
theorem sup_lt_of_lt_sdiff_left (h : y < z \ x) (hxz : x <= z) : x ⊔ y < z := by
  rw [← sup_sdiff_cancel_right hxz]
  refine (sup_le_sup_left h.le _).lt_of_not_ge fun h' => h.not_ge ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_left h').trans sdiff_le

/--
theorem `sup_lt_of_lt_sdiff_right` / 定理 `sup_lt_of_lt_sdiff_right`

English:
theorem sup_lt_of_lt_sdiff_right
  given: (h : x < z \ y) (hyz : y <= z)
  statement: x ⊔ y < z
  proof: by
  rw [← sdiff_sup_cancel hyz]
  refine lt_of_le_not_ge (by grw [h]) fun h' => h.not_ge ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_right h').trans sdiff_le

中文:
定理 sup_lt_of_lt_sdiff_right
  条件: (h : x < z \ y) (hyz : y <= z)
  结论: x ⊔ y < z
  证明: by
  rw [← sdiff_sup_cancel hyz]
  refine lt_of_le_not_ge (by grw [h]) fun h' => h.not_ge ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_right h').trans sdiff_le

Depends on / 依赖: h.not_ge, lt_of_le_not_ge, not_ge, sdiff_idem, sdiff_le, sdiff_le_sdiff_of_sup_le_sup_right, sdiff_sup_cancel
-/
theorem sup_lt_of_lt_sdiff_right (h : x < z \ y) (hyz : y <= z) : x ⊔ y < z := by
  rw [← sdiff_sup_cancel hyz]
  refine lt_of_le_not_ge (by grw [h]) fun h' => h.not_ge ?_
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_right h').trans sdiff_le

/--
Instance `Prod.instGeneralizedBooleanAlgebra` / 实例 `Prod.instGeneralizedBooleanAlgebra`

English:
instance Prod.instGeneralizedBooleanAlgebra
  signature: [GeneralizedBooleanAlgebra β]
  body: Prod.ext (sup_inf_sdiff _ _) (sup_inf_sdiff _ _)
  inf_inf_sdiff _ _ := Prod.ext (inf_inf_sdiff _ _) (inf_inf_sdiff _ _)

中文:
实例 积类型.instGeneralized布尔eanAlgebra
  签名: [Generalized布尔ean代数 β]
  定义体: Prod.ext (sup_inf_sdiff _ _) (sup_inf_sdiff _ _)
  inf_inf_sdiff _ _ := Prod.ext (inf_inf_sdiff _ _) (inf_inf_sdiff _ _)

Depends on / 依赖: Prod.ext, sup_inf_sdiff
-/
instance Prod.instGeneralizedBooleanAlgebra [GeneralizedBooleanAlgebra β] :
    GeneralizedBooleanAlgebra (α × β) where
  sup_inf_sdiff _ _ := Prod.ext (sup_inf_sdiff _ _) (sup_inf_sdiff _ _)
  inf_inf_sdiff _ _ := Prod.ext (inf_inf_sdiff _ _) (inf_inf_sdiff _ _)

-- Porting note: Once `pi_instance` has been ported, this is just `by pi_instance`.
/--
Instance `Pi.instGeneralizedBooleanAlgebra` / 实例 `Pi.instGeneralizedBooleanAlgebra`

English:
instance Pi.instGeneralizedBooleanAlgebra
  signature: {ι : Type*} {α : ι -> Type*}
  body: fun f g => funext fun a => sup_inf_sdiff (f a) (g a)
  inf_inf_sdiff := fun f g => funext fun a => inf_inf_sdiff (f a) (g a)

中文:
实例 依赖函数类型.instGeneralized布尔eanAlgebra
  签名: {ι : 类型} {α : ι -> 类型}
  定义体: fun f g => funext fun a => sup_inf_sdiff (f a) (g a)
  inf_inf_sdiff := fun f g => funext fun a => inf_inf_sdiff (f a) (g a)

Depends on / 依赖: sup_inf_sdiff
-/
instance Pi.instGeneralizedBooleanAlgebra {ι : Type*} {α : ι -> Type*}
    [forall i, GeneralizedBooleanAlgebra (α i)] : GeneralizedBooleanAlgebra (forall i, α i) where
  sup_inf_sdiff := fun f g => funext fun a => sup_inf_sdiff (f a) (g a)
  inf_inf_sdiff := fun f g => funext fun a => inf_inf_sdiff (f a) (g a)

end GeneralizedBooleanAlgebra


/-!
### Boolean algebras
-/
-- See note [reducible non-instances]
/--
Definition of `GeneralizedBooleanAlgebra.toBooleanAlgebra` / `GeneralizedBooleanAlgebra.toBooleanAlgebra` 的定义

English:
abbreviation GeneralizedBooleanAlgebra.toBooleanAlgebra
  signature: [GeneralizedBooleanAlgebra α] [OrderTop α]
  body: ‹GeneralizedBooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toOrderBot
  __ := ‹OrderTop α›
  compl a := ⊤ \ a
  inf_compl_le_bot _ := disjoint_sdiff_self_right.le_bot
  top_le_sup_compl _ := le_sup_sdiff
  sdiff_eq a b := by
    change _ = a ⊓ (⊤ \ b)
    rw [← inf_sdiff_assoc]; rw [inf_top_eq]

中文:
缩写 Generalized布尔ean代数.to布尔eanAlgebra
  签名: [Generalized布尔ean代数 α] [有顶序 α]
  定义体: ‹GeneralizedBooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toOrderBot
  __ := ‹OrderTop α›
  compl a := ⊤ \ a
  inf_compl_le_bot _ := disjoint_sdiff_self_right.le_bot
  top_le_sup_compl _ := le_sup_sdiff
  sdiff_eq a b := by
    change _ = a ⊓ (⊤ \ b)
    rw [← inf_sdiff_assoc]; rw [inf_top_eq]

Depends on / 依赖: GeneralizedBooleanAlgebra
-/
abbrev GeneralizedBooleanAlgebra.toBooleanAlgebra [GeneralizedBooleanAlgebra α] [OrderTop α] :
    BooleanAlgebra α where
  __ := ‹GeneralizedBooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toOrderBot
  __ := ‹OrderTop α›
  compl a := ⊤ \ a
  inf_compl_le_bot _ := disjoint_sdiff_self_right.le_bot
  top_le_sup_compl _ := le_sup_sdiff
  sdiff_eq a b := by
    change _ = a ⊓ (⊤ \ b)
    rw [← inf_sdiff_assoc]; rw [inf_top_eq]

section BooleanAlgebra

variable [BooleanAlgebra α]

/--
theorem `inf_compl_eq_bot'` / 定理 `inf_compl_eq_bot'`

English:
theorem inf_compl_eq_bot'
  statement: x ⊓ xᶜ = ⊥
  proof: bot_unique BooleanAlgebra.inf_compl_le_bot x

@[simp]

中文:
定理 inf_compl_eq_bot'
  结论: x ⊓ xᶜ = ⊥
  证明: bot_unique BooleanAlgebra.inf_compl_le_bot x

@[simp]

Depends on / 依赖: BooleanAlgebra, BooleanAlgebra.inf_compl_le_bot, bot_unique, inf_compl_le_bot
-/
theorem inf_compl_eq_bot' : x ⊓ xᶜ = ⊥ :=
bot_unique BooleanAlgebra.inf_compl_le_bot x

@[simp]
/--
theorem `sup_compl_eq_top` / 定理 `sup_compl_eq_top`

English:
theorem sup_compl_eq_top
  statement: x ⊔ xᶜ = ⊤
  proof: top_unique BooleanAlgebra.top_le_sup_compl x

@[simp]

中文:
定理 sup_compl_eq_top
  结论: x ⊔ xᶜ = ⊤
  证明: top_unique BooleanAlgebra.top_le_sup_compl x

@[simp]

Depends on / 依赖: BooleanAlgebra, BooleanAlgebra.top_le_sup_compl, top_le_sup_compl, top_unique
-/
theorem sup_compl_eq_top : x ⊔ xᶜ = ⊤ :=
top_unique BooleanAlgebra.top_le_sup_compl x

@[simp]
/--
theorem `compl_sup_eq_top` / 定理 `compl_sup_eq_top`

English:
theorem compl_sup_eq_top
  statement: xᶜ ⊔ x = ⊤
  proof: by rw [sup_comm, sup_compl_eq_top]

中文:
定理 compl_sup_eq_top
  结论: xᶜ ⊔ x = ⊤
  证明: by rw [sup_comm, sup_compl_eq_top]

Depends on / 依赖: sup_comm, sup_compl_eq_top
-/
theorem compl_sup_eq_top : xᶜ ⊔ x = ⊤ := by rw [sup_comm, sup_compl_eq_top]

/--
theorem `isCompl_compl` / 定理 `isCompl_compl`

English:
theorem isCompl_compl
  statement: IsCompl x xᶜ
  proof: IsCompl.of_eq inf_compl_eq_bot' sup_compl_eq_top

中文:
定理 isCompl_compl
  结论: 是补集 x xᶜ
  证明: IsCompl.of_eq inf_compl_eq_bot' sup_compl_eq_top

Depends on / 依赖: IsCompl, IsCompl.of_eq, inf_compl_eq_bot, of_eq, sup_compl_eq_top
-/
theorem isCompl_compl : IsCompl x xᶜ :=
  IsCompl.of_eq inf_compl_eq_bot' sup_compl_eq_top

/--
theorem `sdiff_eq` / 定理 `sdiff_eq`

English:
theorem sdiff_eq
  statement: x \ y = x ⊓ yᶜ
  proof: BooleanAlgebra.sdiff_eq x y

中文:
定理 sdiff_eq
  结论: x \ y = x ⊓ yᶜ
  证明: BooleanAlgebra.sdiff_eq x y

Depends on / 依赖: BooleanAlgebra, BooleanAlgebra.sdiff_eq, sdiff_eq
-/
theorem sdiff_eq : x \ y = x ⊓ yᶜ :=
  BooleanAlgebra.sdiff_eq x y

/--
theorem `himp_eq` / 定理 `himp_eq`

English:
theorem himp_eq
  statement: x ⇨ y = y ⊔ xᶜ
  proof: BooleanAlgebra.himp_eq x y

中文:
定理 himp_eq
  结论: x ⇨ y = y ⊔ xᶜ
  证明: BooleanAlgebra.himp_eq x y

Depends on / 依赖: BooleanAlgebra, BooleanAlgebra.himp_eq, himp_eq
-/
theorem himp_eq : x ⇨ y = y ⊔ xᶜ :=
  BooleanAlgebra.himp_eq x y

instance (priority := 100) BooleanAlgebra.toComplementedLattice : ComplementedLattice α :=
  ⟨fun x => ⟨xᶜ, isCompl_compl⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toGeneralizedBooleanAlgebra :
    GeneralizedBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  sup_inf_sdiff a b := by rw [sdiff_eq, ← inf_sup_left, sup_compl_eq_top, inf_top_eq]
  inf_inf_sdiff a b := by
    rw [sdiff_eq]; rw [← inf_inf_distrib_left]; rw [inf_compl_eq_bot']; rw [inf_bot_eq]

-- See note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toBiheytingAlgebra : BiheytingAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra
  hnot := compl
  le_himp_iff a b c := by rw [himp_eq, isCompl_compl.le_sup_right_iff_inf_left_le]
  himp_bot _ := _root_.himp_eq.trans (bot_sup_eq _)
  top_sdiff a := by rw [sdiff_eq, top_inf_eq]

@[simp]
/--
theorem `hnot_eq_compl` / 定理 `hnot_eq_compl`

English:
theorem hnot_eq_compl
  statement: ￢x = xᶜ
  proof: rfl

中文:
定理 hnot_eq_compl
  结论: ￢x = xᶜ
  证明: rfl
-/
theorem hnot_eq_compl : ￢x = xᶜ :=
  rfl

/--
theorem `top_sdiff` / 定理 `top_sdiff`

English:
theorem top_sdiff
  statement: ⊤ \ x = xᶜ
  proof: top_sdiff' x

中文:
定理 top_sdiff
  结论: ⊤ \ x = xᶜ
  证明: top_sdiff' x

Depends on / 依赖: top_sdiff
-/
theorem top_sdiff : ⊤ \ x = xᶜ :=
  top_sdiff' x

/--
theorem `eq_compl_iff_isCompl` / 定理 `eq_compl_iff_isCompl`

English:
theorem eq_compl_iff_isCompl
  statement: x = yᶜ ↔ IsCompl x y
  proof: ⟨fun h => by
    rw [h]
    exact isCompl_compl.symm, IsCompl.eq_compl⟩

中文:
定理 eq_compl_iff_isCompl
  结论: x = yᶜ ↔ 是补集 x y
  证明: ⟨fun h => by
    rw [h]
    exact isCompl_compl.symm, IsCompl.eq_compl⟩

Depends on / 依赖: IsCompl, IsCompl.eq_compl, eq_compl, isCompl_compl, isCompl_compl.symm
-/
theorem eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y :=
  ⟨fun h => by
    rw [h]
    exact isCompl_compl.symm, IsCompl.eq_compl⟩

/--
theorem `compl_eq_iff_isCompl` / 定理 `compl_eq_iff_isCompl`

English:
theorem compl_eq_iff_isCompl
  statement: xᶜ = y ↔ IsCompl x y
  proof: ⟨fun h => by
    rw [← h]
    exact isCompl_compl, IsCompl.compl_eq⟩

中文:
定理 compl_eq_iff_isCompl
  结论: xᶜ = y ↔ 是补集 x y
  证明: ⟨fun h => by
    rw [← h]
    exact isCompl_compl, IsCompl.compl_eq⟩

Depends on / 依赖: IsCompl, IsCompl.compl_eq, compl_eq, isCompl_compl
-/
theorem compl_eq_iff_isCompl : xᶜ = y ↔ IsCompl x y :=
  ⟨fun h => by
    rw [← h]
    exact isCompl_compl, IsCompl.compl_eq⟩

/--
theorem `compl_eq_comm` / 定理 `compl_eq_comm`

English:
theorem compl_eq_comm
  statement: xᶜ = y ↔ yᶜ = x
  proof: by
  rw [eq_comm]; rw [compl_eq_iff_isCompl]; rw [eq_compl_iff_isCompl]

中文:
定理 compl_eq_comm
  结论: xᶜ = y ↔ yᶜ = x
  证明: by
  rw [eq_comm]; rw [compl_eq_iff_isCompl]; rw [eq_compl_iff_isCompl]

Depends on / 依赖: compl_eq_iff_isCompl, eq_comm, eq_compl_iff_isCompl
-/
theorem compl_eq_comm : xᶜ = y ↔ yᶜ = x := by
  rw [eq_comm]; rw [compl_eq_iff_isCompl]; rw [eq_compl_iff_isCompl]

/--
theorem `eq_compl_comm` / 定理 `eq_compl_comm`

English:
theorem eq_compl_comm
  statement: x = yᶜ ↔ y = xᶜ
  proof: by
  rw [eq_comm]; rw [compl_eq_iff_isCompl]; rw [eq_compl_iff_isCompl]

@[simp]

中文:
定理 eq_compl_comm
  结论: x = yᶜ ↔ y = xᶜ
  证明: by
  rw [eq_comm]; rw [compl_eq_iff_isCompl]; rw [eq_compl_iff_isCompl]

@[simp]

Depends on / 依赖: compl_eq_iff_isCompl, eq_comm, eq_compl_iff_isCompl
-/
theorem eq_compl_comm : x = yᶜ ↔ y = xᶜ := by
  rw [eq_comm]; rw [compl_eq_iff_isCompl]; rw [eq_compl_iff_isCompl]

@[simp]
/--
theorem `compl_compl` / 定理 `compl_compl`

English:
theorem compl_compl
  given: (x : α)
  statement: xᶜᶜ = x
  proof: (@isCompl_compl _ x _).symm.compl_eq

中文:
定理 compl_compl
  条件: (x : α)
  结论: xᶜᶜ = x
  证明: (@isCompl_compl _ x _).symm.compl_eq

Depends on / 依赖: compl_eq, isCompl_compl, symm.compl_eq
-/
theorem compl_compl (x : α) : xᶜᶜ = x :=
  (@isCompl_compl _ x _).symm.compl_eq

/--
theorem `compl_comp_compl` / 定理 `compl_comp_compl`

English:
theorem compl_comp_compl
  statement: compl ∘ compl = @id α
  proof: funext compl_compl

@[simp]

中文:
定理 compl_comp_compl
  结论: compl ∘ compl = @id α
  证明: funext compl_compl

@[simp]

Depends on / 依赖: compl_compl
-/
theorem compl_comp_compl : compl ∘ compl = @id α :=
  funext compl_compl

@[simp]
/--
theorem `compl_involutive` / 定理 `compl_involutive`

English:
theorem compl_involutive
  statement: Function.Involutive (compl : α -> α)
  proof: compl_compl

中文:
定理 compl_involutive
  结论: 函数.对合 (compl : α -> α)
  证明: compl_compl

Depends on / 依赖: compl_compl
-/
theorem compl_involutive : Function.Involutive (compl : α -> α) :=
  compl_compl

/--
theorem `compl_bijective` / 定理 `compl_bijective`

English:
theorem compl_bijective
  statement: Function.Bijective (compl : α -> α)
  proof: compl_involutive.bijective

中文:
定理 compl_bijective
  结论: 函数.双射 (compl : α -> α)
  证明: compl_involutive.bijective

Depends on / 依赖: bijective, compl_involutive, compl_involutive.bijective
-/
theorem compl_bijective : Function.Bijective (compl : α -> α) :=
  compl_involutive.bijective

/--
theorem `compl_surjective` / 定理 `compl_surjective`

English:
theorem compl_surjective
  statement: Function.Surjective (compl : α -> α)
  proof: compl_involutive.surjective

中文:
定理 compl_surjective
  结论: 函数.满射 (compl : α -> α)
  证明: compl_involutive.surjective

Depends on / 依赖: compl_involutive, compl_involutive.surjective, surjective
-/
theorem compl_surjective : Function.Surjective (compl : α -> α) :=
  compl_involutive.surjective

/--
theorem `compl_injective` / 定理 `compl_injective`

English:
theorem compl_injective
  statement: Function.Injective (compl : α -> α)
  proof: compl_involutive.injective

@[simp]

中文:
定理 compl_injective
  结论: 函数.单射 (compl : α -> α)
  证明: compl_involutive.injective

@[simp]

Depends on / 依赖: compl_involutive, compl_involutive.injective, injective
-/
theorem compl_injective : Function.Injective (compl : α -> α) :=
  compl_involutive.injective

@[simp]
/--
theorem `compl_inj_iff` / 定理 `compl_inj_iff`

English:
theorem compl_inj_iff
  statement: xᶜ = yᶜ ↔ x = y
  proof: compl_injective.eq_iff

中文:
定理 compl_inj_iff
  结论: xᶜ = yᶜ ↔ x = y
  证明: compl_injective.eq_iff

Depends on / 依赖: compl_injective, compl_injective.eq_iff, eq_iff
-/
theorem compl_inj_iff : xᶜ = yᶜ ↔ x = y :=
  compl_injective.eq_iff

/--
theorem `IsCompl.compl_eq_iff` / 定理 `IsCompl.compl_eq_iff`

English:
theorem IsCompl.compl_eq_iff
  given: (h : IsCompl x y)
  statement: zᶜ = y ↔ z = x
  proof: h.compl_eq ▸ compl_inj_iff

@[simp]

中文:
定理 是补集.compl_eq_iff
  条件: (h : 是补集 x y)
  结论: zᶜ = y ↔ z = x
  证明: h.compl_eq ▸ compl_inj_iff

@[simp]

Depends on / 依赖: compl_eq, compl_inj_iff, h.compl_eq
-/
theorem IsCompl.compl_eq_iff (h : IsCompl x y) : zᶜ = y ↔ z = x :=
  h.compl_eq ▸ compl_inj_iff

@[simp]
/--
theorem `compl_eq_top` / 定理 `compl_eq_top`

English:
theorem compl_eq_top
  statement: xᶜ = ⊤ ↔ x = ⊥
  proof: isCompl_bot_top.compl_eq_iff

@[simp]

中文:
定理 compl_eq_top
  结论: xᶜ = ⊤ ↔ x = ⊥
  证明: isCompl_bot_top.compl_eq_iff

@[simp]

Depends on / 依赖: compl_eq_iff, isCompl_bot_top, isCompl_bot_top.compl_eq_iff
-/
theorem compl_eq_top : xᶜ = ⊤ ↔ x = ⊥ :=
  isCompl_bot_top.compl_eq_iff

@[simp]
/--
theorem `compl_eq_bot` / 定理 `compl_eq_bot`

English:
theorem compl_eq_bot
  statement: xᶜ = ⊥ ↔ x = ⊤
  proof: isCompl_top_bot.compl_eq_iff

@[simp]

中文:
定理 compl_eq_bot
  结论: xᶜ = ⊥ ↔ x = ⊤
  证明: isCompl_top_bot.compl_eq_iff

@[simp]

Depends on / 依赖: compl_eq_iff, isCompl_top_bot, isCompl_top_bot.compl_eq_iff
-/
theorem compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤ :=
  isCompl_top_bot.compl_eq_iff

@[simp]
/--
theorem `compl_inf` / 定理 `compl_inf`

English:
theorem compl_inf
  statement: (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
  proof: hnot_inf_distrib _ _

@[simp]

中文:
定理 compl_inf
  结论: (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
  证明: hnot_inf_distrib _ _

@[simp]

Depends on / 依赖: hnot_inf_distrib
-/
theorem compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ :=
  hnot_inf_distrib _ _

@[simp]
/--
theorem `compl_le_compl_iff_le` / 定理 `compl_le_compl_iff_le`

English:
theorem compl_le_compl_iff_le
  statement: yᶜ <= xᶜ ↔ x <= y
  proof: ⟨fun h => by have h := compl_le_compl h; simpa using h, compl_le_compl⟩

中文:
定理 compl_le_compl_iff_le
  结论: yᶜ <= xᶜ ↔ x <= y
  证明: ⟨fun h => by have h := compl_le_compl h; simpa using h, compl_le_compl⟩

Depends on / 依赖: compl_le_compl
-/
theorem compl_le_compl_iff_le : yᶜ <= xᶜ ↔ x <= y :=
  ⟨fun h => by have h := compl_le_compl h; simpa using h, compl_le_compl⟩

/--
lemma `compl_lt_compl_iff_lt` / 引理 `compl_lt_compl_iff_lt`

English:
lemma compl_lt_compl_iff_lt
  statement: yᶜ < xᶜ ↔ x < y
  proof: lt_iff_lt_of_le_iff_le' compl_le_compl_iff_le compl_le_compl_iff_le

中文:
引理 compl_lt_compl_iff_lt
  结论: yᶜ < xᶜ ↔ x < y
  证明: lt_iff_lt_of_le_iff_le' compl_le_compl_iff_le compl_le_compl_iff_le
-/
@[simp] lemma compl_lt_compl_iff_lt : yᶜ < xᶜ ↔ x < y :=
  lt_iff_lt_of_le_iff_le' compl_le_compl_iff_le compl_le_compl_iff_le

/--
theorem `compl_le_of_compl_le` / 定理 `compl_le_of_compl_le`

English:
theorem compl_le_of_compl_le
  given: (h : yᶜ <= x)
  statement: xᶜ <= y
  proof: by
  simpa only [compl_compl] using compl_le_compl h

中文:
定理 compl_le_of_compl_le
  条件: (h : yᶜ <= x)
  结论: xᶜ <= y
  证明: by
  simpa only [compl_compl] using compl_le_compl h

Depends on / 依赖: compl_compl, compl_le_compl
-/
theorem compl_le_of_compl_le (h : yᶜ <= x) : xᶜ <= y := by
  simpa only [compl_compl] using compl_le_compl h

/--
theorem `compl_le_iff_compl_le` / 定理 `compl_le_iff_compl_le`

English:
theorem compl_le_iff_compl_le
  statement: xᶜ <= y ↔ yᶜ <= x
  proof: ⟨compl_le_of_compl_le, compl_le_of_compl_le⟩

中文:
定理 compl_le_iff_compl_le
  结论: xᶜ <= y ↔ yᶜ <= x
  证明: ⟨compl_le_of_compl_le, compl_le_of_compl_le⟩

Depends on / 依赖: compl_le_of_compl_le
-/
theorem compl_le_iff_compl_le : xᶜ <= y ↔ yᶜ <= x :=
  ⟨compl_le_of_compl_le, compl_le_of_compl_le⟩

/--
theorem `compl_le_self` / 定理 `compl_le_self`

English:
theorem compl_le_self
  statement: xᶜ <= x ↔ x = ⊤
  proof: by simpa using le_compl_self (a := xᶜ)

中文:
定理 compl_le_self
  结论: xᶜ <= x ↔ x = ⊤
  证明: by simpa using le_compl_self (a := xᶜ)
-/
@[simp] theorem compl_le_self : xᶜ <= x ↔ x = ⊤ := by simpa using le_compl_self (a := xᶜ)

/--
theorem `compl_lt_self` / 定理 `compl_lt_self`

English:
theorem compl_lt_self
  given: [Nontrivial α]
  statement: xᶜ < x ↔ x = ⊤
  proof: by
  simpa using lt_compl_self (a := xᶜ)

@[simp]

中文:
定理 compl_lt_self
  条件: [非平凡 α]
  结论: xᶜ < x ↔ x = ⊤
  证明: by
  simpa using lt_compl_self (a := xᶜ)

@[simp]
-/
@[simp] theorem compl_lt_self [Nontrivial α] : xᶜ < x ↔ x = ⊤ := by
  simpa using lt_compl_self (a := xᶜ)

@[simp]
/--
theorem `sdiff_compl` / 定理 `sdiff_compl`

English:
theorem sdiff_compl
  statement: x \ yᶜ = x ⊓ y
  proof: by rw [sdiff_eq, compl_compl]

中文:
定理 sdiff_compl
  结论: x \ yᶜ = x ⊓ y
  证明: by rw [sdiff_eq, compl_compl]

Depends on / 依赖: compl_compl, sdiff_eq
-/
theorem sdiff_compl : x \ yᶜ = x ⊓ y := by rw [sdiff_eq, compl_compl]

/--
Instance `OrderDual.instBooleanAlgebra` / 实例 `OrderDual.instBooleanAlgebra`

English:
instance OrderDual.instBooleanAlgebra
  signature: : BooleanAlgebra αᵒᵈ where
  body: instDistribLattice α
  __ := instHeytingAlgebra
  sdiff_eq _ _ := @himp_eq α _ _ _
  himp_eq _ _ := @sdiff_eq α _ _ _
  inf_compl_le_bot a := (@codisjoint_hnot_right _ _ (ofDual a)).top_le
  top_le_sup_compl a := (@disjoint_compl_right _ _ (ofDual a)).le_bot

@[simp]

中文:
实例 OrderDual.inst布尔eanAlgebra
  签名: : 布尔代数 αᵒᵈ where
  定义体: instDistribLattice α
  __ := instHeytingAlgebra
  sdiff_eq _ _ := @himp_eq α _ _ _
  himp_eq _ _ := @sdiff_eq α _ _ _
  inf_compl_le_bot a := (@codisjoint_hnot_right _ _ (ofDual a)).top_le
  top_le_sup_compl a := (@disjoint_compl_right _ _ (ofDual a)).le_bot

@[simp]

Depends on / 依赖: instDistribLattice
-/
instance OrderDual.instBooleanAlgebra : BooleanAlgebra αᵒᵈ where
  __ := instDistribLattice α
  __ := instHeytingAlgebra
  sdiff_eq _ _ := @himp_eq α _ _ _
  himp_eq _ _ := @sdiff_eq α _ _ _
  inf_compl_le_bot a := (@codisjoint_hnot_right _ _ (ofDual a)).top_le
  top_le_sup_compl a := (@disjoint_compl_right _ _ (ofDual a)).le_bot

@[simp]
/--
theorem `sup_inf_inf_compl` / 定理 `sup_inf_inf_compl`

English:
theorem sup_inf_inf_compl
  statement: x ⊓ y ⊔ x ⊓ yᶜ = x
  proof: by rw [← sdiff_eq, sup_inf_sdiff _ _]

中文:
定理 sup_inf_inf_compl
  结论: x ⊓ y ⊔ x ⊓ yᶜ = x
  证明: by rw [← sdiff_eq, sup_inf_sdiff _ _]

Depends on / 依赖: sdiff_eq, sup_inf_sdiff
-/
theorem sup_inf_inf_compl : x ⊓ y ⊔ x ⊓ yᶜ = x := by rw [← sdiff_eq, sup_inf_sdiff _ _]

/--
theorem `compl_sdiff` / 定理 `compl_sdiff`

English:
theorem compl_sdiff
  statement: (x \ y)ᶜ = x ⇨ y
  proof: by
  rw [sdiff_eq]; rw [himp_eq]; rw [compl_inf]; rw [compl_compl]; rw [sup_comm]

@[simp]

中文:
定理 compl_sdiff
  结论: (x \ y)ᶜ = x ⇨ y
  证明: by
  rw [sdiff_eq]; rw [himp_eq]; rw [compl_inf]; rw [compl_compl]; rw [sup_comm]

@[simp]

Depends on / 依赖: compl_compl, compl_inf, himp_eq, sdiff_eq, sup_comm
-/
theorem compl_sdiff : (x \ y)ᶜ = x ⇨ y := by
  rw [sdiff_eq]; rw [himp_eq]; rw [compl_inf]; rw [compl_compl]; rw [sup_comm]

@[simp]
/--
theorem `compl_himp` / 定理 `compl_himp`

English:
theorem compl_himp
  statement: (x ⇨ y)ᶜ = x \ y
  proof: @compl_sdiff αᵒᵈ _ _ _

中文:
定理 compl_himp
  结论: (x ⇨ y)ᶜ = x \ y
  证明: @compl_sdiff αᵒᵈ _ _ _

Depends on / 依赖: compl_sdiff
-/
theorem compl_himp : (x ⇨ y)ᶜ = x \ y :=
  @compl_sdiff αᵒᵈ _ _ _

/--
theorem `compl_sdiff_compl` / 定理 `compl_sdiff_compl`

English:
theorem compl_sdiff_compl
  statement: xᶜ \ yᶜ = y \ x
  proof: by rw [sdiff_compl, sdiff_eq, inf_comm]

@[simp]

中文:
定理 compl_sdiff_compl
  结论: xᶜ \ yᶜ = y \ x
  证明: by rw [sdiff_compl, sdiff_eq, inf_comm]

@[simp]

Depends on / 依赖: inf_comm, sdiff_compl, sdiff_eq
-/
theorem compl_sdiff_compl : xᶜ \ yᶜ = y \ x := by rw [sdiff_compl, sdiff_eq, inf_comm]

@[simp]
/--
theorem `compl_himp_compl` / 定理 `compl_himp_compl`

English:
theorem compl_himp_compl
  statement: xᶜ ⇨ yᶜ = y ⇨ x
  proof: @compl_sdiff_compl αᵒᵈ _ _ _

中文:
定理 compl_himp_compl
  结论: xᶜ ⇨ yᶜ = y ⇨ x
  证明: @compl_sdiff_compl αᵒᵈ _ _ _

Depends on / 依赖: compl_sdiff_compl
-/
theorem compl_himp_compl : xᶜ ⇨ yᶜ = y ⇨ x :=
  @compl_sdiff_compl αᵒᵈ _ _ _

/--
theorem `disjoint_compl_left_iff` / 定理 `disjoint_compl_left_iff`

English:
theorem disjoint_compl_left_iff
  statement: Disjoint xᶜ y ↔ y <= x
  proof: by
  rw [← le_compl_iff_disjoint_left]; rw [compl_compl]

中文:
定理 disjoint_compl_left_iff
  结论: Disjoint xᶜ y ↔ y <= x
  证明: by
  rw [← le_compl_iff_disjoint_left]; rw [compl_compl]

Depends on / 依赖: compl_compl, le_compl_iff_disjoint_left
-/
theorem disjoint_compl_left_iff : Disjoint xᶜ y ↔ y <= x := by
  rw [← le_compl_iff_disjoint_left]; rw [compl_compl]

/--
theorem `disjoint_compl_right_iff` / 定理 `disjoint_compl_right_iff`

English:
theorem disjoint_compl_right_iff
  statement: Disjoint x yᶜ ↔ x <= y
  proof: by
  rw [← le_compl_iff_disjoint_right]; rw [compl_compl]

中文:
定理 disjoint_compl_right_iff
  结论: Disjoint x yᶜ ↔ x <= y
  证明: by
  rw [← le_compl_iff_disjoint_right]; rw [compl_compl]

Depends on / 依赖: compl_compl, le_compl_iff_disjoint_right
-/
theorem disjoint_compl_right_iff : Disjoint x yᶜ ↔ x <= y := by
  rw [← le_compl_iff_disjoint_right]; rw [compl_compl]

/--
theorem `codisjoint_himp_self_left` / 定理 `codisjoint_himp_self_left`

English:
theorem codisjoint_himp_self_left
  statement: Codisjoint (x ⇨ y) x
  proof: @disjoint_sdiff_self_left αᵒᵈ _ _ _

中文:
定理 codisjoint_himp_self_left
  结论: Codisjoint (x ⇨ y) x
  证明: @disjoint_sdiff_self_left αᵒᵈ _ _ _

Depends on / 依赖: disjoint_sdiff_self_left
-/
theorem codisjoint_himp_self_left : Codisjoint (x ⇨ y) x :=
  @disjoint_sdiff_self_left αᵒᵈ _ _ _

/--
theorem `codisjoint_himp_self_right` / 定理 `codisjoint_himp_self_right`

English:
theorem codisjoint_himp_self_right
  statement: Codisjoint x (x ⇨ y)
  proof: @disjoint_sdiff_self_right αᵒᵈ _ _ _

中文:
定理 codisjoint_himp_self_right
  结论: Codisjoint x (x ⇨ y)
  证明: @disjoint_sdiff_self_right αᵒᵈ _ _ _

Depends on / 依赖: disjoint_sdiff_self_right
-/
theorem codisjoint_himp_self_right : Codisjoint x (x ⇨ y) :=
  @disjoint_sdiff_self_right αᵒᵈ _ _ _

/--
theorem `himp_le` / 定理 `himp_le`

English:
theorem himp_le
  statement: x ⇨ y <= z ↔ y <= z ∧ Codisjoint x z
  proof: by
  rw [himp_eq]; rw [sup_le_iff]; rw [and_congr_right_iff]
  exact fun _ => hnot_le_iff_codisjoint_right

中文:
定理 himp_le
  结论: x ⇨ y <= z ↔ y <= z ∧ Codisjoint x z
  证明: by
  rw [himp_eq]; rw [sup_le_iff]; rw [and_congr_right_iff]
  exact fun _ => hnot_le_iff_codisjoint_right

Depends on / 依赖: and_congr_right_iff, himp_eq, hnot_le_iff_codisjoint_right, sup_le_iff
-/
theorem himp_le : x ⇨ y <= z ↔ y <= z ∧ Codisjoint x z := by
  rw [himp_eq]; rw [sup_le_iff]; rw [and_congr_right_iff]
  exact fun _ => hnot_le_iff_codisjoint_right

/--
lemma `himp_le_left` / 引理 `himp_le_left`

English:
lemma himp_le_left
  statement: x ⇨ y <= x ↔ x = ⊤
  proof: ⟨fun h => codisjoint_self.1 codisjoint_himp_self_right.mono_right h, fun h => le_top.trans h.ge⟩

中文:
引理 himp_le_left
  结论: x ⇨ y <= x ↔ x = ⊤
  证明: ⟨fun h => codisjoint_self.1 codisjoint_himp_self_right.mono_right h, fun h => le_top.trans h.ge⟩
-/
@[simp] lemma himp_le_left : x ⇨ y <= x ↔ x = ⊤ :=
⟨fun h => codisjoint_self.1 codisjoint_himp_self_right.mono_right h, fun h => le_top.trans h.ge⟩

/--
lemma `himp_eq_left` / 引理 `himp_eq_left`

English:
lemma himp_eq_left
  statement: x ⇨ y = x ↔ x = ⊤ ∧ y = ⊤
  proof: by
  rw [codisjoint_himp_self_left.eq_iff]; aesop

中文:
引理 himp_eq_left
  结论: x ⇨ y = x ↔ x = ⊤ ∧ y = ⊤
  证明: by
  rw [codisjoint_himp_self_left.eq_iff]; aesop
-/
@[simp] lemma himp_eq_left : x ⇨ y = x ↔ x = ⊤ ∧ y = ⊤ := by
  rw [codisjoint_himp_self_left.eq_iff]; aesop

/--
lemma `himp_ne_right` / 引理 `himp_ne_right`

English:
lemma himp_ne_right
  statement: x ⇨ y != x ↔ x != ⊤ ∨ y != ⊤
  proof: himp_eq_left.not.trans not_and_or

中文:
引理 himp_ne_right
  结论: x ⇨ y != x ↔ x != ⊤ ∨ y != ⊤
  证明: himp_eq_left.not.trans not_and_or

Depends on / 依赖: himp_eq_left, himp_eq_left.not.trans, not_and_or
-/
lemma himp_ne_right : x ⇨ y != x ↔ x != ⊤ ∨ y != ⊤ := himp_eq_left.not.trans not_and_or

/--
lemma `codisjoint_iff_compl_le_left` / 引理 `codisjoint_iff_compl_le_left`

English:
lemma codisjoint_iff_compl_le_left
  statement: Codisjoint x y ↔ yᶜ <= x
  proof: hnot_le_iff_codisjoint_left.symm

中文:
引理 codisjoint_iff_compl_le_left
  结论: Codisjoint x y ↔ yᶜ <= x
  证明: hnot_le_iff_codisjoint_left.symm

Depends on / 依赖: hnot_le_iff_codisjoint_left, hnot_le_iff_codisjoint_left.symm
-/
lemma codisjoint_iff_compl_le_left : Codisjoint x y ↔ yᶜ <= x :=
  hnot_le_iff_codisjoint_left.symm

/--
lemma `codisjoint_iff_compl_le_right` / 引理 `codisjoint_iff_compl_le_right`

English:
lemma codisjoint_iff_compl_le_right
  statement: Codisjoint x y ↔ xᶜ <= y
  proof: hnot_le_iff_codisjoint_right.symm

中文:
引理 codisjoint_iff_compl_le_right
  结论: Codisjoint x y ↔ xᶜ <= y
  证明: hnot_le_iff_codisjoint_right.symm

Depends on / 依赖: hnot_le_iff_codisjoint_right, hnot_le_iff_codisjoint_right.symm
-/
lemma codisjoint_iff_compl_le_right : Codisjoint x y ↔ xᶜ <= y :=
  hnot_le_iff_codisjoint_right.symm

end BooleanAlgebra

/--
Instance `Prod.instBooleanAlgebra` / 实例 `Prod.instBooleanAlgebra`

English:
instance Prod.instBooleanAlgebra
  signature: [BooleanAlgebra α] [BooleanAlgebra β]
  body: instDistribLattice α β
  __ := instHeytingAlgebra
  himp_eq x y := by ext <;> simp [himp_eq]
  sdiff_eq x y := by ext <;> simp [sdiff_eq]
  inf_compl_le_bot x := by constructor <;> simp
  top_le_sup_compl x := by constructor <;> simp

中文:
实例 积类型.inst布尔eanAlgebra
  签名: [布尔代数 α] [布尔代数 β]
  定义体: instDistribLattice α β
  __ := instHeytingAlgebra
  himp_eq x y := by ext <;> simp [himp_eq]
  sdiff_eq x y := by ext <;> simp [sdiff_eq]
  inf_compl_le_bot x := by constructor <;> simp
  top_le_sup_compl x := by constructor <;> simp

Depends on / 依赖: instDistribLattice
-/
instance Prod.instBooleanAlgebra [BooleanAlgebra α] [BooleanAlgebra β] :
    BooleanAlgebra (α × β) where
  __ := instDistribLattice α β
  __ := instHeytingAlgebra
  himp_eq x y := by ext <;> simp [himp_eq]
  sdiff_eq x y := by ext <;> simp [sdiff_eq]
  inf_compl_le_bot x := by constructor <;> simp
  top_le_sup_compl x := by constructor <;> simp

/--
Instance `Pi.instBooleanAlgebra` / 实例 `Pi.instBooleanAlgebra`

English:
instance Pi.instBooleanAlgebra
  signature: {ι : Type u} {α : ι -> Type v} [forall i, BooleanAlgebra (α i)]
  body: instDistribLattice
  __ := instHeytingAlgebra
  sdiff_eq _ _ := funext fun _ => sdiff_eq
  himp_eq _ _ := funext fun _ => himp_eq
  inf_compl_le_bot _ _ := BooleanAlgebra.inf_compl_le_bot _
  top_le_sup_compl _ _ := BooleanAlgebra.top_le_sup_compl _

中文:
实例 依赖函数类型.inst布尔eanAlgebra
  签名: {ι : 类型u} {α : ι -> 类型v} [对任意 i, 布尔代数 (α i)]
  定义体: instDistribLattice
  __ := instHeytingAlgebra
  sdiff_eq _ _ := funext fun _ => sdiff_eq
  himp_eq _ _ := funext fun _ => himp_eq
  inf_compl_le_bot _ _ := BooleanAlgebra.inf_compl_le_bot _
  top_le_sup_compl _ _ := BooleanAlgebra.top_le_sup_compl _

Depends on / 依赖: instDistribLattice
-/
instance Pi.instBooleanAlgebra {ι : Type u} {α : ι -> Type v} [forall i, BooleanAlgebra (α i)] :
    BooleanAlgebra (forall i, α i) where
  __ := instDistribLattice
  __ := instHeytingAlgebra
  sdiff_eq _ _ := funext fun _ => sdiff_eq
  himp_eq _ _ := funext fun _ => himp_eq
  inf_compl_le_bot _ _ := BooleanAlgebra.inf_compl_le_bot _
  top_le_sup_compl _ _ := BooleanAlgebra.top_le_sup_compl _

section lift

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.generalizedBooleanAlgebra` / `Function.Injective.generalizedBooleanAlgebra` 的定义

English:
abbreviation Function.Injective.generalizedBooleanAlgebra
  signature: [Max α] [Min α]
  body: hf.generalizedCoheytingAlgebra f le lt map_sup map_inf map_bot map_sdiff
  __ := hf.distribLattice f le lt map_sup map_inf
sup_inf_sdiff a b := hf by rw [map_sup, map_sdiff, map_inf, sup_inf_sdiff]
inf_inf_sdiff a b := hf by rw [map_inf, map_sdiff, map_inf, inf_inf_sdiff, map_bot]

中文:
缩写 函数.单射.generalized布尔eanAlgebra
  签名: [最大值 α] [最小值 α]
  定义体: hf.generalizedCoheytingAlgebra f le lt map_sup map_inf map_bot map_sdiff
  __ := hf.distribLattice f le lt map_sup map_inf
sup_inf_sdiff a b := hf by rw [map_sup, map_sdiff, map_inf, sup_inf_sdiff]
inf_inf_sdiff a b := hf by rw [map_inf, map_sdiff, map_inf, inf_inf_sdiff, map_bot]
-/
protected abbrev Function.Injective.generalizedBooleanAlgebra [Max α] [Min α]
    [LE α] [LT α] [Bot α] [SDiff α] [GeneralizedBooleanAlgebra β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_bot : f ⊥ = ⊥) (map_sdiff : forall a b, f (a \ b) = f a \ f b) :
    GeneralizedBooleanAlgebra α where
  __ := hf.generalizedCoheytingAlgebra f le lt map_sup map_inf map_bot map_sdiff
  __ := hf.distribLattice f le lt map_sup map_inf
sup_inf_sdiff a b := hf by rw [map_sup, map_sdiff, map_inf, sup_inf_sdiff]
inf_inf_sdiff a b := hf by rw [map_inf, map_sdiff, map_inf, inf_inf_sdiff, map_bot]

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.booleanAlgebra` / `Function.Injective.booleanAlgebra` 的定义

English:
abbreviation Function.Injective.booleanAlgebra
  signature: [Max α] [Min α] [LE α] [LT α] [Top α] [Bot α]
  body: hf.generalizedBooleanAlgebra f le lt map_sup map_inf map_bot map_sdiff
le_top _ := le.1 (@le_top β _ _ _).trans map_top.ge
bot_le _ := le.1 map_bot.le.trans bot_le
  inf_compl_le_bot a := le.1 ((map_inf _ _).trans <| by
    rw [map_compl]; rw [inf_compl_eq_bot]; rw [map_bot]).le
  top_le_sup_compl a

中文:
缩写 函数.单射.booleanAlgebra
  签名: [最大值 α] [最小值 α] [LE α] [LT α] [顶元素 α] [底元素 α]
  定义体: hf.generalizedBooleanAlgebra f le lt map_sup map_inf map_bot map_sdiff
le_top _ := le.1 (@le_top β _ _ _).trans map_top.ge
bot_le _ := le.1 map_bot.le.trans bot_le
  inf_compl_le_bot a := le.1 ((map_inf _ _).trans <| by
    rw [map_compl]; rw [inf_compl_eq_bot]; rw [map_bot]).le
  top_le_sup_compl a
-/
protected abbrev Function.Injective.booleanAlgebra [Max α] [Min α] [LE α] [LT α] [Top α] [Bot α]
    [Compl α] [SDiff α] [HImp α] [BooleanAlgebra β] (f : α -> β) (hf : Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : forall a, f aᶜ = (f a)ᶜ)
    (map_sdiff : forall a b, f (a \ b) = f a \ f b) (map_himp : forall a b, f (a ⇨ b) = f a ⇨ f b) :
    BooleanAlgebra α where
  __ := hf.generalizedBooleanAlgebra f le lt map_sup map_inf map_bot map_sdiff
le_top _ := le.1 (@le_top β _ _ _).trans map_top.ge
bot_le _ := le.1 map_bot.le.trans bot_le
  inf_compl_le_bot a := le.1 ((map_inf _ _).trans <| by
    rw [map_compl]; rw [inf_compl_eq_bot]; rw [map_bot]).le
  top_le_sup_compl a := le.1 ((map_sup _ _).trans <| by
    rw [map_compl]; rw [sup_compl_eq_top]; rw [map_top]).ge
sdiff_eq a b := hf (map_sdiff _ _).trans sdiff_eq.trans by rw [map_inf, map_compl]
himp_eq a b := hf (map_himp _ _).trans himp_eq.trans by rw [map_sup, map_compl]

namespace Equiv

variable (e : α ≃ β)

/--
Definition of `generalizedBooleanAlgebra` / `generalizedBooleanAlgebra` 的定义

English:
abbreviation generalizedBooleanAlgebra
  signature: [GeneralizedBooleanAlgebra β]
  body: by
  let bot := e.bot
  let sdiff := e.sdiff
  let distribLattice := e.distribLattice
  apply e.injective.generalizedBooleanAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

中文:
缩写 generalized布尔eanAlgebra
  签名: [Generalized布尔ean代数 β]
  定义体: by
  let bot := e.bot
  let sdiff := e.sdiff
  let distribLattice := e.distribLattice
  apply e.injective.generalizedBooleanAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _
-/
protected abbrev generalizedBooleanAlgebra [GeneralizedBooleanAlgebra β] :
    GeneralizedBooleanAlgebra α := by
  let bot := e.bot
  let sdiff := e.sdiff
  let distribLattice := e.distribLattice
  apply e.injective.generalizedBooleanAlgebra <;> intros <;>
  first | rfl | exact e.apply_symm_apply _

/--
Definition of `booleanAlgebra` / `booleanAlgebra` 的定义

English:
abbreviation booleanAlgebra
  signature: [BooleanAlgebra β]
  body: by
  let top := e.top
  let compl := e.compl
  let himp := e.himp
  let generalizedBooleanAlgebra := e.generalizedBooleanAlgebra
  apply e.injective.booleanAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 booleanAlgebra
  签名: [布尔代数 β]
  定义体: by
  let top := e.top
  let compl := e.compl
  let himp := e.himp
  let generalizedBooleanAlgebra := e.generalizedBooleanAlgebra
  apply e.injective.booleanAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev booleanAlgebra [BooleanAlgebra β] : BooleanAlgebra α := by
  let top := e.top
  let compl := e.compl
  let himp := e.himp
  let generalizedBooleanAlgebra := e.generalizedBooleanAlgebra
  apply e.injective.booleanAlgebra <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv

end lift
