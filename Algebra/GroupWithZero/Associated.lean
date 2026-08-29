/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Prime.Lemmas
public import Mathlib.Order.BoundedOrder.Basic

/-!
# Associated elements.

In this file we define an equivalence relation `Associated`
saying that two elements of a monoid differ by a multiplication by a unit.
Then we show that the quotient type `Associates` is a monoid
and prove basic properties of this quotient.
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Multiset Ring

variable {M : Type*}

/--
Definition of `Associated` / `Associated` 的定义

English:
definition Associated
  signature: [Monoid M] (x y : M)
  body: exists u : Mˣ, x * u = y

中文:
定义 Associated
  签名: [Monoid M] (x y : M)
  定义体: exists u : Mˣ, x * u = y
-/
def Associated [Monoid M] (x y : M) : Prop :=
  exists u : Mˣ, x * u = y

/-- Notation for two elements of a monoid being associated, i.e.
if one of them is another one multiplied by a unit on the right. -/
local infixl:50 " ~ᵤ " => Associated

namespace Associated

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: [Monoid M] (x : M)
  statement: x ~ᵤ x
  proof: ⟨1, by simp⟩

@[simp]

中文:
定理 refl
  条件: [Monoid M] (x : M)
  结论: x ~ᵤ x
  证明: ⟨1, by simp⟩

@[simp]

Depends on / 依赖: CochainComplex
-/
protected theorem refl [Monoid M] (x : M) : x ~ᵤ x :=
  ⟨1, by simp⟩

@[simp]
/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  given: [Monoid M] {x : M}
  statement: x ~ᵤ x
  proof: .refl x

中文:
定理 rfl
  条件: [Monoid M] {x : M}
  结论: x ~ᵤ x
  证明: .refl x
-/
protected theorem rfl [Monoid M] {x : M} : x ~ᵤ x :=
  .refl x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] : @Std.Refl M Associated
  body: ⟨Associated.refl⟩

@[symm]

中文:
实例 [Monoid
  签名: M] : @Std.Refl M Associated
  定义体: ⟨Associated.refl⟩

@[symm]

Depends on / 依赖: Associated, Associated.refl
-/
instance [Monoid M] : @Std.Refl M Associated :=
  ⟨Associated.refl⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: [Monoid M]
  statement: forall {x y : M}, x ~ᵤ y -> y ~ᵤ x

中文:
定理 symm
  条件: [Monoid M]
  结论: 对任意 {x y : M}, x ~ᵤ y -> y ~ᵤ x
-/
protected theorem symm [Monoid M] : forall {x y : M}, x ~ᵤ y -> y ~ᵤ x
  | x, _, ⟨u, rfl⟩ => ⟨u⁻¹, by rw [mul_assoc, Units.mul_inv, mul_one]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] : Std.Symm (α
  body: ⟨fun _ _ => Associated.symm⟩

中文:
实例 [Monoid
  签名: M] : Std.Symm (α
  定义体: ⟨fun _ _ => Associated.symm⟩

Depends on / 依赖: Associated
-/
instance [Monoid M] : Std.Symm (α := M) Associated :=
  ⟨fun _ _ => Associated.symm⟩

/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  given: [Monoid M] {x y : M}
  statement: x ~ᵤ y ↔ y ~ᵤ x
  proof: ⟨Associated.symm, Associated.symm⟩

@[trans]

中文:
定理 comm
  条件: [Monoid M] {x y : M}
  结论: x ~ᵤ y ↔ y ~ᵤ x
  证明: ⟨Associated.symm, Associated.symm⟩

@[trans]
-/
protected theorem comm [Monoid M] {x y : M} : x ~ᵤ y ↔ y ~ᵤ x :=
  ⟨Associated.symm, Associated.symm⟩

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: [Monoid M]
  statement: forall {x y z : M}, x ~ᵤ y -> y ~ᵤ z -> x ~ᵤ z

中文:
定理 trans
  条件: [Monoid M]
  结论: 对任意 {x y z : M}, x ~ᵤ y -> y ~ᵤ z -> x ~ᵤ z
-/
protected theorem trans [Monoid M] : forall {x y z : M}, x ~ᵤ y -> y ~ᵤ z -> x ~ᵤ z
  | x, _, _, ⟨u, rfl⟩, ⟨v, rfl⟩ => ⟨u * v, by rw [Units.val_mul, mul_assoc]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] : IsTrans M Associated
  body: ⟨fun _ _ _ => Associated.trans⟩

中文:
实例 [Monoid
  签名: M] : IsTrans M Associated
  定义体: ⟨fun _ _ _ => Associated.trans⟩

Depends on / 依赖: Associated, Associated.trans
-/
instance [Monoid M] : IsTrans M Associated :=
  ⟨fun _ _ _ => Associated.trans⟩

/-- The setoid of the relation `x ~ᵤ y` iff there is a unit `u` such that `x * u = y` -/
@[instance_reducible]
/--
Definition of `setoid` / `setoid` 的定义

English:
definition setoid
  signature: (M : Type*) [Monoid M]
  body: Associated
  iseqv := ⟨Associated.refl, Associated.symm, Associated.trans⟩

中文:
定义 setoid
  签名: (M : 类型) [Monoid M]
  定义体: Associated
  iseqv := ⟨Associated.refl, Associated.symm, Associated.trans⟩
-/
protected def setoid (M : Type*) [Monoid M] :
    Setoid M where
  r := Associated
  iseqv := ⟨Associated.refl, Associated.symm, Associated.trans⟩

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: {M N : Type*} [Monoid M] [Monoid N] {F : Type*} [FunLike F M N] [MonoidHomClass F M N]
  proof: by
  obtain ⟨u, ha⟩ := ha
  exact ⟨Units.map f u, by rw [← ha, map_mul, Units.coe_map, MonoidHom.coe_coe]⟩

中文:
定理 map
  结论: {M N : 类型} [Monoid M] [Monoid N] {F : 类型} [FunLike F M N] [MonoidHomClass F M N]
  证明: by
  obtain ⟨u, ha⟩ := ha
  exact ⟨Units.map f u, by rw [← ha, map_mul, Units.coe_map, MonoidHom.coe_coe]⟩

Depends on / 依赖: MonoidHom, MonoidHom.coe_coe, Units.coe_map, Units.map, coe_coe, coe_map, map_mul
-/
theorem map {M N : Type*} [Monoid M] [Monoid N] {F : Type*} [FunLike F M N] [MonoidHomClass F M N]
    (f : F) {x y : M} (ha : Associated x y) : Associated (f x) (f y) := by
  obtain ⟨u, ha⟩ := ha
  exact ⟨Units.map f u, by rw [← ha, map_mul, Units.coe_map, MonoidHom.coe_coe]⟩

end Associated

attribute [local instance] Associated.setoid

/--
theorem `Associated.of_eq` / 定理 `Associated.of_eq`

English:
theorem Associated.of_eq
  given: [Monoid M] {a b : M} (h : a = b)
  statement: a ~ᵤ b
  proof: ⟨1, by rwa [Units.val_one, mul_one]⟩

中文:
定理 Associated.of_eq
  条件: [Monoid M] {a b : M} (h : a = b)
  结论: a ~ᵤ b
  证明: ⟨1, by rwa [Units.val_one, mul_one]⟩

Depends on / 依赖: Units.val_one, mul_one, val_one
-/
theorem Associated.of_eq [Monoid M] {a b : M} (h : a = b) : a ~ᵤ b :=
  ⟨1, by rwa [Units.val_one, mul_one]⟩

/--
theorem `Associated.of_subsingleton` / 定理 `Associated.of_subsingleton`

English:
theorem Associated.of_subsingleton
  given: [Subsingleton M] [Monoid M] (a b : M)
  proof: .of_eq (Subsingleton.elim ..)

中文:
定理 Associated.of_subsingleton
  条件: [Subsingleton M] [Monoid M] (a b : M)
  证明: .of_eq (Subsingleton.elim ..)
-/
@[nontriviality] theorem Associated.of_subsingleton [Subsingleton M] [Monoid M] (a b : M) :
    Associated a b := .of_eq (Subsingleton.elim ..)

/--
theorem `unit_associated_one` / 定理 `unit_associated_one`

English:
theorem unit_associated_one
  given: [Monoid M] {u : Mˣ}
  statement: (u : M) ~ᵤ 1
  proof: ⟨u⁻¹, Units.mul_inv u⟩

@[simp]

中文:
定理 unit_associated_one
  条件: [Monoid M] {u : Mˣ}
  结论: (u : M) ~ᵤ 1
  证明: ⟨u⁻¹, Units.mul_inv u⟩

@[simp]

Depends on / 依赖: Units.mul_inv, mul_inv
-/
theorem unit_associated_one [Monoid M] {u : Mˣ} : (u : M) ~ᵤ 1 :=
  ⟨u⁻¹, Units.mul_inv u⟩

@[simp]
/--
theorem `associated_one_iff_isUnit` / 定理 `associated_one_iff_isUnit`

English:
theorem associated_one_iff_isUnit
  given: [Monoid M] {a : M}
  statement: (a : M) ~ᵤ 1 ↔ IsUnit a
  proof: Iff.intro
    (fun h =>
      let ⟨c, h⟩ := h.symm
      h ▸ ⟨c, (one_mul _).symm⟩)
    fun ⟨c, h⟩ => Associated.symm ⟨c, by simp [h]⟩

@[simp]

中文:
定理 associated_one_iff_isUnit
  条件: [Monoid M] {a : M}
  结论: (a : M) ~ᵤ 1 ↔ IsUnit a
  证明: Iff.intro
    (fun h =>
      let ⟨c, h⟩ := h.symm
      h ▸ ⟨c, (one_mul _).symm⟩)
    fun ⟨c, h⟩ => Associated.symm ⟨c, by simp [h]⟩

@[simp]

Depends on / 依赖: Associated, Associated.symm, Iff.intro, h.symm, one_mul
-/
theorem associated_one_iff_isUnit [Monoid M] {a : M} : (a : M) ~ᵤ 1 ↔ IsUnit a :=
  Iff.intro
    (fun h =>
      let ⟨c, h⟩ := h.symm
      h ▸ ⟨c, (one_mul _).symm⟩)
    fun ⟨c, h⟩ => Associated.symm ⟨c, by simp [h]⟩

@[simp]
/--
theorem `associated_zero_iff_eq_zero` / 定理 `associated_zero_iff_eq_zero`

English:
theorem associated_zero_iff_eq_zero
  given: [MonoidWithZero M] (a : M)
  statement: a ~ᵤ 0 ↔ a = 0
  proof: Iff.intro
    (fun h => by
      let ⟨u, h⟩ := h.symm
      simpa using h.symm)
    fun h => h ▸ Associated.refl a

中文:
定理 associated_zero_iff_eq_zero
  条件: [MonoidWithZero M] (a : M)
  结论: a ~ᵤ 0 ↔ a = 0
  证明: Iff.intro
    (fun h => by
      let ⟨u, h⟩ := h.symm
      simpa using h.symm)
    fun h => h ▸ Associated.refl a

Depends on / 依赖: Associated, Associated.refl, Iff.intro, h.symm
-/
theorem associated_zero_iff_eq_zero [MonoidWithZero M] (a : M) : a ~ᵤ 0 ↔ a = 0 :=
  Iff.intro
    (fun h => by
      let ⟨u, h⟩ := h.symm
      simpa using h.symm)
    fun h => h ▸ Associated.refl a

/--
theorem `associated_one_of_mul_eq_one` / 定理 `associated_one_of_mul_eq_one`

English:
theorem associated_one_of_mul_eq_one
  given: [CommMonoid M] {a : M} (b : M) (hab : a * b = 1)
  statement: a ~ᵤ 1
  proof: show (Units.mkOfMulEqOne a b hab : M) ~ᵤ 1 from unit_associated_one

中文:
定理 associated_one_of_mul_eq_one
  条件: [CommMonoid M] {a : M} (b : M) (hab : a * b = 1)
  结论: a ~ᵤ 1
  证明: show (Units.mkOfMulEqOne a b hab : M) ~ᵤ 1 from unit_associated_one

Depends on / 依赖: Units.mkOfMulEqOne, mkOfMulEqOne, unit_associated_one
-/
theorem associated_one_of_mul_eq_one [CommMonoid M] {a : M} (b : M) (hab : a * b = 1) : a ~ᵤ 1 :=
  show (Units.mkOfMulEqOne a b hab : M) ~ᵤ 1 from unit_associated_one

/--
theorem `associated_one_of_associated_mul_one` / 定理 `associated_one_of_associated_mul_one`

English:
theorem associated_one_of_associated_mul_one
  given: [CommMonoid M] {a b : M}
  statement: a * b ~ᵤ 1 -> a ~ᵤ 1

中文:
定理 associated_one_of_associated_mul_one
  条件: [CommMonoid M] {a b : M}
  结论: a * b ~ᵤ 1 -> a ~ᵤ 1
-/
theorem associated_one_of_associated_mul_one [CommMonoid M] {a b : M} : a * b ~ᵤ 1 -> a ~ᵤ 1
| ⟨u, h⟩ => associated_one_of_mul_eq_one (b * u) by simpa [mul_assoc] using h

/--
theorem `associated_mul_unit_left` / 定理 `associated_mul_unit_left`

English:
theorem associated_mul_unit_left
  given: {N : Type*} [Monoid N] (a u : N) (hu : IsUnit u)
  proof: let ⟨u', hu⟩ := hu
  ⟨u'⁻¹, hu ▸ Units.mul_inv_cancel_right _ _⟩

中文:
定理 associated_mul_unit_left
  条件: {N : 类型} [Monoid N] (a u : N) (hu : IsUnit u)
  证明: let ⟨u', hu⟩ := hu
  ⟨u'⁻¹, hu ▸ Units.mul_inv_cancel_right _ _⟩

Depends on / 依赖: Units.mul_inv_cancel_right, mul_inv_cancel_right
-/
theorem associated_mul_unit_left {N : Type*} [Monoid N] (a u : N) (hu : IsUnit u) :
    Associated (a * u) a :=
  let ⟨u', hu⟩ := hu
  ⟨u'⁻¹, hu ▸ Units.mul_inv_cancel_right _ _⟩

/--
theorem `associated_unit_mul_left` / 定理 `associated_unit_mul_left`

English:
theorem associated_unit_mul_left
  given: {N : Type*} [CommMonoid N] (a u : N) (hu : IsUnit u)
  proof: by
  rw [mul_comm]
  exact associated_mul_unit_left _ _ hu

中文:
定理 associated_unit_mul_left
  条件: {N : 类型} [CommMonoid N] (a u : N) (hu : IsUnit u)
  证明: by
  rw [mul_comm]
  exact associated_mul_unit_left _ _ hu

Depends on / 依赖: associated_mul_unit_left, mul_comm
-/
theorem associated_unit_mul_left {N : Type*} [CommMonoid N] (a u : N) (hu : IsUnit u) :
    Associated (u * a) a := by
  rw [mul_comm]
  exact associated_mul_unit_left _ _ hu

/--
theorem `associated_mul_unit_right` / 定理 `associated_mul_unit_right`

English:
theorem associated_mul_unit_right
  given: {N : Type*} [Monoid N] (a u : N) (hu : IsUnit u)
  proof: (associated_mul_unit_left a u hu).symm

中文:
定理 associated_mul_unit_right
  条件: {N : 类型} [Monoid N] (a u : N) (hu : IsUnit u)
  证明: (associated_mul_unit_left a u hu).symm

Depends on / 依赖: associated_mul_unit_left
-/
theorem associated_mul_unit_right {N : Type*} [Monoid N] (a u : N) (hu : IsUnit u) :
    Associated a (a * u) :=
  (associated_mul_unit_left a u hu).symm

/--
theorem `associated_unit_mul_right` / 定理 `associated_unit_mul_right`

English:
theorem associated_unit_mul_right
  given: {N : Type*} [CommMonoid N] (a u : N) (hu : IsUnit u)
  proof: (associated_unit_mul_left a u hu).symm

中文:
定理 associated_unit_mul_right
  条件: {N : 类型} [CommMonoid N] (a u : N) (hu : IsUnit u)
  证明: (associated_unit_mul_left a u hu).symm

Depends on / 依赖: Finset, Finset.image, Finset.min, HomologicalComplex, HomologicalComplex.eval, IsStrictlyGE, IsZero, IsZero.iff_id_eq_zero, associated_unit_mul_left, eq_of_tgt, hom_ext, iff_id_eq_zero, isLimit, isLimitOfPreserves, isStrictlyGE_iff, isStrictlyGE_of_ge, isZero_of_isStrictlyGE, p.diag.obj, p.isLimit, p.prop_diag_obj
-/
theorem associated_unit_mul_right {N : Type*} [CommMonoid N] (a u : N) (hu : IsUnit u) :
    Associated a (u * a) :=
  (associated_unit_mul_left a u hu).symm

/--
theorem `associated_mul_isUnit_left_iff` / 定理 `associated_mul_isUnit_left_iff`

English:
theorem associated_mul_isUnit_left_iff
  given: {N : Type*} [Monoid N] {a u b : N} (hu : IsUnit u)
  proof: ⟨(associated_mul_unit_right _ _ hu).trans, (associated_mul_unit_left _ _ hu).trans⟩

中文:
定理 associated_mul_isUnit_left_iff
  条件: {N : 类型} [Monoid N] {a u b : N} (hu : IsUnit u)
  证明: ⟨(associated_mul_unit_right _ _ hu).trans, (associated_mul_unit_left _ _ hu).trans⟩

Depends on / 依赖: Finset, Finset.image, Finset.min, HomologicalComplex, HomologicalComplex.eval, IsStrictlyGE, IsZero, IsZero.iff_id_eq_zero, associated_mul_unit_left, associated_mul_unit_right, eq_of_s, hom_ext, iff_id_eq_zero, isColimit, isColimitOfPreserves, isStrictlyGE_iff, isStrictlyGE_of_ge, isZero_of_isStrictlyGE, p.diag.obj, p.isColimit
-/
theorem associated_mul_isUnit_left_iff {N : Type*} [Monoid N] {a u b : N} (hu : IsUnit u) :
    Associated (a * u) b ↔ Associated a b :=
  ⟨(associated_mul_unit_right _ _ hu).trans, (associated_mul_unit_left _ _ hu).trans⟩

/--
theorem `associated_isUnit_mul_left_iff` / 定理 `associated_isUnit_mul_left_iff`

English:
theorem associated_isUnit_mul_left_iff
  given: {N : Type*} [CommMonoid N] {u a b : N} (hu : IsUnit u)
  proof: by
  rw [mul_comm]
  exact associated_mul_isUnit_left_iff hu

中文:
定理 associated_isUnit_mul_left_iff
  条件: {N : 类型} [CommMonoid N] {u a b : N} (hu : IsUnit u)
  证明: by
  rw [mul_comm]
  exact associated_mul_isUnit_left_iff hu

Depends on / 依赖: associated_mul_isUnit_left_iff, mul_comm
-/
theorem associated_isUnit_mul_left_iff {N : Type*} [CommMonoid N] {u a b : N} (hu : IsUnit u) :
    Associated (u * a) b ↔ Associated a b := by
  rw [mul_comm]
  exact associated_mul_isUnit_left_iff hu

/--
theorem `associated_mul_isUnit_right_iff` / 定理 `associated_mul_isUnit_right_iff`

English:
theorem associated_mul_isUnit_right_iff
  given: {N : Type*} [Monoid N] {a b u : N} (hu : IsUnit u)
  proof: Associated.comm.trans (associated_mul_isUnit_left_iff hu).trans Associated.comm

中文:
定理 associated_mul_isUnit_right_iff
  条件: {N : 类型} [Monoid N] {a b u : N} (hu : IsUnit u)
  证明: Associated.comm.trans (associated_mul_isUnit_left_iff hu).trans Associated.comm

Depends on / 依赖: Associated, Associated.comm, Associated.comm.trans, associated_mul_isUnit_left_iff
-/
theorem associated_mul_isUnit_right_iff {N : Type*} [Monoid N] {a b u : N} (hu : IsUnit u) :
    Associated a (b * u) ↔ Associated a b :=
Associated.comm.trans (associated_mul_isUnit_left_iff hu).trans Associated.comm

/--
theorem `associated_isUnit_mul_right_iff` / 定理 `associated_isUnit_mul_right_iff`

English:
theorem associated_isUnit_mul_right_iff
  given: {N : Type*} [CommMonoid N] {a u b : N} (hu : IsUnit u)
  proof: Associated.comm.trans (associated_isUnit_mul_left_iff hu).trans Associated.comm

@[simp]

中文:
定理 associated_isUnit_mul_right_iff
  条件: {N : 类型} [CommMonoid N] {a u b : N} (hu : IsUnit u)
  证明: Associated.comm.trans (associated_isUnit_mul_left_iff hu).trans Associated.comm

@[simp]

Depends on / 依赖: Associated, Associated.comm, Associated.comm.trans, associated_isUnit_mul_left_iff
-/
theorem associated_isUnit_mul_right_iff {N : Type*} [CommMonoid N] {a u b : N} (hu : IsUnit u) :
    Associated a (u * b) ↔ Associated a b :=
Associated.comm.trans (associated_isUnit_mul_left_iff hu).trans Associated.comm

@[simp]
/--
theorem `associated_mul_unit_left_iff` / 定理 `associated_mul_unit_left_iff`

English:
theorem associated_mul_unit_left_iff
  given: {N : Type*} [Monoid N] {a b : N} {u : Units N}
  proof: associated_mul_isUnit_left_iff u.isUnit

@[simp]

中文:
定理 associated_mul_unit_left_iff
  条件: {N : 类型} [Monoid N] {a b : N} {u : Units N}
  证明: associated_mul_isUnit_left_iff u.isUnit

@[simp]

Depends on / 依赖: associated_mul_isUnit_left_iff, isUnit, u.isUnit
-/
theorem associated_mul_unit_left_iff {N : Type*} [Monoid N] {a b : N} {u : Units N} :
    Associated (a * u) b ↔ Associated a b :=
  associated_mul_isUnit_left_iff u.isUnit

@[simp]
/--
theorem `associated_unit_mul_left_iff` / 定理 `associated_unit_mul_left_iff`

English:
theorem associated_unit_mul_left_iff
  given: {N : Type*} [CommMonoid N] {a b : N} {u : Units N}
  proof: associated_isUnit_mul_left_iff u.isUnit

@[simp]

中文:
定理 associated_unit_mul_left_iff
  条件: {N : 类型} [CommMonoid N] {a b : N} {u : Units N}
  证明: associated_isUnit_mul_left_iff u.isUnit

@[simp]

Depends on / 依赖: associated_isUnit_mul_left_iff, isUnit, u.isUnit
-/
theorem associated_unit_mul_left_iff {N : Type*} [CommMonoid N] {a b : N} {u : Units N} :
    Associated (↑u * a) b ↔ Associated a b :=
  associated_isUnit_mul_left_iff u.isUnit

@[simp]
/--
theorem `associated_mul_unit_right_iff` / 定理 `associated_mul_unit_right_iff`

English:
theorem associated_mul_unit_right_iff
  given: {N : Type*} [Monoid N] {a b : N} {u : Units N}
  proof: associated_mul_isUnit_right_iff u.isUnit

@[simp]

中文:
定理 associated_mul_unit_right_iff
  条件: {N : 类型} [Monoid N] {a b : N} {u : Units N}
  证明: associated_mul_isUnit_right_iff u.isUnit

@[simp]

Depends on / 依赖: associated_mul_isUnit_right_iff, isUnit, u.isUnit
-/
theorem associated_mul_unit_right_iff {N : Type*} [Monoid N] {a b : N} {u : Units N} :
    Associated a (b * u) ↔ Associated a b :=
  associated_mul_isUnit_right_iff u.isUnit

@[simp]
/--
theorem `associated_unit_mul_right_iff` / 定理 `associated_unit_mul_right_iff`

English:
theorem associated_unit_mul_right_iff
  given: {N : Type*} [CommMonoid N] {a b : N} {u : Units N}
  proof: associated_isUnit_mul_right_iff u.isUnit

@[gcongr]

中文:
定理 associated_unit_mul_right_iff
  条件: {N : 类型} [CommMonoid N] {a b : N} {u : Units N}
  证明: associated_isUnit_mul_right_iff u.isUnit

@[gcongr]

Depends on / 依赖: associated_isUnit_mul_right_iff, isUnit, u.isUnit
-/
theorem associated_unit_mul_right_iff {N : Type*} [CommMonoid N] {a b : N} {u : Units N} :
    Associated a (↑u * b) ↔ Associated a b :=
  associated_isUnit_mul_right_iff u.isUnit

@[gcongr]
/--
theorem `Associated.mul_left` / 定理 `Associated.mul_left`

English:
theorem Associated.mul_left
  given: [Monoid M] (a : M) {b c : M} (h : b ~ᵤ c)
  statement: a * b ~ᵤ a * c
  proof: by
  obtain ⟨d, rfl⟩ := h; exact ⟨d, mul_assoc _ _ _⟩

@[gcongr]

中文:
定理 Associated.mul_left
  条件: [Monoid M] (a : M) {b c : M} (h : b ~ᵤ c)
  结论: a * b ~ᵤ a * c
  证明: by
  obtain ⟨d, rfl⟩ := h; exact ⟨d, mul_assoc _ _ _⟩

@[gcongr]

Depends on / 依赖: mul_assoc
-/
theorem Associated.mul_left [Monoid M] (a : M) {b c : M} (h : b ~ᵤ c) : a * b ~ᵤ a * c := by
  obtain ⟨d, rfl⟩ := h; exact ⟨d, mul_assoc _ _ _⟩

@[gcongr]
/--
theorem `Associated.mul_right` / 定理 `Associated.mul_right`

English:
theorem Associated.mul_right
  given: [CommMonoid M] {a b : M} (h : a ~ᵤ b) (c : M)
  statement: a * c ~ᵤ b * c
  proof: by
  obtain ⟨d, rfl⟩ := h; exact ⟨d, mul_right_comm _ _ _⟩

@[gcongr]

中文:
定理 Associated.mul_right
  条件: [CommMonoid M] {a b : M} (h : a ~ᵤ b) (c : M)
  结论: a * c ~ᵤ b * c
  证明: by
  obtain ⟨d, rfl⟩ := h; exact ⟨d, mul_right_comm _ _ _⟩

@[gcongr]

Depends on / 依赖: mul_right_comm
-/
theorem Associated.mul_right [CommMonoid M] {a b : M} (h : a ~ᵤ b) (c : M) : a * c ~ᵤ b * c := by
  obtain ⟨d, rfl⟩ := h; exact ⟨d, mul_right_comm _ _ _⟩

@[gcongr]
/--
theorem `Associated.mul_mul` / 定理 `Associated.mul_mul`

English:
theorem Associated.mul_mul
  statement: [CommMonoid M] {a₁ a₂ b₁ b₂ : M}
  proof: (h₁.mul_right _).trans (h₂.mul_left _)

@[gcongr]

中文:
定理 Associated.mul_mul
  结论: [CommMonoid M] {a₁ a₂ b₁ b₂ : M}
  证明: (h₁.mul_right _).trans (h₂.mul_left _)

@[gcongr]

Depends on / 依赖: mul_left, mul_right
-/
theorem Associated.mul_mul [CommMonoid M] {a₁ a₂ b₁ b₂ : M}
    (h₁ : a₁ ~ᵤ b₁) (h₂ : a₂ ~ᵤ b₂) : a₁ * a₂ ~ᵤ b₁ * b₂ := (h₁.mul_right _).trans (h₂.mul_left _)

@[gcongr]
/--
theorem `Associated.pow_pow` / 定理 `Associated.pow_pow`

English:
theorem Associated.pow_pow
  given: [CommMonoid M] {a b : M} {n : Nat} (h : a ~ᵤ b)
  statement: a ^ n ~ᵤ b ^ n
  proof: by
  induction n with
  | zero => simp [Associated.refl]
  | succ n ih => convert! h.mul_mul ih <;> rw [pow_succ']

中文:
定理 Associated.pow_pow
  条件: [CommMonoid M] {a b : M} {n : 自然数} (h : a ~ᵤ b)
  结论: a ^ n ~ᵤ b ^ n
  证明: by
  induction n with
  | zero => simp [Associated.refl]
  | succ n ih => convert! h.mul_mul ih <;> rw [pow_succ']

Depends on / 依赖: Associated, Associated.refl, convert, h.mul_mul, mul_mul, pow_succ
-/
theorem Associated.pow_pow [CommMonoid M] {a b : M} {n : Nat} (h : a ~ᵤ b) : a ^ n ~ᵤ b ^ n := by
  induction n with
  | zero => simp [Associated.refl]
  | succ n ih => convert! h.mul_mul ih <;> rw [pow_succ']

/--
theorem `Associated.dvd` / 定理 `Associated.dvd`

English:
theorem Associated.dvd
  given: [Monoid M] {a b : M}
  statement: a ~ᵤ b -> a ∣ b
  proof: fun ⟨u, hu⟩ =>
  ⟨u, hu.symm⟩

中文:
定理 Associated.dvd
  条件: [Monoid M] {a b : M}
  结论: a ~ᵤ b -> a ∣ b
  证明: fun ⟨u, hu⟩ =>
  ⟨u, hu.symm⟩
-/
protected theorem Associated.dvd [Monoid M] {a b : M} : a ~ᵤ b -> a ∣ b := fun ⟨u, hu⟩ =>
  ⟨u, hu.symm⟩

/--
theorem `Associated.dvd'` / 定理 `Associated.dvd'`

English:
theorem Associated.dvd'
  given: [Monoid M] {a b : M} (h : a ~ᵤ b)
  statement: b ∣ a
  proof: h.symm.dvd

中文:
定理 Associated.dvd'
  条件: [Monoid M] {a b : M} (h : a ~ᵤ b)
  结论: b ∣ a
  证明: h.symm.dvd
-/
protected theorem Associated.dvd' [Monoid M] {a b : M} (h : a ~ᵤ b) : b ∣ a :=
  h.symm.dvd

/--
theorem `Associated.dvd_dvd` / 定理 `Associated.dvd_dvd`

English:
theorem Associated.dvd_dvd
  given: [Monoid M] {a b : M} (h : a ~ᵤ b)
  statement: a ∣ b ∧ b ∣ a
  proof: ⟨h.dvd, h.symm.dvd⟩

中文:
定理 Associated.dvd_dvd
  条件: [Monoid M] {a b : M} (h : a ~ᵤ b)
  结论: a ∣ b ∧ b ∣ a
  证明: ⟨h.dvd, h.symm.dvd⟩
-/
protected theorem Associated.dvd_dvd [Monoid M] {a b : M} (h : a ~ᵤ b) : a ∣ b ∧ b ∣ a :=
  ⟨h.dvd, h.symm.dvd⟩

/--
theorem `associated_of_dvd_dvd` / 定理 `associated_of_dvd_dvd`

English:
theorem associated_of_dvd_dvd
  statement: [MonoidWithZero M] [IsLeftCancelMulZero M] {a b : M}
  proof: by
  rcases hab with ⟨c, rfl⟩
  rcases hba with ⟨d, a_eq⟩
  by_cases ha0 : a = 0
  · simp_all
  have hac0 : a * c != 0 := by
    intro con
    rw [con]; rw [zero_mul] at a_eq
    apply ha0 a_eq
  have : a * (c * d) = a * 1 := by rw [← mul_assoc, ← a_eq, mul_one]
  have hcd : c * d = 1 := mul_left_ca

中文:
定理 associated_of_dvd_dvd
  结论: [MonoidWithZero M] [IsLeftCancelMulZero M] {a b : M}
  证明: by
  rcases hab with ⟨c, rfl⟩
  rcases hba with ⟨d, a_eq⟩
  by_cases ha0 : a = 0
  · simp_all
  have hac0 : a * c != 0 := by
    intro con
    rw [con]; rw [zero_mul] at a_eq
    apply ha0 a_eq
  have : a * (c * d) = a * 1 := by rw [← mul_assoc, ← a_eq, mul_one]
  have hcd : c * d = 1 := mul_left_ca

Depends on / 依赖: a_eq, mul_assoc, mul_one, zero_mul
-/
theorem associated_of_dvd_dvd [MonoidWithZero M] [IsLeftCancelMulZero M] {a b : M}
    (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b := by
  rcases hab with ⟨c, rfl⟩
  rcases hba with ⟨d, a_eq⟩
  by_cases ha0 : a = 0
  · simp_all
  have hac0 : a * c != 0 := by
    intro con
    rw [con]; rw [zero_mul] at a_eq
    apply ha0 a_eq
  have : a * (c * d) = a * 1 := by rw [← mul_assoc, ← a_eq, mul_one]
  have hcd : c * d = 1 := mul_left_cancel₀ ha0 this
  have : a * c * (d * c) = a * c * 1 := by rw [← mul_assoc, ← a_eq, mul_one]
  have hdc : d * c = 1 := mul_left_cancel₀ hac0 this
  exact ⟨⟨c, d, hcd, hdc⟩, rfl⟩

/--
theorem `dvd_dvd_iff_associated` / 定理 `dvd_dvd_iff_associated`

English:
theorem dvd_dvd_iff_associated
  given: [MonoidWithZero M] [IsLeftCancelMulZero M] {a b : M}
  proof: ⟨fun ⟨h1, h2⟩ => associated_of_dvd_dvd h1 h2, Associated.dvd_dvd⟩

中文:
定理 dvd_dvd_iff_associated
  条件: [MonoidWithZero M] [IsLeftCancelMulZero M] {a b : M}
  证明: ⟨fun ⟨h1, h2⟩ => associated_of_dvd_dvd h1 h2, Associated.dvd_dvd⟩

Depends on / 依赖: Associated, Associated.dvd_dvd, associated_of_dvd_dvd, dvd_dvd
-/
theorem dvd_dvd_iff_associated [MonoidWithZero M] [IsLeftCancelMulZero M] {a b : M} :
    a ∣ b ∧ b ∣ a ↔ a ~ᵤ b :=
  ⟨fun ⟨h1, h2⟩ => associated_of_dvd_dvd h1 h2, Associated.dvd_dvd⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidWithZero
  signature: M] [IsLeftCancelMulZero M] [DecidableRel ((· ∣ ·) : M -> M -> Prop)] :
  body: fun _ _ => decidable_of_iff _ dvd_dvd_iff_associated

中文:
实例 [MonoidWithZero
  签名: M] [IsLeftCancelMulZero M] [DecidableRel ((· ∣ ·) : M -> M -> 命题)] :
  定义体: fun _ _ => decidable_of_iff _ dvd_dvd_iff_associated

Depends on / 依赖: decidable_of_iff, dvd_dvd_iff_associated
-/
instance [MonoidWithZero M] [IsLeftCancelMulZero M] [DecidableRel ((· ∣ ·) : M -> M -> Prop)] :
    DecidableRel ((· ~ᵤ ·) : M -> M -> Prop) := fun _ _ => decidable_of_iff _ dvd_dvd_iff_associated

/--
theorem `Associated.dvd_iff_dvd_left` / 定理 `Associated.dvd_iff_dvd_left`

English:
theorem Associated.dvd_iff_dvd_left
  given: [Monoid M] {a b c : M} (h : a ~ᵤ b)
  statement: a ∣ c ↔ b ∣ c
  proof: let ⟨_, hu⟩ := h
  hu ▸ Units.mul_right_dvd.symm

中文:
定理 Associated.dvd_iff_dvd_left
  条件: [Monoid M] {a b c : M} (h : a ~ᵤ b)
  结论: a ∣ c ↔ b ∣ c
  证明: let ⟨_, hu⟩ := h
  hu ▸ Units.mul_right_dvd.symm

Depends on / 依赖: Units.mul_right_dvd.symm, mul_right_dvd
-/
theorem Associated.dvd_iff_dvd_left [Monoid M] {a b c : M} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c :=
  let ⟨_, hu⟩ := h
  hu ▸ Units.mul_right_dvd.symm

/--
theorem `Associated.dvd_iff_dvd_right` / 定理 `Associated.dvd_iff_dvd_right`

English:
theorem Associated.dvd_iff_dvd_right
  given: [Monoid M] {a b c : M} (h : b ~ᵤ c)
  statement: a ∣ b ↔ a ∣ c
  proof: let ⟨_, hu⟩ := h
  hu ▸ Units.dvd_mul_right.symm

中文:
定理 Associated.dvd_iff_dvd_right
  条件: [Monoid M] {a b c : M} (h : b ~ᵤ c)
  结论: a ∣ b ↔ a ∣ c
  证明: let ⟨_, hu⟩ := h
  hu ▸ Units.dvd_mul_right.symm

Depends on / 依赖: Units.dvd_mul_right.symm, dvd_mul_right
-/
theorem Associated.dvd_iff_dvd_right [Monoid M] {a b c : M} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c :=
  let ⟨_, hu⟩ := h
  hu ▸ Units.dvd_mul_right.symm

/--
theorem `Associated.eq_zero_iff` / 定理 `Associated.eq_zero_iff`

English:
theorem Associated.eq_zero_iff
  given: [MonoidWithZero M] {a b : M} (h : a ~ᵤ b)
  statement: a = 0 ↔ b = 0
  proof: by
  obtain ⟨u, rfl⟩ := h
  rw [← Units.eq_mul_inv_iff_mul_eq]; rw [zero_mul]

中文:
定理 Associated.eq_zero_iff
  条件: [MonoidWithZero M] {a b : M} (h : a ~ᵤ b)
  结论: a = 0 ↔ b = 0
  证明: by
  obtain ⟨u, rfl⟩ := h
  rw [← Units.eq_mul_inv_iff_mul_eq]; rw [zero_mul]

Depends on / 依赖: Units.eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq, zero_mul
-/
theorem Associated.eq_zero_iff [MonoidWithZero M] {a b : M} (h : a ~ᵤ b) : a = 0 ↔ b = 0 := by
  obtain ⟨u, rfl⟩ := h
  rw [← Units.eq_mul_inv_iff_mul_eq]; rw [zero_mul]

/--
theorem `Associated.ne_zero_iff` / 定理 `Associated.ne_zero_iff`

English:
theorem Associated.ne_zero_iff
  given: [MonoidWithZero M] {a b : M} (h : a ~ᵤ b)
  statement: a != 0 ↔ b != 0
  proof: not_congr h.eq_zero_iff

中文:
定理 Associated.ne_zero_iff
  条件: [MonoidWithZero M] {a b : M} (h : a ~ᵤ b)
  结论: a != 0 ↔ b != 0
  证明: not_congr h.eq_zero_iff

Depends on / 依赖: eq_zero_iff, h.eq_zero_iff, not_congr
-/
theorem Associated.ne_zero_iff [MonoidWithZero M] {a b : M} (h : a ~ᵤ b) : a != 0 ↔ b != 0 :=
  not_congr h.eq_zero_iff

/--
theorem `Associated.prime` / 定理 `Associated.prime`

English:
theorem Associated.prime
  given: [CommMonoidWithZero M] {p q : M} (h : p ~ᵤ q) (hp : Prime p)
  proof: ⟨h.ne_zero_iff.1 hp.ne_zero,
    let ⟨u, hu⟩ := h
    ⟨fun ⟨v, hv⟩ => hp.not_isUnit ⟨v * u⁻¹, by simp [hv, hu.symm]⟩, by
      rw [← hu]
      simp only [Units.isUnit, IsUnit.mul_right_dvd]
      intro a b
      exact hp.dvd_or_dvd⟩⟩

中文:
定理 Associated.prime
  条件: [CommMonoidWithZero M] {p q : M} (h : p ~ᵤ q) (hp : Prime p)
  证明: ⟨h.ne_zero_iff.1 hp.ne_zero,
    let ⟨u, hu⟩ := h
    ⟨fun ⟨v, hv⟩ => hp.not_isUnit ⟨v * u⁻¹, by simp [hv, hu.symm]⟩, by
      rw [← hu]
      simp only [Units.isUnit, IsUnit.mul_right_dvd]
      intro a b
      exact hp.dvd_or_dvd⟩⟩
-/
protected theorem Associated.prime [CommMonoidWithZero M] {p q : M} (h : p ~ᵤ q) (hp : Prime p) :
    Prime q :=
  ⟨h.ne_zero_iff.1 hp.ne_zero,
    let ⟨u, hu⟩ := h
    ⟨fun ⟨v, hv⟩ => hp.not_isUnit ⟨v * u⁻¹, by simp [hv, hu.symm]⟩, by
      rw [← hu]
      simp only [Units.isUnit, IsUnit.mul_right_dvd]
      intro a b
      exact hp.dvd_or_dvd⟩⟩

/--
theorem `prime_mul_iff` / 定理 `prime_mul_iff`

English:
theorem prime_mul_iff
  given: [CommMonoidWithZero M] [IsCancelMulZero M] {x y : M}
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases of_irreducible_mul h.irreducible with hx | hy
    · exact Or.inr ⟨hx, (associated_unit_mul_left y x hx).prime h⟩
    · exact Or.inl ⟨(associated_mul_unit_left x y hy).prime h, hy⟩
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact (associated_mul_unit_left x y hy).

中文:
定理 prime_mul_iff
  条件: [CommMonoidWithZero M] [IsCancelMulZero M] {x y : M}
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases of_irreducible_mul h.irreducible with hx | hy
    · exact Or.inr ⟨hx, (associated_unit_mul_left y x hx).prime h⟩
    · exact Or.inl ⟨(associated_mul_unit_left x y hy).prime h, hy⟩
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact (associated_mul_unit_left x y hy).

Depends on / 依赖: Or.inl, Or.inr, associated_mul_unit_left, associated_unit_mul_left, associated_unit_mul_right, h.irreducible, irreducible, of_irreducible_mul, symm.prime
-/
theorem prime_mul_iff [CommMonoidWithZero M] [IsCancelMulZero M] {x y : M} :
    Prime (x * y) ↔ (Prime x ∧ IsUnit y) ∨ (IsUnit x ∧ Prime y) := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases of_irreducible_mul h.irreducible with hx | hy
    · exact Or.inr ⟨hx, (associated_unit_mul_left y x hx).prime h⟩
    · exact Or.inl ⟨(associated_mul_unit_left x y hy).prime h, hy⟩
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact (associated_mul_unit_left x y hy).symm.prime hx
    · exact (associated_unit_mul_right y x hx).prime hy

@[simp]
/--
lemma `prime_pow_iff` / 引理 `prime_pow_iff`

English:
lemma prime_pow_iff
  given: [CommMonoidWithZero M] [IsCancelMulZero M] {p : M} {n : Nat}
  proof: by
  refine ⟨fun hp => ?_, fun ⟨hp, hn⟩ => by simpa [hn]⟩
  suffices n = 1 by simp_all
  grind [not_prime_pow, Nat.zero_eq_one_mod_iff]

中文:
引理 prime_pow_iff
  条件: [CommMonoidWithZero M] [IsCancelMulZero M] {p : M} {n : 自然数}
  证明: by
  refine ⟨fun hp => ?_, fun ⟨hp, hn⟩ => by simpa [hn]⟩
  suffices n = 1 by simp_all
  grind [not_prime_pow, Nat.zero_eq_one_mod_iff]

Depends on / 依赖: Nat.zero_eq_one_mod_iff, not_prime_pow, zero_eq_one_mod_iff
-/
lemma prime_pow_iff [CommMonoidWithZero M] [IsCancelMulZero M] {p : M} {n : Nat} :
    Prime (p ^ n) ↔ Prime p ∧ n = 1 := by
  refine ⟨fun hp => ?_, fun ⟨hp, hn⟩ => by simpa [hn]⟩
  suffices n = 1 by simp_all
  grind [not_prime_pow, Nat.zero_eq_one_mod_iff]

/--
theorem `Irreducible.dvd_iff` / 定理 `Irreducible.dvd_iff`

English:
theorem Irreducible.dvd_iff
  given: [Monoid M] {x y : M} (hx : Irreducible x)
  proof: by
  constructor
  · rintro ⟨z, hz⟩
    obtain (h | h) := hx.isUnit_or_isUnit hz
    · exact Or.inl h
    · rw [hz]
      exact Or.inr (associated_mul_unit_left _ _ h)
  · rintro (hy | h)
    · exact hy.dvd
    · exact h.symm.dvd

中文:
定理 Irreducible.dvd_iff
  条件: [Monoid M] {x y : M} (hx : Irreducible x)
  证明: by
  constructor
  · rintro ⟨z, hz⟩
    obtain (h | h) := hx.isUnit_or_isUnit hz
    · exact Or.inl h
    · rw [hz]
      exact Or.inr (associated_mul_unit_left _ _ h)
  · rintro (hy | h)
    · exact hy.dvd
    · exact h.symm.dvd

Depends on / 依赖: Or.inl, Or.inr, associated_mul_unit_left, h.symm.dvd, hx.isUnit_or_isUnit, hy.dvd, isUnit_or_isUnit
-/
theorem Irreducible.dvd_iff [Monoid M] {x y : M} (hx : Irreducible x) :
    y ∣ x ↔ IsUnit y ∨ Associated x y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain (h | h) := hx.isUnit_or_isUnit hz
    · exact Or.inl h
    · rw [hz]
      exact Or.inr (associated_mul_unit_left _ _ h)
  · rintro (hy | h)
    · exact hy.dvd
    · exact h.symm.dvd

/--
theorem `Irreducible.associated_of_dvd` / 定理 `Irreducible.associated_of_dvd`

English:
theorem Irreducible.associated_of_dvd
  statement: [Monoid M] {p q : M} (p_irr : Irreducible p)
  proof: ((q_irr.dvd_iff.mp dvd).resolve_left p_irr.not_isUnit).symm

中文:
定理 Irreducible.associated_of_dvd
  结论: [Monoid M] {p q : M} (p_irr : Irreducible p)
  证明: ((q_irr.dvd_iff.mp dvd).resolve_left p_irr.not_isUnit).symm

Depends on / 依赖: dvd_iff, not_isUnit, p_irr, p_irr.not_isUnit, q_irr, q_irr.dvd_iff.mp, resolve_left
-/
theorem Irreducible.associated_of_dvd [Monoid M] {p q : M} (p_irr : Irreducible p)
    (q_irr : Irreducible q) (dvd : p ∣ q) : Associated p q :=
  ((q_irr.dvd_iff.mp dvd).resolve_left p_irr.not_isUnit).symm

/--
theorem `Irreducible.dvd_irreducible_iff_associated` / 定理 `Irreducible.dvd_irreducible_iff_associated`

English:
theorem Irreducible.dvd_irreducible_iff_associated
  statement: [Monoid M] {p q : M}
  proof: ⟨Irreducible.associated_of_dvd pp qp, Associated.dvd⟩

中文:
定理 Irreducible.dvd_irreducible_iff_associated
  结论: [Monoid M] {p q : M}
  证明: ⟨Irreducible.associated_of_dvd pp qp, Associated.dvd⟩

Depends on / 依赖: Associated, Associated.dvd, Irreducible, Irreducible.associated_of_dvd, associated_of_dvd
-/
theorem Irreducible.dvd_irreducible_iff_associated [Monoid M] {p q : M}
    (pp : Irreducible p) (qp : Irreducible q) : p ∣ q ↔ Associated p q :=
  ⟨Irreducible.associated_of_dvd pp qp, Associated.dvd⟩

/--
theorem `Prime.associated_of_dvd` / 定理 `Prime.associated_of_dvd`

English:
theorem Prime.associated_of_dvd
  statement: [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
  proof: p_prime.irreducible.associated_of_dvd q_prime.irreducible dvd

中文:
定理 Prime.associated_of_dvd
  结论: [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
  证明: p_prime.irreducible.associated_of_dvd q_prime.irreducible dvd

Depends on / 依赖: associated_of_dvd, irreducible, p_prime, p_prime.irreducible.associated_of_dvd, q_prime, q_prime.irreducible
-/
theorem Prime.associated_of_dvd [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
    (p_prime : Prime p) (q_prime : Prime q) (dvd : p ∣ q) : Associated p q :=
  p_prime.irreducible.associated_of_dvd q_prime.irreducible dvd

/--
theorem `Prime.dvd_prime_iff_associated` / 定理 `Prime.dvd_prime_iff_associated`

English:
theorem Prime.dvd_prime_iff_associated
  statement: [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
  proof: pp.irreducible.dvd_irreducible_iff_associated qp.irreducible

中文:
定理 Prime.dvd_prime_iff_associated
  结论: [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
  证明: pp.irreducible.dvd_irreducible_iff_associated qp.irreducible

Depends on / 依赖: dvd_irreducible_iff_associated, irreducible, pp.irreducible.dvd_irreducible_iff_associated, qp.irreducible
-/
theorem Prime.dvd_prime_iff_associated [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
    (pp : Prime p) (qp : Prime q) : p ∣ q ↔ Associated p q :=
  pp.irreducible.dvd_irreducible_iff_associated qp.irreducible

/--
theorem `Associated.prime_iff` / 定理 `Associated.prime_iff`

English:
theorem Associated.prime_iff
  given: [CommMonoidWithZero M] {p q : M} (h : p ~ᵤ q)
  statement: Prime p ↔ Prime q
  proof: ⟨h.prime, h.symm.prime⟩

中文:
定理 Associated.prime_iff
  条件: [CommMonoidWithZero M] {p q : M} (h : p ~ᵤ q)
  结论: Prime p ↔ Prime q
  证明: ⟨h.prime, h.symm.prime⟩

Depends on / 依赖: h.prime, h.symm.prime
-/
theorem Associated.prime_iff [CommMonoidWithZero M] {p q : M} (h : p ~ᵤ q) : Prime p ↔ Prime q :=
  ⟨h.prime, h.symm.prime⟩

/--
theorem `Associated.isUnit` / 定理 `Associated.isUnit`

English:
theorem Associated.isUnit
  given: [Monoid M] {a b : M} (h : a ~ᵤ b)
  statement: IsUnit a -> IsUnit b
  proof: let ⟨u, hu⟩ := h
  fun ⟨v, hv⟩ => ⟨v * u, by simp [hv, hu.symm]⟩

中文:
定理 Associated.isUnit
  条件: [Monoid M] {a b : M} (h : a ~ᵤ b)
  结论: IsUnit a -> IsUnit b
  证明: let ⟨u, hu⟩ := h
  fun ⟨v, hv⟩ => ⟨v * u, by simp [hv, hu.symm]⟩
-/
protected theorem Associated.isUnit [Monoid M] {a b : M} (h : a ~ᵤ b) : IsUnit a -> IsUnit b :=
  let ⟨u, hu⟩ := h
  fun ⟨v, hv⟩ => ⟨v * u, by simp [hv, hu.symm]⟩

/--
theorem `Associated.isUnit_iff` / 定理 `Associated.isUnit_iff`

English:
theorem Associated.isUnit_iff
  given: [Monoid M] {a b : M} (h : a ~ᵤ b)
  statement: IsUnit a ↔ IsUnit b
  proof: ⟨h.isUnit, h.symm.isUnit⟩

中文:
定理 Associated.isUnit_iff
  条件: [Monoid M] {a b : M} (h : a ~ᵤ b)
  结论: IsUnit a ↔ IsUnit b
  证明: ⟨h.isUnit, h.symm.isUnit⟩

Depends on / 依赖: h.isUnit, h.symm.isUnit, isUnit
-/
theorem Associated.isUnit_iff [Monoid M] {a b : M} (h : a ~ᵤ b) : IsUnit a ↔ IsUnit b :=
  ⟨h.isUnit, h.symm.isUnit⟩

/--
theorem `Irreducible.isUnit_iff_not_associated_of_dvd` / 定理 `Irreducible.isUnit_iff_not_associated_of_dvd`

English:
theorem Irreducible.isUnit_iff_not_associated_of_dvd
  statement: [Monoid M]
  proof: ⟨fun hy hxy => hx.1 (hxy.symm.isUnit hy), (hx.dvd_iff.mp hy).resolve_right⟩

中文:
定理 Irreducible.isUnit_iff_not_associated_of_dvd
  结论: [Monoid M]
  证明: ⟨fun hy hxy => hx.1 (hxy.symm.isUnit hy), (hx.dvd_iff.mp hy).resolve_right⟩

Depends on / 依赖: dvd_iff, hx.dvd_iff.mp, hxy.symm.isUnit, isUnit, resolve_right
-/
theorem Irreducible.isUnit_iff_not_associated_of_dvd [Monoid M]
    {x y : M} (hx : Irreducible x) (hy : y ∣ x) : IsUnit y ↔ ¬ Associated x y :=
  ⟨fun hy hxy => hx.1 (hxy.symm.isUnit hy), (hx.dvd_iff.mp hy).resolve_right⟩

/--
theorem `Associated.irreducible` / 定理 `Associated.irreducible`

English:
theorem Associated.irreducible
  given: [Monoid M] {p q : M} (h : p ~ᵤ q) (hp : Irreducible p)
  proof: ⟨mt h.symm.isUnit hp.1,
    let ⟨u, hu⟩ := h
    fun a b hab =>
    have hpab : p = a * (b * (u⁻¹ : Mˣ)) :=
      calc
        p = p * u * (u⁻¹ : Mˣ) := by simp
        _ = _ := by rw [hu]; simp [hab, mul_assoc]
    (hp.isUnit_or_isUnit hpab).elim Or.inl fun ⟨v, hv⟩ => Or.inr ⟨v * u, by simp [hv]⟩⟩

中文:
定理 Associated.irreducible
  条件: [Monoid M] {p q : M} (h : p ~ᵤ q) (hp : Irreducible p)
  证明: ⟨mt h.symm.isUnit hp.1,
    let ⟨u, hu⟩ := h
    fun a b hab =>
    have hpab : p = a * (b * (u⁻¹ : Mˣ)) :=
      calc
        p = p * u * (u⁻¹ : Mˣ) := by simp
        _ = _ := by rw [hu]; simp [hab, mul_assoc]
    (hp.isUnit_or_isUnit hpab).elim Or.inl fun ⟨v, hv⟩ => Or.inr ⟨v * u, by simp [hv]⟩⟩
-/
protected theorem Associated.irreducible [Monoid M] {p q : M} (h : p ~ᵤ q) (hp : Irreducible p) :
    Irreducible q :=
  ⟨mt h.symm.isUnit hp.1,
    let ⟨u, hu⟩ := h
    fun a b hab =>
    have hpab : p = a * (b * (u⁻¹ : Mˣ)) :=
      calc
        p = p * u * (u⁻¹ : Mˣ) := by simp
        _ = _ := by rw [hu]; simp [hab, mul_assoc]
    (hp.isUnit_or_isUnit hpab).elim Or.inl fun ⟨v, hv⟩ => Or.inr ⟨v * u, by simp [hv]⟩⟩

/--
theorem `Associated.irreducible_iff` / 定理 `Associated.irreducible_iff`

English:
theorem Associated.irreducible_iff
  given: [Monoid M] {p q : M} (h : p ~ᵤ q)
  proof: ⟨h.irreducible, h.symm.irreducible⟩

中文:
定理 Associated.irreducible_iff
  条件: [Monoid M] {p q : M} (h : p ~ᵤ q)
  证明: ⟨h.irreducible, h.symm.irreducible⟩
-/
protected theorem Associated.irreducible_iff [Monoid M] {p q : M} (h : p ~ᵤ q) :
    Irreducible p ↔ Irreducible q :=
  ⟨h.irreducible, h.symm.irreducible⟩

/--
theorem `Associated.of_mul_left` / 定理 `Associated.of_mul_left`

English:
theorem Associated.of_mul_left
  statement: [CommMonoidWithZero M] [IsCancelMulZero M] {a b c d : M}
  proof: let ⟨u, hu⟩ := h
  let ⟨v, hv⟩ := Associated.symm h₁
  ⟨u * (v : Mˣ),
    mul_left_cancel₀ ha
      (by
        rw [← hv]; rw [mul_assoc c (v : M) d]; rw [mul_left_comm c]; rw [← hu]
        simp [hv.symm, mul_comm, mul_left_comm])⟩

中文:
定理 Associated.of_mul_left
  结论: [CommMonoidWithZero M] [IsCancelMulZero M] {a b c d : M}
  证明: let ⟨u, hu⟩ := h
  let ⟨v, hv⟩ := Associated.symm h₁
  ⟨u * (v : Mˣ),
    mul_left_cancel₀ ha
      (by
        rw [← hv]; rw [mul_assoc c (v : M) d]; rw [mul_left_comm c]; rw [← hu]
        simp [hv.symm, mul_comm, mul_left_comm])⟩

Depends on / 依赖: Associated, Associated.symm, hv.symm, mul_assoc, mul_comm, mul_left_comm
-/
theorem Associated.of_mul_left [CommMonoidWithZero M] [IsCancelMulZero M] {a b c d : M}
    (h : a * b ~ᵤ c * d) (h₁ : a ~ᵤ c) (ha : a != 0) : b ~ᵤ d :=
  let ⟨u, hu⟩ := h
  let ⟨v, hv⟩ := Associated.symm h₁
  ⟨u * (v : Mˣ),
    mul_left_cancel₀ ha
      (by
        rw [← hv]; rw [mul_assoc c (v : M) d]; rw [mul_left_comm c]; rw [← hu]
        simp [hv.symm, mul_comm, mul_left_comm])⟩

/--
theorem `Associated.of_mul_right` / 定理 `Associated.of_mul_right`

English:
theorem Associated.of_mul_right
  given: [CommMonoidWithZero M] [IsCancelMulZero M] {a b c d : M}
  proof: by
  rw [mul_comm a]; rw [mul_comm c]; exact Associated.of_mul_left

中文:
定理 Associated.of_mul_right
  条件: [CommMonoidWithZero M] [IsCancelMulZero M] {a b c d : M}
  证明: by
  rw [mul_comm a]; rw [mul_comm c]; exact Associated.of_mul_left

Depends on / 依赖: Associated, Associated.of_mul_left, mul_comm, of_mul_left
-/
theorem Associated.of_mul_right [CommMonoidWithZero M] [IsCancelMulZero M] {a b c d : M} :
    a * b ~ᵤ c * d -> b ~ᵤ d -> b != 0 -> a ~ᵤ c := by
  rw [mul_comm a]; rw [mul_comm c]; exact Associated.of_mul_left

/--
theorem `Associated.of_pow_associated_of_prime` / 定理 `Associated.of_pow_associated_of_prime`

English:
theorem Associated.of_pow_associated_of_prime
  statement: [CommMonoidWithZero M] [IsCancelMulZero M]
  proof: by
  have : p₁ ∣ p₂ ^ k₂ := by
    rw [← h.dvd_iff_dvd_right]
    apply dvd_pow_self _ hk₁.ne'
  rw [← hp₁.dvd_prime_iff_associated hp₂]
  exact hp₁.dvd_of_dvd_pow this

中文:
定理 Associated.of_pow_associated_of_prime
  结论: [CommMonoidWithZero M] [IsCancelMulZero M]
  证明: by
  have : p₁ ∣ p₂ ^ k₂ := by
    rw [← h.dvd_iff_dvd_right]
    apply dvd_pow_self _ hk₁.ne'
  rw [← hp₁.dvd_prime_iff_associated hp₂]
  exact hp₁.dvd_of_dvd_pow this

Depends on / 依赖: dvd_iff_dvd_right, dvd_of_dvd_pow, dvd_pow_self, dvd_prime_iff_associated, h.dvd_iff_dvd_right
-/
theorem Associated.of_pow_associated_of_prime [CommMonoidWithZero M] [IsCancelMulZero M]
    {p₁ p₂ : M} {k₁ k₂ : Nat}
    (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₁) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) : p₁ ~ᵤ p₂ := by
  have : p₁ ∣ p₂ ^ k₂ := by
    rw [← h.dvd_iff_dvd_right]
    apply dvd_pow_self _ hk₁.ne'
  rw [← hp₁.dvd_prime_iff_associated hp₂]
  exact hp₁.dvd_of_dvd_pow this

/--
theorem `Associated.of_pow_associated_of_prime'` / 定理 `Associated.of_pow_associated_of_prime'`

English:
theorem Associated.of_pow_associated_of_prime'
  statement: [CommMonoidWithZero M] [IsCancelMulZero M]
  proof: (h.symm.of_pow_associated_of_prime hp₂ hp₁ hk₂).symm

中文:
定理 Associated.of_pow_associated_of_prime'
  结论: [CommMonoidWithZero M] [IsCancelMulZero M]
  证明: (h.symm.of_pow_associated_of_prime hp₂ hp₁ hk₂).symm

Depends on / 依赖: h.symm.of_pow_associated_of_prime, of_pow_associated_of_prime
-/
theorem Associated.of_pow_associated_of_prime' [CommMonoidWithZero M] [IsCancelMulZero M]
    {p₁ p₂ : M} {k₁ k₂ : Nat}
    (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₂ : 0 < k₂) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) : p₁ ~ᵤ p₂ :=
  (h.symm.of_pow_associated_of_prime hp₂ hp₁ hk₂).symm

/--
lemma `Irreducible.isRelPrime_iff_not_dvd` / 引理 `Irreducible.isRelPrime_iff_not_dvd`

English:
lemma Irreducible.isRelPrime_iff_not_dvd
  given: [Monoid M] {p n : M} (hp : Irreducible p)
  proof: by
  refine ⟨fun h contra => hp.not_isUnit (h dvd_rfl contra), fun hpn d hdp hdn => ?_⟩
  contrapose hpn
  suffices Associated p d from this.dvd.trans hdn
  exact (hp.dvd_iff.mp hdp).resolve_left hpn

中文:
引理 Irreducible.isRelPrime_iff_not_dvd
  条件: [Monoid M] {p n : M} (hp : Irreducible p)
  证明: by
  refine ⟨fun h contra => hp.not_isUnit (h dvd_rfl contra), fun hpn d hdp hdn => ?_⟩
  contrapose hpn
  suffices Associated p d from this.dvd.trans hdn
  exact (hp.dvd_iff.mp hdp).resolve_left hpn

Depends on / 依赖: Associated, contra, contrapose, dvd_iff, dvd_rfl, hp.dvd_iff.mp, hp.not_isUnit, not_isUnit, resolve_left, this.dvd.trans
-/
lemma Irreducible.isRelPrime_iff_not_dvd [Monoid M] {p n : M} (hp : Irreducible p) :
    IsRelPrime p n ↔ ¬ p ∣ n := by
  refine ⟨fun h contra => hp.not_isUnit (h dvd_rfl contra), fun hpn d hdp hdn => ?_⟩
  contrapose hpn
  suffices Associated p d from this.dvd.trans hdn
  exact (hp.dvd_iff.mp hdp).resolve_left hpn

/--
lemma `Irreducible.dvd_or_isRelPrime` / 引理 `Irreducible.dvd_or_isRelPrime`

English:
lemma Irreducible.dvd_or_isRelPrime
  given: [Monoid M] {p n : M} (hp : Irreducible p)
  proof: Classical.or_iff_not_imp_left.mpr hp.isRelPrime_iff_not_dvd.2

中文:
引理 Irreducible.dvd_or_isRelPrime
  条件: [Monoid M] {p n : M} (hp : Irreducible p)
  证明: Classical.or_iff_not_imp_left.mpr hp.isRelPrime_iff_not_dvd.2

Depends on / 依赖: Classical, Classical.or_iff_not_imp_left.mpr, hp.isRelPrime_iff_not_dvd, isRelPrime_iff_not_dvd, or_iff_not_imp_left
-/
lemma Irreducible.dvd_or_isRelPrime [Monoid M] {p n : M} (hp : Irreducible p) :
    p ∣ n ∨ IsRelPrime p n := Classical.or_iff_not_imp_left.mpr hp.isRelPrime_iff_not_dvd.2

section UniqueUnits

variable [Monoid M] [Subsingleton Mˣ]

/--
theorem `associated_iff_eq` / 定理 `associated_iff_eq`

English:
theorem associated_iff_eq
  given: {x y : M}
  statement: x ~ᵤ y ↔ x = y
  proof: by
  simp [Associated, Units.eq_one]

中文:
定理 associated_iff_eq
  条件: {x y : M}
  结论: x ~ᵤ y ↔ x = y
  证明: by
  simp [Associated, Units.eq_one]

Depends on / 依赖: Associated, Units.eq_one, eq_one
-/
theorem associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y := by
  simp [Associated, Units.eq_one]

/--
theorem `associated_eq_eq` / 定理 `associated_eq_eq`

English:
theorem associated_eq_eq
  statement: (Associated : M -> M -> Prop) = Eq
  proof: by
  ext
  rw [associated_iff_eq]

中文:
定理 associated_eq_eq
  结论: (Associated : M -> M -> 命题) = Eq
  证明: by
  ext
  rw [associated_iff_eq]

Depends on / 依赖: associated_iff_eq
-/
theorem associated_eq_eq : (Associated : M -> M -> Prop) = Eq := by
  ext
  rw [associated_iff_eq]

/--
theorem `prime_dvd_prime_iff_eq` / 定理 `prime_dvd_prime_iff_eq`

English:
theorem prime_dvd_prime_iff_eq
  statement: {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]
  proof: by
  rw [pp.dvd_prime_iff_associated qp]; rw [← associated_eq_eq]

中文:
定理 prime_dvd_prime_iff_eq
  结论: {M : 类型} [CommMonoidWithZero M] [IsCancelMulZero M]
  证明: by
  rw [pp.dvd_prime_iff_associated qp]; rw [← associated_eq_eq]

Depends on / 依赖: associated_eq_eq, dvd_prime_iff_associated, pp.dvd_prime_iff_associated
-/
theorem prime_dvd_prime_iff_eq {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]
    [Subsingleton Mˣ] {p q : M} (pp : Prime p) (qp : Prime q) : p ∣ q ↔ p = q := by
  rw [pp.dvd_prime_iff_associated qp]; rw [← associated_eq_eq]

end UniqueUnits

section UniqueUnits₀

variable {R : Type*} [CommMonoidWithZero R] [IsCancelMulZero R] [Subsingleton Rˣ]
variable {p₁ p₂ : R} {k₁ k₂ : Nat}

/--
theorem `eq_of_prime_pow_eq` / 定理 `eq_of_prime_pow_eq`

English:
theorem eq_of_prime_pow_eq
  statement: (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₁)
  proof: by
  rw [← associated_iff_eq] at h ⊢
  apply h.of_pow_associated_of_prime hp₁ hp₂ hk₁

中文:
定理 eq_of_prime_pow_eq
  结论: (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₁)
  证明: by
  rw [← associated_iff_eq] at h ⊢
  apply h.of_pow_associated_of_prime hp₁ hp₂ hk₁

Depends on / 依赖: associated_iff_eq, h.of_pow_associated_of_prime, of_pow_associated_of_prime
-/
theorem eq_of_prime_pow_eq (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₁)
    (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂ := by
  rw [← associated_iff_eq] at h ⊢
  apply h.of_pow_associated_of_prime hp₁ hp₂ hk₁

/--
theorem `eq_of_prime_pow_eq'` / 定理 `eq_of_prime_pow_eq'`

English:
theorem eq_of_prime_pow_eq'
  statement: (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₂)
  proof: by
  rw [← associated_iff_eq] at h ⊢
  apply h.of_pow_associated_of_prime' hp₁ hp₂ hk₁

中文:
定理 eq_of_prime_pow_eq'
  结论: (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₂)
  证明: by
  rw [← associated_iff_eq] at h ⊢
  apply h.of_pow_associated_of_prime' hp₁ hp₂ hk₁

Depends on / 依赖: associated_iff_eq, h.of_pow_associated_of_prime, of_pow_associated_of_prime
-/
theorem eq_of_prime_pow_eq' (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₂)
    (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂ := by
  rw [← associated_iff_eq] at h ⊢
  apply h.of_pow_associated_of_prime' hp₁ hp₂ hk₁

end UniqueUnits₀

/--
Definition of `Associates` / `Associates` 的定义

English:
abbreviation Associates
  signature: (M : Type*) [Monoid M]
  body: Quotient (Associated.setoid M)

中文:
缩写 Associates
  签名: (M : 类型) [Monoid M]
  定义体: Quotient (Associated.setoid M)

Depends on / 依赖: Associated, Associated.setoid, Quotient, setoid
-/
abbrev Associates (M : Type*) [Monoid M] : Type _ :=
  Quotient (Associated.setoid M)

namespace Associates

open Associated

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: {M : Type*} [Monoid M] (a : M)
  body: ⟦a⟧

中文:
缩写 mk
  签名: {M : 类型} [Monoid M] (a : M)
  定义体: ⟦a⟧
-/
protected abbrev mk {M : Type*} [Monoid M] (a : M) : Associates M :=
  ⟦a⟧

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] : Inhabited (Associates M)
  body: ⟨⟦1⟧⟩

中文:
实例 [Monoid
  签名: M] : Inhabited (Associates M)
  定义体: ⟨⟦1⟧⟩
-/
instance [Monoid M] : Inhabited (Associates M) :=
  ⟨⟦1⟧⟩

/--
theorem `mk_eq_mk_iff_associated` / 定理 `mk_eq_mk_iff_associated`

English:
theorem mk_eq_mk_iff_associated
  given: [Monoid M] {a b : M}
  statement: Associates.mk a = Associates.mk b ↔ a ~ᵤ b
  proof: Iff.intro Quotient.exact Quot.sound

中文:
定理 mk_eq_mk_iff_associated
  条件: [Monoid M] {a b : M}
  结论: Associates.mk a = Associates.mk b ↔ a ~ᵤ b
  证明: Iff.intro Quotient.exact Quot.sound

Depends on / 依赖: Iff.intro, Quot.sound, Quotient, Quotient.exact
-/
theorem mk_eq_mk_iff_associated [Monoid M] {a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b :=
  Iff.intro Quotient.exact Quot.sound

/--
theorem `quotient_mk_eq_mk` / 定理 `quotient_mk_eq_mk`

English:
theorem quotient_mk_eq_mk
  given: [Monoid M] (a : M)
  statement: ⟦a⟧ = Associates.mk a
  proof: rfl

中文:
定理 quotient_mk_eq_mk
  条件: [Monoid M] (a : M)
  结论: ⟦a⟧ = Associates.mk a
  证明: rfl
-/
theorem quotient_mk_eq_mk [Monoid M] (a : M) : ⟦a⟧ = Associates.mk a :=
  rfl

/--
theorem `quot_mk_eq_mk` / 定理 `quot_mk_eq_mk`

English:
theorem quot_mk_eq_mk
  given: [Monoid M] (a : M)
  statement: Quot.mk Setoid.r a = Associates.mk a
  proof: rfl

中文:
定理 quot_mk_eq_mk
  条件: [Monoid M] (a : M)
  结论: Quot.mk Setoid.r a = Associates.mk a
  证明: rfl
-/
theorem quot_mk_eq_mk [Monoid M] (a : M) : Quot.mk Setoid.r a = Associates.mk a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `quot_out` / 定理 `quot_out`

English:
theorem quot_out
  given: [Monoid M] (a : Associates M)
  statement: Associates.mk (Quot.out a) = a
  proof: by
  rw [← quot_mk_eq_mk]; rw [Quot.out_eq]

中文:
定理 quot_out
  条件: [Monoid M] (a : Associates M)
  结论: Associates.mk (Quot.out a) = a
  证明: by
  rw [← quot_mk_eq_mk]; rw [Quot.out_eq]

Depends on / 依赖: Quot.out_eq, out_eq, quot_mk_eq_mk
-/
theorem quot_out [Monoid M] (a : Associates M) : Associates.mk (Quot.out a) = a := by
  rw [← quot_mk_eq_mk]; rw [Quot.out_eq]

/--
theorem `mk_quot_out` / 定理 `mk_quot_out`

English:
theorem mk_quot_out
  given: [Monoid M] (a : M)
  statement: Quot.out (Associates.mk a) ~ᵤ a
  proof: by
  rw [← Associates.mk_eq_mk_iff_associated]; rw [Associates.quot_out]

中文:
定理 mk_quot_out
  条件: [Monoid M] (a : M)
  结论: Quot.out (Associates.mk a) ~ᵤ a
  证明: by
  rw [← Associates.mk_eq_mk_iff_associated]; rw [Associates.quot_out]

Depends on / 依赖: Associates, Associates.mk_eq_mk_iff_associated, Associates.quot_out, mk_eq_mk_iff_associated, quot_out
-/
theorem mk_quot_out [Monoid M] (a : M) : Quot.out (Associates.mk a) ~ᵤ a := by
  rw [← Associates.mk_eq_mk_iff_associated]; rw [Associates.quot_out]

/--
theorem `forall_associated` / 定理 `forall_associated`

English:
theorem forall_associated
  given: [Monoid M] {p : Associates M -> Prop}
  proof: Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

中文:
定理 forall_associated
  条件: [Monoid M] {p : Associates M -> 命题}
  证明: Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

Depends on / 依赖: Iff.intro, Quotient, Quotient.inductionOn, inductionOn
-/
theorem forall_associated [Monoid M] {p : Associates M -> Prop} :
    (forall a, p a) ↔ forall a, p (Associates.mk a) :=
  Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  given: [Monoid M]
  statement: Function.Surjective (@Associates.mk M _)
  proof: forall_associated.2 fun a => ⟨a, rfl⟩

中文:
定理 mk_surjective
  条件: [Monoid M]
  结论: Function.Surjective (@Associates.mk M _)
  证明: forall_associated.2 fun a => ⟨a, rfl⟩

Depends on / 依赖: forall_associated
-/
theorem mk_surjective [Monoid M] : Function.Surjective (@Associates.mk M _) :=
  forall_associated.2 fun a => ⟨a, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] : One (Associates M)
  body: ⟨⟦1⟧⟩

@[simp]

中文:
实例 [Monoid
  签名: M] : One (Associates M)
  定义体: ⟨⟦1⟧⟩

@[simp]
-/
instance [Monoid M] : One (Associates M) :=
  ⟨⟦1⟧⟩

@[simp]
/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  given: [Monoid M]
  statement: Associates.mk (1 : M) = 1
  proof: rfl

中文:
定理 mk_one
  条件: [Monoid M]
  结论: Associates.mk (1 : M) = 1
  证明: rfl
-/
theorem mk_one [Monoid M] : Associates.mk (1 : M) = 1 :=
  rfl

/--
theorem `one_eq_mk_one` / 定理 `one_eq_mk_one`

English:
theorem one_eq_mk_one
  given: [Monoid M]
  statement: (1 : Associates M) = Associates.mk 1
  proof: rfl

@[simp]

中文:
定理 one_eq_mk_one
  条件: [Monoid M]
  结论: (1 : Associates M) = Associates.mk 1
  证明: rfl

@[simp]
-/
theorem one_eq_mk_one [Monoid M] : (1 : Associates M) = Associates.mk 1 :=
  rfl

@[simp]
/--
theorem `mk_eq_one` / 定理 `mk_eq_one`

English:
theorem mk_eq_one
  given: [Monoid M] {a : M}
  statement: Associates.mk a = 1 ↔ IsUnit a
  proof: by
  rw [← mk_one]; rw [mk_eq_mk_iff_associated]; rw [associated_one_iff_isUnit]

中文:
定理 mk_eq_one
  条件: [Monoid M] {a : M}
  结论: Associates.mk a = 1 ↔ IsUnit a
  证明: by
  rw [← mk_one]; rw [mk_eq_mk_iff_associated]; rw [associated_one_iff_isUnit]

Depends on / 依赖: associated_one_iff_isUnit, mk_eq_mk_iff_associated, mk_one
-/
theorem mk_eq_one [Monoid M] {a : M} : Associates.mk a = 1 ↔ IsUnit a := by
  rw [← mk_one]; rw [mk_eq_mk_iff_associated]; rw [associated_one_iff_isUnit]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] : Bot (Associates M)
  body: ⟨1⟩

中文:
实例 [Monoid
  签名: M] : Bot (Associates M)
  定义体: ⟨1⟩
-/
instance [Monoid M] : Bot (Associates M) :=
  ⟨1⟩

/--
theorem `bot_eq_one` / 定理 `bot_eq_one`

English:
theorem bot_eq_one
  given: [Monoid M]
  statement: (⊥ : Associates M) = 1
  proof: rfl

中文:
定理 bot_eq_one
  条件: [Monoid M]
  结论: (⊥ : Associates M) = 1
  证明: rfl
-/
theorem bot_eq_one [Monoid M] : (⊥ : Associates M) = 1 :=
  rfl

/--
theorem `exists_rep` / 定理 `exists_rep`

English:
theorem exists_rep
  given: [Monoid M] (a : Associates M)
  statement: exists a0 : M, Associates.mk a0 = a
  proof: Quot.exists_rep a

中文:
定理 exists_rep
  条件: [Monoid M] (a : Associates M)
  结论: 存在 a0 : M, Associates.mk a0 = a
  证明: Quot.exists_rep a

Depends on / 依赖: Quot.exists_rep, exists_rep
-/
theorem exists_rep [Monoid M] (a : Associates M) : exists a0 : M, Associates.mk a0 = a :=
  Quot.exists_rep a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [Subsingleton M] :
  body: 1
uniq := forall_associated.2 fun _ => mk_eq_one.2 isUnit_of_subsingleton _

中文:
实例 [Monoid
  签名: M] [Subsingleton M] :
  定义体: 1
uniq := forall_associated.2 fun _ => mk_eq_one.2 isUnit_of_subsingleton _
-/
instance [Monoid M] [Subsingleton M] :
    Unique (Associates M) where
  default := 1
uniq := forall_associated.2 fun _ => mk_eq_one.2 isUnit_of_subsingleton _

/--
theorem `mk_injective` / 定理 `mk_injective`

English:
theorem mk_injective
  given: [Monoid M] [Subsingleton Mˣ]
  statement: Function.Injective (@Associates.mk M _)
  proof: fun _ _ h => associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)

中文:
定理 mk_injective
  条件: [Monoid M] [Subsingleton Mˣ]
  结论: Function.Injective (@Associates.mk M _)
  证明: fun _ _ h => associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)

Depends on / 依赖: Associates, Associates.mk_eq_mk_iff_associated.mp, associated_iff_eq, associated_iff_eq.mp, mk_eq_mk_iff_associated
-/
theorem mk_injective [Monoid M] [Subsingleton Mˣ] : Function.Injective (@Associates.mk M _) :=
  fun _ _ h => associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)

section CommMonoid

variable [CommMonoid M]

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (Associates M)
  body: ⟨Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => h₁.mul_mul h₂⟩

中文:
实例 instMul
  签名: : Mul (Associates M)
  定义体: ⟨Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => h₁.mul_mul h₂⟩

Depends on / 依赖: Quotient, Quotient.map, mul_mul
-/
instance instMul : Mul (Associates M) :=
  ⟨Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => h₁.mul_mul h₂⟩

/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: {x y : M}
  statement: Associates.mk x * Associates.mk y = Associates.mk (x * y)
  proof: rfl

中文:
定理 mk_mul_mk
  条件: {x y : M}
  结论: Associates.mk x * Associates.mk y = Associates.mk (x * y)
  证明: rfl
-/
theorem mk_mul_mk {x y : M} : Associates.mk x * Associates.mk y = Associates.mk (x * y) :=
  rfl

/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: : CommMonoid (Associates M) where
  body: Quotient.inductionOn a' fun a => show ⟦a * 1⟧ = ⟦a⟧ by simp
  one_mul a' := Quotient.inductionOn a' fun a => show ⟦1 * a⟧ = ⟦a⟧ by simp
  mul_assoc a' b' c' :=
    Quotient.inductionOn₃ a' b' c' fun a b c =>
      show ⟦a * b * c⟧ = ⟦a * (b * c)⟧ by rw [mul_assoc]
  mul_comm a' b' :=
    Quotient.in

中文:
实例 instCommMonoid
  签名: : CommMonoid (Associates M) where
  定义体: Quotient.inductionOn a' fun a => show ⟦a * 1⟧ = ⟦a⟧ by simp
  one_mul a' := Quotient.inductionOn a' fun a => show ⟦1 * a⟧ = ⟦a⟧ by simp
  mul_assoc a' b' c' :=
    Quotient.inductionOn₃ a' b' c' fun a b c =>
      show ⟦a * b * c⟧ = ⟦a * (b * c)⟧ by rw [mul_assoc]
  mul_comm a' b' :=
    Quotient.in

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
instance instCommMonoid : CommMonoid (Associates M) where
  mul_one a' := Quotient.inductionOn a' fun a => show ⟦a * 1⟧ = ⟦a⟧ by simp
  one_mul a' := Quotient.inductionOn a' fun a => show ⟦1 * a⟧ = ⟦a⟧ by simp
  mul_assoc a' b' c' :=
    Quotient.inductionOn₃ a' b' c' fun a b c =>
      show ⟦a * b * c⟧ = ⟦a * (b * c)⟧ by rw [mul_assoc]
  mul_comm a' b' :=
    Quotient.inductionOn₂ a' b' fun a b => show ⟦a * b⟧ = ⟦b * a⟧ by rw [mul_comm]

/--
Instance `instPreorder` / 实例 `instPreorder`

English:
instance instPreorder
  signature: : Preorder (Associates M) where
  body: Dvd.dvd
  le_refl := dvd_refl
  le_trans _ _ _ := dvd_trans

中文:
实例 instPreorder
  签名: : Preorder (Associates M) where
  定义体: Dvd.dvd
  le_refl := dvd_refl
  le_trans _ _ _ := dvd_trans

Depends on / 依赖: Dvd.dvd
-/
instance instPreorder : Preorder (Associates M) where
  le := Dvd.dvd
  le_refl := dvd_refl
  le_trans _ _ _ := dvd_trans

/--
Definition of `mkMonoidHom` / `mkMonoidHom` 的定义

English:
definition mkMonoidHom
  signature: : M ->* Associates M where
  body: Associates.mk
  map_one' := mk_one
  map_mul' _ _ := mk_mul_mk

@[simp]

中文:
定义 mkMonoidHom
  签名: : M ->* Associates M where
  定义体: Associates.mk
  map_one' := mk_one
  map_mul' _ _ := mk_mul_mk

@[simp]
-/
protected def mkMonoidHom : M ->* Associates M where
  toFun := Associates.mk
  map_one' := mk_one
  map_mul' _ _ := mk_mul_mk

@[simp]
/--
theorem `mkMonoidHom_apply` / 定理 `mkMonoidHom_apply`

English:
theorem mkMonoidHom_apply
  given: (a : M)
  statement: Associates.mkMonoidHom a = Associates.mk a
  proof: rfl

中文:
定理 mkMonoidHom_apply
  条件: (a : M)
  结论: Associates.mkMonoidHom a = Associates.mk a
  证明: rfl

Depends on / 依赖: add_assoc
-/
theorem mkMonoidHom_apply (a : M) : Associates.mkMonoidHom a = Associates.mk a :=
  rfl

/--
theorem `associated_map_mk` / 定理 `associated_map_mk`

English:
theorem associated_map_mk
  statement: {f : Associates M ->* M} (hinv : Function.RightInverse f Associates.mk)
  proof: Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm

中文:
定理 associated_map_mk
  结论: {f : Associates M ->* M} (hinv : Function.RightInverse f Associates.mk)
  证明: Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm

Depends on / 依赖: Associates, Associates.mk, Associates.mk_eq_mk_iff_associated, mk_eq_mk_iff_associated
-/
theorem associated_map_mk {f : Associates M ->* M} (hinv : Function.RightInverse f Associates.mk)
    (a : M) : a ~ᵤ f (Associates.mk a) :=
  Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm

/--
theorem `mk_pow` / 定理 `mk_pow`

English:
theorem mk_pow
  given: (a : M) (n : Nat)
  statement: Associates.mk (a ^ n) = Associates.mk a ^ n
  proof: by
  induction n <;> simp [*, pow_succ, Associates.mk_mul_mk.symm]

中文:
定理 mk_pow
  条件: (a : M) (n : 自然数)
  结论: Associates.mk (a ^ n) = Associates.mk a ^ n
  证明: by
  induction n <;> simp [*, pow_succ, Associates.mk_mul_mk.symm]

Depends on / 依赖: Associates, Associates.mk_mul_mk.symm, mk_mul_mk, pow_succ
-/
theorem mk_pow (a : M) (n : Nat) : Associates.mk (a ^ n) = Associates.mk a ^ n := by
  induction n <;> simp [*, pow_succ, Associates.mk_mul_mk.symm]

/--
theorem `dvd_eq_le` / 定理 `dvd_eq_le`

English:
theorem dvd_eq_le
  statement: ((· ∣ ·) : Associates M -> Associates M -> Prop) = (· <= ·)
  proof: rfl

中文:
定理 dvd_eq_le
  结论: ((· ∣ ·) : Associates M -> Associates M -> 命题) = (· <= ·)
  证明: rfl
-/
theorem dvd_eq_le : ((· ∣ ·) : Associates M -> Associates M -> Prop) = (· <= ·) :=
  rfl

/--
Instance `uniqueUnits` / 实例 `uniqueUnits`

English:
instance uniqueUnits
  signature: : Unique (Associates M)ˣ where
  body: by
    rintro ⟨a, b, hab, hba⟩
    induction a, b using Quotient.inductionOn₂ with | _ a b
exact Units.ext Quotient.sound associated_one_of_associated_mul_one Quotient.exact hab

@[simp]

中文:
实例 uniqueUnits
  签名: : Unique (Associates M)ˣ where
  定义体: by
    rintro ⟨a, b, hab, hba⟩
    induction a, b using Quotient.inductionOn₂ with | _ a b
exact Units.ext Quotient.sound associated_one_of_associated_mul_one Quotient.exact hab

@[simp]

Depends on / 依赖: Quotient, Quotient.exact, Quotient.inductionOn, Quotient.sound, Units.ext, associated_one_of_associated_mul_one
-/
instance uniqueUnits : Unique (Associates M)ˣ where
  uniq := by
    rintro ⟨a, b, hab, hba⟩
    induction a, b using Quotient.inductionOn₂ with | _ a b
exact Units.ext Quotient.sound associated_one_of_associated_mul_one Quotient.exact hab

@[simp]
/--
theorem `coe_unit_eq_one` / 定理 `coe_unit_eq_one`

English:
theorem coe_unit_eq_one
  given: (u : (Associates M)ˣ)
  statement: (u : Associates M) = 1
  proof: by
  simp [eq_iff_true_of_subsingleton]

中文:
定理 coe_unit_eq_one
  条件: (u : (Associates M)ˣ)
  结论: (u : Associates M) = 1
  证明: by
  simp [eq_iff_true_of_subsingleton]

Depends on / 依赖: eq_iff_true_of_subsingleton
-/
theorem coe_unit_eq_one (u : (Associates M)ˣ) : (u : Associates M) = 1 := by
  simp [eq_iff_true_of_subsingleton]

/--
theorem `isUnit_iff_eq_one` / 定理 `isUnit_iff_eq_one`

English:
theorem isUnit_iff_eq_one
  given: (a : Associates M)
  statement: IsUnit a ↔ a = 1
  proof: Iff.intro (fun ⟨_, h⟩ => h ▸ coe_unit_eq_one _) fun h => h.symm ▸ isUnit_one

中文:
定理 isUnit_iff_eq_one
  条件: (a : Associates M)
  结论: IsUnit a ↔ a = 1
  证明: Iff.intro (fun ⟨_, h⟩ => h ▸ coe_unit_eq_one _) fun h => h.symm ▸ isUnit_one

Depends on / 依赖: Iff.intro, coe_unit_eq_one, h.symm, isUnit_one
-/
theorem isUnit_iff_eq_one (a : Associates M) : IsUnit a ↔ a = 1 :=
  Iff.intro (fun ⟨_, h⟩ => h ▸ coe_unit_eq_one _) fun h => h.symm ▸ isUnit_one

/--
theorem `isUnit_iff_eq_bot` / 定理 `isUnit_iff_eq_bot`

English:
theorem isUnit_iff_eq_bot
  given: {a : Associates M}
  statement: IsUnit a ↔ a = ⊥
  proof: by
  rw [Associates.isUnit_iff_eq_one]; rw [bot_eq_one]

中文:
定理 isUnit_iff_eq_bot
  条件: {a : Associates M}
  结论: IsUnit a ↔ a = ⊥
  证明: by
  rw [Associates.isUnit_iff_eq_one]; rw [bot_eq_one]

Depends on / 依赖: Associates, Associates.isUnit_iff_eq_one, bot_eq_one, isUnit_iff_eq_one
-/
theorem isUnit_iff_eq_bot {a : Associates M} : IsUnit a ↔ a = ⊥ := by
  rw [Associates.isUnit_iff_eq_one]; rw [bot_eq_one]

/--
theorem `isUnit_mk` / 定理 `isUnit_mk`

English:
theorem isUnit_mk
  given: {a : M}
  statement: IsUnit (Associates.mk a) ↔ IsUnit a
  proof: calc
    IsUnit (Associates.mk a) ↔ a ~ᵤ 1 := by
      rw [isUnit_iff_eq_one]; rw [one_eq_mk_one]; rw [mk_eq_mk_iff_associated]
    _ ↔ IsUnit a := associated_one_iff_isUnit

中文:
定理 isUnit_mk
  条件: {a : M}
  结论: IsUnit (Associates.mk a) ↔ IsUnit a
  证明: calc
    IsUnit (Associates.mk a) ↔ a ~ᵤ 1 := by
      rw [isUnit_iff_eq_one]; rw [one_eq_mk_one]; rw [mk_eq_mk_iff_associated]
    _ ↔ IsUnit a := associated_one_iff_isUnit

Depends on / 依赖: Associates, Associates.mk, IsUnit, associated_one_iff_isUnit, isUnit_iff_eq_one, mk_eq_mk_iff_associated, one_eq_mk_one
-/
theorem isUnit_mk {a : M} : IsUnit (Associates.mk a) ↔ IsUnit a :=
  calc
    IsUnit (Associates.mk a) ↔ a ~ᵤ 1 := by
      rw [isUnit_iff_eq_one]; rw [one_eq_mk_one]; rw [mk_eq_mk_iff_associated]
    _ ↔ IsUnit a := associated_one_iff_isUnit

section Order

/--
theorem `mul_mono` / 定理 `mul_mono`

English:
theorem mul_mono
  given: {a b c d : Associates M} (h₁ : a <= b) (h₂ : c <= d)
  statement: a * c <= b * d
  proof: let ⟨x, hx⟩ := h₁
  let ⟨y, hy⟩ := h₂
  ⟨x * y, by simp [hx, hy, mul_comm, mul_left_comm]⟩

中文:
定理 mul_mono
  条件: {a b c d : Associates M} (h₁ : a <= b) (h₂ : c <= d)
  结论: a * c <= b * d
  证明: let ⟨x, hx⟩ := h₁
  let ⟨y, hy⟩ := h₂
  ⟨x * y, by simp [hx, hy, mul_comm, mul_left_comm]⟩

Depends on / 依赖: mul_comm, mul_left_comm
-/
theorem mul_mono {a b c d : Associates M} (h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d :=
  let ⟨x, hx⟩ := h₁
  let ⟨y, hy⟩ := h₂
  ⟨x * y, by simp [hx, hy, mul_comm, mul_left_comm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsBotOneClass (Associates M)
  body: Dvd.intro _ (one_mul a)

中文:
实例 :
  签名: IsBotOneClass (Associates M)
  定义体: Dvd.intro _ (one_mul a)

Depends on / 依赖: Dvd.intro, one_mul
-/
instance : IsBotOneClass (Associates M) where
  isBot_one a := Dvd.intro _ (one_mul a)

/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: : OrderBot (Associates M) where
  body: one_le

@[deprecated _root_.one_le (since := "2026-05-07")]

中文:
实例 instOrderBot
  签名: : OrderBot (Associates M) where
  定义体: one_le

@[deprecated _root_.one_le (since := "2026-05-07")]

Depends on / 依赖: one_le
-/
instance instOrderBot : OrderBot (Associates M) where
  bot_le _ := one_le

@[deprecated _root_.one_le (since := "2026-05-07")]
/--
theorem `one_le` / 定理 `one_le`

English:
theorem one_le
  given: {a : Associates M}
  statement: 1 <= a
  proof: one_le

中文:
定理 one_le
  条件: {a : Associates M}
  结论: 1 <= a
  证明: one_le
-/
protected theorem one_le {a : Associates M} : 1 <= a :=
  one_le

/--
theorem `le_mul_right` / 定理 `le_mul_right`

English:
theorem le_mul_right
  given: {a b : Associates M}
  statement: a <= a * b
  proof: ⟨b, rfl⟩

中文:
定理 le_mul_right
  条件: {a b : Associates M}
  结论: a <= a * b
  证明: ⟨b, rfl⟩
-/
theorem le_mul_right {a b : Associates M} : a <= a * b :=
  ⟨b, rfl⟩

/--
theorem `le_mul_left` / 定理 `le_mul_left`

English:
theorem le_mul_left
  given: {a b : Associates M}
  statement: a <= b * a
  proof: by rw [mul_comm]; exact le_mul_right

中文:
定理 le_mul_left
  条件: {a b : Associates M}
  结论: a <= b * a
  证明: by rw [mul_comm]; exact le_mul_right

Depends on / 依赖: le_mul_right, mul_comm
-/
theorem le_mul_left {a b : Associates M} : a <= b * a := by rw [mul_comm]; exact le_mul_right

end Order

@[simp]
/--
theorem `mk_dvd_mk` / 定理 `mk_dvd_mk`

English:
theorem mk_dvd_mk
  given: {a b : M}
  statement: Associates.mk a ∣ Associates.mk b ↔ a ∣ b
  proof: by
  simp only [dvd_def, mk_surjective.exists, mk_mul_mk, mk_eq_mk_iff_associated,
    Associated.comm (x := b)]
  constructor
  · rintro ⟨x, u, rfl⟩
    exact ⟨_, mul_assoc ..⟩
  · rintro ⟨c, rfl⟩
    use c

中文:
定理 mk_dvd_mk
  条件: {a b : M}
  结论: Associates.mk a ∣ Associates.mk b ↔ a ∣ b
  证明: by
  simp only [dvd_def, mk_surjective.exists, mk_mul_mk, mk_eq_mk_iff_associated,
    Associated.comm (x := b)]
  constructor
  · rintro ⟨x, u, rfl⟩
    exact ⟨_, mul_assoc ..⟩
  · rintro ⟨c, rfl⟩
    use c

Depends on / 依赖: Associated, Associated.comm, dvd_def, mk_eq_mk_iff_associated, mk_mul_mk, mk_surjective, mk_surjective.exists, mul_assoc
-/
theorem mk_dvd_mk {a b : M} : Associates.mk a ∣ Associates.mk b ↔ a ∣ b := by
  simp only [dvd_def, mk_surjective.exists, mk_mul_mk, mk_eq_mk_iff_associated,
    Associated.comm (x := b)]
  constructor
  · rintro ⟨x, u, rfl⟩
    exact ⟨_, mul_assoc ..⟩
  · rintro ⟨c, rfl⟩
    use c

/--
theorem `dvd_of_mk_le_mk` / 定理 `dvd_of_mk_le_mk`

English:
theorem dvd_of_mk_le_mk
  given: {a b : M}
  statement: Associates.mk a <= Associates.mk b -> a ∣ b
  proof: mk_dvd_mk.mp

中文:
定理 dvd_of_mk_le_mk
  条件: {a b : M}
  结论: Associates.mk a <= Associates.mk b -> a ∣ b
  证明: mk_dvd_mk.mp

Depends on / 依赖: mk_dvd_mk, mk_dvd_mk.mp
-/
theorem dvd_of_mk_le_mk {a b : M} : Associates.mk a <= Associates.mk b -> a ∣ b :=
  mk_dvd_mk.mp

/--
theorem `mk_le_mk_of_dvd` / 定理 `mk_le_mk_of_dvd`

English:
theorem mk_le_mk_of_dvd
  given: {a b : M}
  statement: a ∣ b -> Associates.mk a <= Associates.mk b
  proof: mk_dvd_mk.mpr

中文:
定理 mk_le_mk_of_dvd
  条件: {a b : M}
  结论: a ∣ b -> Associates.mk a <= Associates.mk b
  证明: mk_dvd_mk.mpr

Depends on / 依赖: mk_dvd_mk, mk_dvd_mk.mpr
-/
theorem mk_le_mk_of_dvd {a b : M} : a ∣ b -> Associates.mk a <= Associates.mk b :=
  mk_dvd_mk.mpr

/--
theorem `mk_le_mk_iff_dvd` / 定理 `mk_le_mk_iff_dvd`

English:
theorem mk_le_mk_iff_dvd
  given: {a b : M}
  statement: Associates.mk a <= Associates.mk b ↔ a ∣ b
  proof: mk_dvd_mk

@[simp]

中文:
定理 mk_le_mk_iff_dvd
  条件: {a b : M}
  结论: Associates.mk a <= Associates.mk b ↔ a ∣ b
  证明: mk_dvd_mk

@[simp]

Depends on / 依赖: mk_dvd_mk
-/
theorem mk_le_mk_iff_dvd {a b : M} : Associates.mk a <= Associates.mk b ↔ a ∣ b := mk_dvd_mk

@[simp]
/--
theorem `isPrimal_mk` / 定理 `isPrimal_mk`

English:
theorem isPrimal_mk
  given: {a : M}
  statement: IsPrimal (Associates.mk a) ↔ IsPrimal a
  proof: by
  simp_rw [IsPrimal, forall_associated, mk_surjective.exists, mk_mul_mk, mk_dvd_mk]
  constructor <;> intro h b c dvd <;> obtain ⟨a₁, a₂, h₁, h₂, eq⟩ := @h b c dvd
  · obtain ⟨u, rfl⟩ := mk_eq_mk_iff_associated.mp eq.symm
    exact ⟨a₁, a₂ * u, h₁, Units.mul_right_dvd.mpr h₂, mul_assoc _ _ _⟩
  ·

中文:
定理 isPrimal_mk
  条件: {a : M}
  结论: IsPrimal (Associates.mk a) ↔ IsPrimal a
  证明: by
  simp_rw [IsPrimal, forall_associated, mk_surjective.exists, mk_mul_mk, mk_dvd_mk]
  constructor <;> intro h b c dvd <;> obtain ⟨a₁, a₂, h₁, h₂, eq⟩ := @h b c dvd
  · obtain ⟨u, rfl⟩ := mk_eq_mk_iff_associated.mp eq.symm
    exact ⟨a₁, a₂ * u, h₁, Units.mul_right_dvd.mpr h₂, mul_assoc _ _ _⟩
  ·

Depends on / 依赖: IsPrimal, Units.mul_right_dvd.mpr, congr_arg, eq.symm, forall_associated, mk_dvd_mk, mk_eq_mk_iff_associated, mk_eq_mk_iff_associated.mp, mk_mul_mk, mk_surjective, mk_surjective.exists, mul_assoc, mul_right_dvd, simp_rw
-/
theorem isPrimal_mk {a : M} : IsPrimal (Associates.mk a) ↔ IsPrimal a := by
  simp_rw [IsPrimal, forall_associated, mk_surjective.exists, mk_mul_mk, mk_dvd_mk]
  constructor <;> intro h b c dvd <;> obtain ⟨a₁, a₂, h₁, h₂, eq⟩ := @h b c dvd
  · obtain ⟨u, rfl⟩ := mk_eq_mk_iff_associated.mp eq.symm
    exact ⟨a₁, a₂ * u, h₁, Units.mul_right_dvd.mpr h₂, mul_assoc _ _ _⟩
  · exact ⟨a₁, a₂, h₁, h₂, congr_arg _ eq⟩

@[simp]
/--
theorem `decompositionMonoid_iff` / 定理 `decompositionMonoid_iff`

English:
theorem decompositionMonoid_iff
  statement: DecompositionMonoid (Associates M) ↔ DecompositionMonoid M
  proof: by
  simp_rw [_root_.decompositionMonoid_iff, forall_associated, isPrimal_mk]

中文:
定理 decompositionMonoid_iff
  结论: DecompositionMonoid (Associates M) ↔ DecompositionMonoid M
  证明: by
  simp_rw [_root_.decompositionMonoid_iff, forall_associated, isPrimal_mk]

Depends on / 依赖: _root_, _root_.decompositionMonoid_iff, decompositionMonoid_iff, forall_associated, isPrimal_mk, simp_rw
-/
theorem decompositionMonoid_iff : DecompositionMonoid (Associates M) ↔ DecompositionMonoid M := by
  simp_rw [_root_.decompositionMonoid_iff, forall_associated, isPrimal_mk]

/--
Instance `instDecompositionMonoid` / 实例 `instDecompositionMonoid`

English:
instance instDecompositionMonoid
  signature: [DecompositionMonoid M]
  body: decompositionMonoid_iff.mpr ‹_›

@[simp]

中文:
实例 instDecompositionMonoid
  签名: [DecompositionMonoid M]
  定义体: decompositionMonoid_iff.mpr ‹_›

@[simp]

Depends on / 依赖: decompositionMonoid_iff, decompositionMonoid_iff.mpr
-/
instance instDecompositionMonoid [DecompositionMonoid M] : DecompositionMonoid (Associates M) :=
  decompositionMonoid_iff.mpr ‹_›

@[simp]
/--
theorem `mk_isRelPrime_iff` / 定理 `mk_isRelPrime_iff`

English:
theorem mk_isRelPrime_iff
  given: {a b : M}
  proof: by
  simp_rw [IsRelPrime, forall_associated, mk_dvd_mk, isUnit_mk]

中文:
定理 mk_isRelPrime_iff
  条件: {a b : M}
  证明: by
  simp_rw [IsRelPrime, forall_associated, mk_dvd_mk, isUnit_mk]

Depends on / 依赖: IsRelPrime, forall_associated, isUnit_mk, mk_dvd_mk, simp_rw
-/
theorem mk_isRelPrime_iff {a b : M} :
    IsRelPrime (Associates.mk a) (Associates.mk b) ↔ IsRelPrime a b := by
  simp_rw [IsRelPrime, forall_associated, mk_dvd_mk, isUnit_mk]

end CommMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: M] [Monoid M] : Zero (Associates M)
  body: ⟨⟦0⟧⟩

中文:
实例 [Zero
  签名: M] [Monoid M] : Zero (Associates M)
  定义体: ⟨⟦0⟧⟩
-/
instance [Zero M] [Monoid M] : Zero (Associates M) :=
  ⟨⟦0⟧⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: M] [Monoid M] : Top (Associates M)
  body: ⟨0⟩

中文:
实例 [Zero
  签名: M] [Monoid M] : Top (Associates M)
  定义体: ⟨0⟩
-/
instance [Zero M] [Monoid M] : Top (Associates M) :=
  ⟨0⟩

/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  given: [Zero M] [Monoid M]
  statement: Associates.mk (0 : M) = 0
  proof: rfl

中文:
定理 mk_zero
  条件: [Zero M] [Monoid M]
  结论: Associates.mk (0 : M) = 0
  证明: rfl
-/
@[simp] theorem mk_zero [Zero M] [Monoid M] : Associates.mk (0 : M) = 0 := rfl

section MonoidWithZero

variable [MonoidWithZero M]

@[simp]
/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: {a : M}
  statement: Associates.mk a = 0 ↔ a = 0
  proof: ⟨fun h => (associated_zero_iff_eq_zero a).1 Quotient.exact h, fun h => h.symm ▸ rfl⟩

@[simp]

中文:
定理 mk_eq_zero
  条件: {a : M}
  结论: Associates.mk a = 0 ↔ a = 0
  证明: ⟨fun h => (associated_zero_iff_eq_zero a).1 Quotient.exact h, fun h => h.symm ▸ rfl⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.exact, associated_zero_iff_eq_zero, h.symm
-/
theorem mk_eq_zero {a : M} : Associates.mk a = 0 ↔ a = 0 :=
⟨fun h => (associated_zero_iff_eq_zero a).1 Quotient.exact h, fun h => h.symm ▸ rfl⟩

@[simp]
/--
theorem `quot_out_zero` / 定理 `quot_out_zero`

English:
theorem quot_out_zero
  statement: Quot.out (0 : Associates M) = 0
  proof: by rw [← mk_eq_zero, quot_out]

中文:
定理 quot_out_zero
  结论: Quot.out (0 : Associates M) = 0
  证明: by rw [← mk_eq_zero, quot_out]

Depends on / 依赖: mk_eq_zero, quot_out
-/
theorem quot_out_zero : Quot.out (0 : Associates M) = 0 := by rw [← mk_eq_zero, quot_out]

/--
theorem `mk_ne_zero` / 定理 `mk_ne_zero`

English:
theorem mk_ne_zero
  given: {a : M}
  statement: Associates.mk a != 0 ↔ a != 0
  proof: not_congr mk_eq_zero

中文:
定理 mk_ne_zero
  条件: {a : M}
  结论: Associates.mk a != 0 ↔ a != 0
  证明: not_congr mk_eq_zero

Depends on / 依赖: mk_eq_zero, not_congr
-/
theorem mk_ne_zero {a : M} : Associates.mk a != 0 ↔ a != 0 :=
  not_congr mk_eq_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] : Nontrivial (Associates M)
  body: ⟨⟨1, 0, mk_ne_zero.2 one_ne_zero⟩⟩

中文:
实例 [Nontrivial
  签名: M] : Nontrivial (Associates M)
  定义体: ⟨⟨1, 0, mk_ne_zero.2 one_ne_zero⟩⟩

Depends on / 依赖: mk_ne_zero, one_ne_zero
-/
instance [Nontrivial M] : Nontrivial (Associates M) :=
  ⟨⟨1, 0, mk_ne_zero.2 one_ne_zero⟩⟩

/--
theorem `exists_non_zero_rep` / 定理 `exists_non_zero_rep`

English:
theorem exists_non_zero_rep
  given: {a : Associates M}
  statement: a != 0 -> exists a0 : M, a0 != 0 ∧ Associates.mk a0 = a
  proof: Quotient.inductionOn a fun b nz => ⟨b, mt (congr_arg Quotient.mk'') nz, rfl⟩

中文:
定理 exists_non_zero_rep
  条件: {a : Associates M}
  结论: a != 0 -> 存在 a0 : M, a0 != 0 ∧ Associates.mk a0 = a
  证明: Quotient.inductionOn a fun b nz => ⟨b, mt (congr_arg Quotient.mk'') nz, rfl⟩

Depends on / 依赖: Quotient, Quotient.inductionOn, Quotient.mk, congr_arg, inductionOn
-/
theorem exists_non_zero_rep {a : Associates M} : a != 0 -> exists a0 : M, a0 != 0 ∧ Associates.mk a0 = a :=
  Quotient.inductionOn a fun b nz => ⟨b, mt (congr_arg Quotient.mk'') nz, rfl⟩

end MonoidWithZero

section CommMonoidWithZero

variable [CommMonoidWithZero M]

/--
Instance `instCommMonoidWithZero` / 实例 `instCommMonoidWithZero`

English:
instance instCommMonoidWithZero
  signature: : CommMonoidWithZero (Associates M) where
  body: forall_associated.2 fun a => by rw [← mk_zero, mk_mul_mk, zero_mul]
    mul_zero := forall_associated.2 fun a => by rw [← mk_zero, mk_mul_mk, mul_zero]

中文:
实例 instCommMonoidWithZero
  签名: : CommMonoidWithZero (Associates M) where
  定义体: forall_associated.2 fun a => by rw [← mk_zero, mk_mul_mk, zero_mul]
    mul_zero := forall_associated.2 fun a => by rw [← mk_zero, mk_mul_mk, mul_zero]

Depends on / 依赖: forall_associated, mk_mul_mk, mk_zero, zero_mul
-/
instance instCommMonoidWithZero : CommMonoidWithZero (Associates M) where
    zero_mul := forall_associated.2 fun a => by rw [← mk_zero, mk_mul_mk, zero_mul]
    mul_zero := forall_associated.2 fun a => by rw [← mk_zero, mk_mul_mk, mul_zero]

/--
Instance `instOrderTop` / 实例 `instOrderTop`

English:
instance instOrderTop
  signature: : OrderTop (Associates M) where
  body: 0
  le_top := dvd_zero

中文:
实例 instOrderTop
  签名: : OrderTop (Associates M) where
  定义体: 0
  le_top := dvd_zero
-/
instance instOrderTop : OrderTop (Associates M) where
  top := 0
  le_top := dvd_zero

/--
theorem `le_zero` / 定理 `le_zero`

English:
theorem le_zero
  given: (a : Associates M)
  statement: a <= 0
  proof: le_top

中文:
定理 le_zero
  条件: (a : Associates M)
  结论: a <= 0
  证明: le_top
-/
@[simp] protected theorem le_zero (a : Associates M) : a <= 0 := le_top

/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: : BoundedOrder (Associates M) where

中文:
实例 instBoundedOrder
  签名: : BoundedOrder (Associates M) where
-/
instance instBoundedOrder : BoundedOrder (Associates M) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableRel
  signature: ((· ∣ ·) : M -> M -> Prop)] :
  body: fun a b =>
  Quotient.recOnSubsingleton₂ a b fun _ _ => decidable_of_iff' _ mk_dvd_mk

中文:
实例 [DecidableRel
  签名: ((· ∣ ·) : M -> M -> 命题)] :
  定义体: fun a b =>
  Quotient.recOnSubsingleton₂ a b fun _ _ => decidable_of_iff' _ mk_dvd_mk
-/
instance [DecidableRel ((· ∣ ·) : M -> M -> Prop)] :
    DecidableRel ((· ∣ ·) : Associates M -> Associates M -> Prop) := fun a b =>
  Quotient.recOnSubsingleton₂ a b fun _ _ => decidable_of_iff' _ mk_dvd_mk

/--
theorem `Prime.le_or_le` / 定理 `Prime.le_or_le`

English:
theorem Prime.le_or_le
  given: {p : Associates M} (hp : Prime p) {a b : Associates M} (h : p <= a * b)
  proof: hp.2.2 a b h

@[simp]

中文:
定理 Prime.le_or_le
  条件: {p : Associates M} (hp : Prime p) {a b : Associates M} (h : p <= a * b)
  证明: hp.2.2 a b h

@[simp]
-/
theorem Prime.le_or_le {p : Associates M} (hp : Prime p) {a b : Associates M} (h : p <= a * b) :
    p <= a ∨ p <= b :=
  hp.2.2 a b h

@[simp]
/--
theorem `prime_mk` / 定理 `prime_mk`

English:
theorem prime_mk
  given: {p : M}
  statement: Prime (Associates.mk p) ↔ Prime p
  proof: by
  rw [Prime]; rw [_root_.Prime]; rw [forall_associated]
  simp only [forall_associated, mk_ne_zero, isUnit_mk, mk_mul_mk, mk_dvd_mk]

@[simp]

中文:
定理 prime_mk
  条件: {p : M}
  结论: Prime (Associates.mk p) ↔ Prime p
  证明: by
  rw [Prime]; rw [_root_.Prime]; rw [forall_associated]
  simp only [forall_associated, mk_ne_zero, isUnit_mk, mk_mul_mk, mk_dvd_mk]

@[simp]

Depends on / 依赖: _root_, _root_.Prime, forall_associated, isUnit_mk, mk_dvd_mk, mk_mul_mk, mk_ne_zero
-/
theorem prime_mk {p : M} : Prime (Associates.mk p) ↔ Prime p := by
  rw [Prime]; rw [_root_.Prime]; rw [forall_associated]
  simp only [forall_associated, mk_ne_zero, isUnit_mk, mk_mul_mk, mk_dvd_mk]

@[simp]
/--
theorem `irreducible_mk` / 定理 `irreducible_mk`

English:
theorem irreducible_mk
  given: {a : M}
  statement: Irreducible (Associates.mk a) ↔ Irreducible a
  proof: by
  simp only [irreducible_iff, isUnit_mk, forall_associated, isUnit_mk, mk_mul_mk,
    mk_eq_mk_iff_associated, Associated.comm (x := a)]
  apply Iff.rfl.and
  constructor
  · rintro h x y rfl
exact h _ _ .refl _
  · rintro h x y ⟨u, rfl⟩
    simpa using h (mul_assoc _ _ _)

@[simp]

中文:
定理 irreducible_mk
  条件: {a : M}
  结论: Irreducible (Associates.mk a) ↔ Irreducible a
  证明: by
  simp only [irreducible_iff, isUnit_mk, forall_associated, isUnit_mk, mk_mul_mk,
    mk_eq_mk_iff_associated, Associated.comm (x := a)]
  apply Iff.rfl.and
  constructor
  · rintro h x y rfl
exact h _ _ .refl _
  · rintro h x y ⟨u, rfl⟩
    simpa using h (mul_assoc _ _ _)

@[simp]

Depends on / 依赖: Associated, Associated.comm, Iff.rfl.and, forall_associated, irreducible_iff, isUnit_mk, mk_eq_mk_iff_associated, mk_mul_mk, mul_assoc
-/
theorem irreducible_mk {a : M} : Irreducible (Associates.mk a) ↔ Irreducible a := by
  simp only [irreducible_iff, isUnit_mk, forall_associated, isUnit_mk, mk_mul_mk,
    mk_eq_mk_iff_associated, Associated.comm (x := a)]
  apply Iff.rfl.and
  constructor
  · rintro h x y rfl
exact h _ _ .refl _
  · rintro h x y ⟨u, rfl⟩
    simpa using h (mul_assoc _ _ _)

@[simp]
/--
theorem `mk_dvdNotUnit_mk_iff` / 定理 `mk_dvdNotUnit_mk_iff`

English:
theorem mk_dvdNotUnit_mk_iff
  given: {a b : M}
  proof: by
  simp only [DvdNotUnit, mk_ne_zero, mk_surjective.exists, isUnit_mk, mk_mul_mk,
    mk_eq_mk_iff_associated, Associated.comm (x := b)]
  refine Iff.rfl.and ?_
  constructor
  · rintro ⟨x, hx, u, rfl⟩
    refine ⟨x * u, ?_, mul_assoc ..⟩
    simpa
  · rintro ⟨x, ⟨hx, rfl⟩⟩
    use x

中文:
定理 mk_dvdNotUnit_mk_iff
  条件: {a b : M}
  证明: by
  simp only [DvdNotUnit, mk_ne_zero, mk_surjective.exists, isUnit_mk, mk_mul_mk,
    mk_eq_mk_iff_associated, Associated.comm (x := b)]
  refine Iff.rfl.and ?_
  constructor
  · rintro ⟨x, hx, u, rfl⟩
    refine ⟨x * u, ?_, mul_assoc ..⟩
    simpa
  · rintro ⟨x, ⟨hx, rfl⟩⟩
    use x

Depends on / 依赖: Associated, Associated.comm, DvdNotUnit, Iff.rfl.and, isUnit_mk, mk_eq_mk_iff_associated, mk_mul_mk, mk_ne_zero, mk_surjective, mk_surjective.exists, mul_assoc
-/
theorem mk_dvdNotUnit_mk_iff {a b : M} :
    DvdNotUnit (Associates.mk a) (Associates.mk b) ↔ DvdNotUnit a b := by
  simp only [DvdNotUnit, mk_ne_zero, mk_surjective.exists, isUnit_mk, mk_mul_mk,
    mk_eq_mk_iff_associated, Associated.comm (x := b)]
  refine Iff.rfl.and ?_
  constructor
  · rintro ⟨x, hx, u, rfl⟩
    refine ⟨x * u, ?_, mul_assoc ..⟩
    simpa
  · rintro ⟨x, ⟨hx, rfl⟩⟩
    use x

/--
theorem `dvdNotUnit_of_lt` / 定理 `dvdNotUnit_of_lt`

English:
theorem dvdNotUnit_of_lt
  given: {a b : Associates M} (hlt : a < b)
  statement: DvdNotUnit a b
  proof: by
  constructor
  · rintro rfl
    apply not_lt_of_ge _ hlt
    apply dvd_zero
  rcases hlt with ⟨⟨x, rfl⟩, ndvd⟩
  refine ⟨x, ?_, rfl⟩
  contrapose ndvd
  rcases ndvd with ⟨u, rfl⟩
  simp

中文:
定理 dvdNotUnit_of_lt
  条件: {a b : Associates M} (hlt : a < b)
  结论: DvdNotUnit a b
  证明: by
  constructor
  · rintro rfl
    apply not_lt_of_ge _ hlt
    apply dvd_zero
  rcases hlt with ⟨⟨x, rfl⟩, ndvd⟩
  refine ⟨x, ?_, rfl⟩
  contrapose ndvd
  rcases ndvd with ⟨u, rfl⟩
  simp

Depends on / 依赖: contrapose, dvd_zero, not_lt_of_ge
-/
theorem dvdNotUnit_of_lt {a b : Associates M} (hlt : a < b) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    apply not_lt_of_ge _ hlt
    apply dvd_zero
  rcases hlt with ⟨⟨x, rfl⟩, ndvd⟩
  refine ⟨x, ?_, rfl⟩
  contrapose ndvd
  rcases ndvd with ⟨u, rfl⟩
  simp

/--
theorem `irreducible_iff_prime_iff` / 定理 `irreducible_iff_prime_iff`

English:
theorem irreducible_iff_prime_iff
  proof: by
  simp_rw [forall_associated, irreducible_mk, prime_mk]

中文:
定理 irreducible_iff_prime_iff
  证明: by
  simp_rw [forall_associated, irreducible_mk, prime_mk]

Depends on / 依赖: forall_associated, irreducible_mk, prime_mk, simp_rw
-/
theorem irreducible_iff_prime_iff :
    (forall a : M, Irreducible a ↔ Prime a) ↔ forall a : Associates M, Irreducible a ↔ Prime a := by
  simp_rw [forall_associated, irreducible_mk, prime_mk]

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CommMonoidWithZero M] [IsCancelMulZero M]

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (Associates M) where
  body: mk_surjective.forall₂.2 fun _a _b hab hba => mk_eq_mk_iff_associated.2
    associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba)

中文:
实例 instPartialOrder
  签名: : PartialOrder (Associates M) where
  定义体: mk_surjective.forall₂.2 fun _a _b hab hba => mk_eq_mk_iff_associated.2
    associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba)

Depends on / 依赖: mk_eq_mk_iff_associated, mk_surjective, mk_surjective.forall
-/
instance instPartialOrder : PartialOrder (Associates M) where
le_antisymm := mk_surjective.forall₂.2 fun _a _b hab hba => mk_eq_mk_iff_associated.2
    associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba)

/--
Instance `instIsCancelMulZero` / 实例 `instIsCancelMulZero`

English:
instance instIsCancelMulZero
  signature: : IsCancelMulZero (Associates M)
  body: @IsLeftCancelMulZero.to_isCancelMulZero _ _ _
  { mul_left_cancel_of_ne_zero := by
      rintro ⟨a⟩ ha ⟨b⟩ ⟨c⟩ h
      rcases Quotient.exact' h with ⟨u, hu⟩
      have hu : a * (b * ↑u) = a * c := by rwa [← mul_assoc]
      exact Quotient.sound' ⟨u, mul_left_cancel₀ (mk_ne_zero.1 ha) hu⟩ }

中文:
实例 instIsCancelMulZero
  签名: : IsCancelMulZero (Associates M)
  定义体: @IsLeftCancelMulZero.to_isCancelMulZero _ _ _
  { mul_left_cancel_of_ne_zero := by
      rintro ⟨a⟩ ha ⟨b⟩ ⟨c⟩ h
      rcases Quotient.exact' h with ⟨u, hu⟩
      have hu : a * (b * ↑u) = a * c := by rwa [← mul_assoc]
      exact Quotient.sound' ⟨u, mul_left_cancel₀ (mk_ne_zero.1 ha) hu⟩ }

Depends on / 依赖: IsLeftCancelMulZero, IsLeftCancelMulZero.to_isCancelMulZero, Quotient, Quotient.exact, Quotient.sound, evalCompCoyonedaCorepresentable, mk_ne_zero, mul_assoc, mul_left_cancel_of_ne_zero, to_isCancelMulZero
-/
instance instIsCancelMulZero : IsCancelMulZero (Associates M) :=
  @IsLeftCancelMulZero.to_isCancelMulZero _ _ _
  { mul_left_cancel_of_ne_zero := by
      rintro ⟨a⟩ ha ⟨b⟩ ⟨c⟩ h
      rcases Quotient.exact' h with ⟨u, hu⟩
      have hu : a * (b * ↑u) = a * c := by rwa [← mul_assoc]
      exact Quotient.sound' ⟨u, mul_left_cancel₀ (mk_ne_zero.1 ha) hu⟩ }

/--
theorem `_root_.associates_irreducible_iff_prime` / 定理 `_root_.associates_irreducible_iff_prime`

English:
theorem _root_.associates_irreducible_iff_prime
  given: [DecompositionMonoid M] {p : Associates M}
  proof: irreducible_iff_prime

中文:
定理 _root_.associates_irreducible_iff_prime
  条件: [DecompositionMonoid M] {p : Associates M}
  证明: irreducible_iff_prime

Depends on / 依赖: irreducible_iff_prime
-/
theorem _root_.associates_irreducible_iff_prime [DecompositionMonoid M] {p : Associates M} :
    Irreducible p ↔ Prime p := irreducible_iff_prime

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoZeroDivisors (Associates M)
  body: by infer_instance

中文:
实例 :
  签名: NoZeroDivisors (Associates M)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : NoZeroDivisors (Associates M) := by infer_instance

/--
theorem `le_of_mul_le_mul_left` / 定理 `le_of_mul_le_mul_left`

English:
theorem le_of_mul_le_mul_left
  given: (a b c : Associates M) (ha : a != 0)
  statement: a * b <= a * c -> b <= c

中文:
定理 le_of_mul_le_mul_left
  条件: (a b c : Associates M) (ha : a != 0)
  结论: a * b <= a * c -> b <= c
-/
theorem le_of_mul_le_mul_left (a b c : Associates M) (ha : a != 0) : a * b <= a * c -> b <= c
| ⟨d, hd⟩ => ⟨d, mul_left_cancel₀ ha by rwa [← mul_assoc]⟩

/--
theorem `one_or_eq_of_le_of_prime` / 定理 `one_or_eq_of_le_of_prime`

English:
theorem one_or_eq_of_le_of_prime
  given: {p m : Associates M} (hp : Prime p) (hle : m <= p)
  proof: by
  rcases mk_surjective p with ⟨p, rfl⟩
  rcases mk_surjective m with ⟨m, rfl⟩
  simpa [mk_eq_mk_iff_associated, Associated.comm]
    using (prime_mk.1 hp).irreducible.dvd_iff.mp (mk_le_mk_iff_dvd.1 hle)

中文:
定理 one_or_eq_of_le_of_prime
  条件: {p m : Associates M} (hp : Prime p) (hle : m <= p)
  证明: by
  rcases mk_surjective p with ⟨p, rfl⟩
  rcases mk_surjective m with ⟨m, rfl⟩
  simpa [mk_eq_mk_iff_associated, Associated.comm]
    using (prime_mk.1 hp).irreducible.dvd_iff.mp (mk_le_mk_iff_dvd.1 hle)

Depends on / 依赖: Associated, Associated.comm, dvd_iff, irreducible, irreducible.dvd_iff.mp, mk_eq_mk_iff_associated, mk_le_mk_iff_dvd, mk_surjective, prime_mk
-/
theorem one_or_eq_of_le_of_prime {p m : Associates M} (hp : Prime p) (hle : m <= p) :
    m = 1 ∨ m = p := by
  rcases mk_surjective p with ⟨p, rfl⟩
  rcases mk_surjective m with ⟨m, rfl⟩
  simpa [mk_eq_mk_iff_associated, Associated.comm]
    using (prime_mk.1 hp).irreducible.dvd_iff.mp (mk_le_mk_iff_dvd.1 hle)

/--
theorem `dvdNotUnit_iff_lt` / 定理 `dvdNotUnit_iff_lt`

English:
theorem dvdNotUnit_iff_lt
  given: {a b : Associates M}
  statement: DvdNotUnit a b ↔ a < b
  proof: dvd_and_not_dvd_iff.symm

中文:
定理 dvdNotUnit_iff_lt
  条件: {a b : Associates M}
  结论: DvdNotUnit a b ↔ a < b
  证明: dvd_and_not_dvd_iff.symm

Depends on / 依赖: dvd_and_not_dvd_iff, dvd_and_not_dvd_iff.symm
-/
theorem dvdNotUnit_iff_lt {a b : Associates M} : DvdNotUnit a b ↔ a < b :=
  dvd_and_not_dvd_iff.symm

/--
theorem `le_one_iff` / 定理 `le_one_iff`

English:
theorem le_one_iff
  given: {p : Associates M}
  statement: p <= 1 ↔ p = 1
  proof: by rw [← Associates.bot_eq_one, le_bot_iff]

中文:
定理 le_one_iff
  条件: {p : Associates M}
  结论: p <= 1 ↔ p = 1
  证明: by rw [← Associates.bot_eq_one, le_bot_iff]

Depends on / 依赖: Associates, Associates.bot_eq_one, bot_eq_one, le_bot_iff
-/
theorem le_one_iff {p : Associates M} : p <= 1 ↔ p = 1 := by rw [← Associates.bot_eq_one, le_bot_iff]

end CancelCommMonoidWithZero

end Associates

section CommMonoidWithZero

variable [CommMonoidWithZero M] {p q r : M}

/--
theorem `dvdNotUnit_of_dvdNotUnit_associated` / 定理 `dvdNotUnit_of_dvdNotUnit_associated`

English:
theorem dvdNotUnit_of_dvdNotUnit_associated
  proof: by
  obtain ⟨u, rfl⟩ := h'
  obtain ⟨hp, x, hx⟩ := h
  refine ⟨hp, x * u, mt isUnit_of_mul_isUnit_left hx.1, ?_⟩
  rw [← mul_assoc]; rw [← hx.right]

alias Associated.dvdNotUnit_right := dvdNotUnit_of_dvdNotUnit_associated

中文:
定理 dvdNotUnit_of_dvdNotUnit_associated
  证明: by
  obtain ⟨u, rfl⟩ := h'
  obtain ⟨hp, x, hx⟩ := h
  refine ⟨hp, x * u, mt isUnit_of_mul_isUnit_left hx.1, ?_⟩
  rw [← mul_assoc]; rw [← hx.right]

alias Associated.dvdNotUnit_right := dvdNotUnit_of_dvdNotUnit_associated

Depends on / 依赖: hx.right, isUnit_of_mul_isUnit_left, mul_assoc
-/
theorem dvdNotUnit_of_dvdNotUnit_associated
    (h : DvdNotUnit p q) (h' : Associated q r) : DvdNotUnit p r := by
  obtain ⟨u, rfl⟩ := h'
  obtain ⟨hp, x, hx⟩ := h
  refine ⟨hp, x * u, mt isUnit_of_mul_isUnit_left hx.1, ?_⟩
  rw [← mul_assoc]; rw [← hx.right]

alias Associated.dvdNotUnit_right := dvdNotUnit_of_dvdNotUnit_associated

/--
theorem `Associated.dvdNotUnit_left` / 定理 `Associated.dvdNotUnit_left`

English:
theorem Associated.dvdNotUnit_left
  given: (h : DvdNotUnit p r) (h' : Associated p q)
  proof: by
  obtain ⟨u, rfl⟩ := h'.symm
  obtain ⟨hp, x, hx⟩ := h
  have hq : q != 0 := by simp_all
  refine ⟨hq, x * u, mt isUnit_of_mul_isUnit_left hx.1, ?_⟩
  rw [mul_comm x]; rw [← mul_assoc]; rw [← hx.2]

中文:
定理 Associated.dvdNotUnit_left
  条件: (h : DvdNotUnit p r) (h' : Associated p q)
  证明: by
  obtain ⟨u, rfl⟩ := h'.symm
  obtain ⟨hp, x, hx⟩ := h
  have hq : q != 0 := by simp_all
  refine ⟨hq, x * u, mt isUnit_of_mul_isUnit_left hx.1, ?_⟩
  rw [mul_comm x]; rw [← mul_assoc]; rw [← hx.2]

Depends on / 依赖: isUnit_of_mul_isUnit_left, mul_assoc, mul_comm
-/
theorem Associated.dvdNotUnit_left (h : DvdNotUnit p r) (h' : Associated p q) :
    DvdNotUnit q r := by
  obtain ⟨u, rfl⟩ := h'.symm
  obtain ⟨hp, x, hx⟩ := h
  have hq : q != 0 := by simp_all
  refine ⟨hq, x * u, mt isUnit_of_mul_isUnit_left hx.1, ?_⟩
  rw [mul_comm x]; rw [← mul_assoc]; rw [← hx.2]

/--
theorem `Associated.dvdNotUnit_left_iff` / 定理 `Associated.dvdNotUnit_left_iff`

English:
theorem Associated.dvdNotUnit_left_iff
  given: (h : Associated p q)
  statement: DvdNotUnit p r ↔ DvdNotUnit q r where
  proof: (h.dvdNotUnit_left ·)
  mpr := (h.symm.dvdNotUnit_left ·)

中文:
定理 Associated.dvdNotUnit_left_iff
  条件: (h : Associated p q)
  结论: DvdNotUnit p r ↔ DvdNotUnit q r where
  证明: (h.dvdNotUnit_left ·)
  mpr := (h.symm.dvdNotUnit_left ·)

Depends on / 依赖: dvdNotUnit_left, h.dvdNotUnit_left
-/
theorem Associated.dvdNotUnit_left_iff (h : Associated p q) : DvdNotUnit p r ↔ DvdNotUnit q r where
  mp := (h.dvdNotUnit_left ·)
  mpr := (h.symm.dvdNotUnit_left ·)

/--
theorem `Associated.dvdNotUnit_right_iff` / 定理 `Associated.dvdNotUnit_right_iff`

English:
theorem Associated.dvdNotUnit_right_iff
  given: (h : Associated q r)
  statement: DvdNotUnit p q ↔ DvdNotUnit p r where
  proof: (h.dvdNotUnit_right ·)
  mpr := (h.symm.dvdNotUnit_right ·)

中文:
定理 Associated.dvdNotUnit_right_iff
  条件: (h : Associated q r)
  结论: DvdNotUnit p q ↔ DvdNotUnit p r where
  证明: (h.dvdNotUnit_right ·)
  mpr := (h.symm.dvdNotUnit_right ·)

Depends on / 依赖: dvdNotUnit_right, h.dvdNotUnit_right
-/
theorem Associated.dvdNotUnit_right_iff (h : Associated q r) : DvdNotUnit p q ↔ DvdNotUnit p r where
  mp := (h.dvdNotUnit_right ·)
  mpr := (h.symm.dvdNotUnit_right ·)

/--
theorem `Associated.acc_dvdNotUnit_iff` / 定理 `Associated.acc_dvdNotUnit_iff`

English:
theorem Associated.acc_dvdNotUnit_iff
  given: (h : Associated p q)
  proof: .intro _ fun _r hr => acc.inv (h.dvdNotUnit_right_iff.mpr hr)
  mpr acc := .intro _ fun _r hr => acc.inv (h.dvdNotUnit_right_iff.mp hr)

中文:
定理 Associated.acc_dvdNotUnit_iff
  条件: (h : Associated p q)
  证明: .intro _ fun _r hr => acc.inv (h.dvdNotUnit_right_iff.mpr hr)
  mpr acc := .intro _ fun _r hr => acc.inv (h.dvdNotUnit_right_iff.mp hr)

Depends on / 依赖: acc.inv, dvdNotUnit_right_iff, h.dvdNotUnit_right_iff.mpr
-/
theorem Associated.acc_dvdNotUnit_iff (h : Associated p q) :
    Acc DvdNotUnit p ↔ Acc DvdNotUnit q where
  mp acc := .intro _ fun _r hr => acc.inv (h.dvdNotUnit_right_iff.mpr hr)
  mpr acc := .intro _ fun _r hr => acc.inv (h.dvdNotUnit_right_iff.mp hr)

end CommMonoidWithZero

section CancelCommMonoidWithZero

/--
theorem `isUnit_of_associated_mul` / 定理 `isUnit_of_associated_mul`

English:
theorem isUnit_of_associated_mul
  statement: [CommMonoidWithZero M] [IsCancelMulZero M] {p b : M}
  proof: by
  obtain ⟨a, ha⟩ := h
  refine .of_mul_eq_one a ((mul_right_inj' hp).mp ?_)
  rwa [← mul_assoc, mul_one]

中文:
定理 isUnit_of_associated_mul
  结论: [CommMonoidWithZero M] [IsCancelMulZero M] {p b : M}
  证明: by
  obtain ⟨a, ha⟩ := h
  refine .of_mul_eq_one a ((mul_right_inj' hp).mp ?_)
  rwa [← mul_assoc, mul_one]

Depends on / 依赖: mul_assoc, mul_one, mul_right_inj, of_mul_eq_one
-/
theorem isUnit_of_associated_mul [CommMonoidWithZero M] [IsCancelMulZero M] {p b : M}
    (h : Associated (p * b) p) (hp : p != 0) : IsUnit b := by
  obtain ⟨a, ha⟩ := h
  refine .of_mul_eq_one a ((mul_right_inj' hp).mp ?_)
  rwa [← mul_assoc, mul_one]

/--
theorem `DvdNotUnit.not_associated` / 定理 `DvdNotUnit.not_associated`

English:
theorem DvdNotUnit.not_associated
  statement: [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
  proof: by
  rintro ⟨a, rfl⟩
  obtain ⟨hp, x, hx, hx'⟩ := h
  rcases (mul_right_inj' hp).mp hx' with rfl
  exact hx a.isUnit

中文:
定理 DvdNotUnit.not_associated
  结论: [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
  证明: by
  rintro ⟨a, rfl⟩
  obtain ⟨hp, x, hx, hx'⟩ := h
  rcases (mul_right_inj' hp).mp hx' with rfl
  exact hx a.isUnit

Depends on / 依赖: a.isUnit, isUnit, mul_right_inj
-/
theorem DvdNotUnit.not_associated [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
    (h : DvdNotUnit p q) : ¬Associated p q := by
  rintro ⟨a, rfl⟩
  obtain ⟨hp, x, hx, hx'⟩ := h
  rcases (mul_right_inj' hp).mp hx' with rfl
  exact hx a.isUnit

/--
theorem `dvd_prime_pow` / 定理 `dvd_prime_pow`

English:
theorem dvd_prime_pow
  given: [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M} (hp : Prime p) (n : Nat)
  proof: by
  induction n generalizing q with
  | zero =>
    simp [← isUnit_iff_dvd_one, associated_one_iff_isUnit]
  | succ n ih =>
    refine ⟨fun h => ?_, fun ⟨i, hi, hq⟩ => hq.dvd.trans (pow_dvd_pow p hi)⟩
    rw [pow_succ'] at h
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with (⟨q, rfl⟩ | hno)
   

中文:
定理 dvd_prime_pow
  条件: [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M} (hp : Prime p) (n : 自然数)
  证明: by
  induction n generalizing q with
  | zero =>
    simp [← isUnit_iff_dvd_one, associated_one_iff_isUnit]
  | succ n ih =>
    refine ⟨fun h => ?_, fun ⟨i, hi, hq⟩ => hq.dvd.trans (pow_dvd_pow p hi)⟩
    rw [pow_succ'] at h
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with (⟨q, rfl⟩ | hno)
   

Depends on / 依赖: Nat.succ_le_succ, associated_one_iff_isUnit, generalizing, hi.trans, hp.left_dvd_or_dvd_right_of_dvd_mul, hp.ne_zero, hq.dvd.trans, hq.mul_left, ih.mp, isUnit_iff_dvd_one, le_succ, left_dvd_or_dvd_right_of_dvd_mul, mul_dvd_mul_iff_left, mul_left, n.le_succ, ne_zero, pow_dvd_pow, pow_succ, succ_le_succ
-/
theorem dvd_prime_pow [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M} (hp : Prime p) (n : Nat) :
    q ∣ p ^ n ↔ exists i <= n, Associated q (p ^ i) := by
  induction n generalizing q with
  | zero =>
    simp [← isUnit_iff_dvd_one, associated_one_iff_isUnit]
  | succ n ih =>
    refine ⟨fun h => ?_, fun ⟨i, hi, hq⟩ => hq.dvd.trans (pow_dvd_pow p hi)⟩
    rw [pow_succ'] at h
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with (⟨q, rfl⟩ | hno)
    · rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at h
      rcases h with ⟨i, hi, hq⟩
      refine ⟨i + 1, Nat.succ_le_succ hi, (hq.mul_left p).trans ?_⟩
      rw [pow_succ']
    · obtain ⟨i, hi, hq⟩ := ih.mp hno
      exact ⟨i, hi.trans n.le_succ, hq⟩

end CancelCommMonoidWithZero
