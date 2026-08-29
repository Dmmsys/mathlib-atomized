/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.GroupLike

/-!
# Group-like elements in a Hopf algebra

This file proves that group-like elements in a Hopf algebra form a group.
-/

@[expose] public section

open HopfAlgebra

variable {R A : Type*}

section Semiring
variable [CommSemiring R] [Semiring A] [HopfAlgebra R A] {a b : A}

/--
lemma `IsGroupLikeElem.antipode_mul_cancel` / 引理 `IsGroupLikeElem.antipode_mul_cancel`

English:
lemma IsGroupLikeElem.antipode_mul_cancel
  given: (ha : IsGroupLikeElem R a)
  proof: by
  simpa [ha, -mul_antipode_lTensor_comul_apply] using mul_antipode_rTensor_comul_apply (R := R) a

中文:
引理 IsGroupLikeElem.antipode_mul_cancel
  条件: (ha : IsGroupLikeElem R a)
  证明: by
  simpa [ha, -mul_antipode_lTensor_comul_apply] using mul_antipode_rTensor_comul_apply (R := R) a
-/
@[simp] lemma IsGroupLikeElem.antipode_mul_cancel (ha : IsGroupLikeElem R a) :
    antipode R a * a = 1 := by
  simpa [ha, -mul_antipode_lTensor_comul_apply] using mul_antipode_rTensor_comul_apply (R := R) a

/--
lemma `IsGroupLikeElem.mul_antipode_cancel` / 引理 `IsGroupLikeElem.mul_antipode_cancel`

English:
lemma IsGroupLikeElem.mul_antipode_cancel
  given: (ha : IsGroupLikeElem R a)
  proof: by
  simpa [ha, -mul_antipode_lTensor_comul_apply] using mul_antipode_lTensor_comul_apply (R := R) a

中文:
引理 IsGroupLikeElem.mul_antipode_cancel
  条件: (ha : IsGroupLikeElem R a)
  证明: by
  simpa [ha, -mul_antipode_lTensor_comul_apply] using mul_antipode_lTensor_comul_apply (R := R) a
-/
@[simp] lemma IsGroupLikeElem.mul_antipode_cancel (ha : IsGroupLikeElem R a) :
    a * antipode R a = 1 := by
  simpa [ha, -mul_antipode_lTensor_comul_apply] using mul_antipode_lTensor_comul_apply (R := R) a

variable (R) in
/-- Turn a group-like element `a` into a unit with inverse its antipode. -/
@[simps]
/--
Definition of `GroupLike.toUnits` / `GroupLike.toUnits` 的定义

English:
definition GroupLike.toUnits
  signature: : GroupLike R A ->* Aˣ where
  body: {
    val := a
    inv := antipode R a
    val_inv := a.2.mul_antipode_cancel
    inv_val := a.2.antipode_mul_cancel
  }
  map_one' := by ext; rfl
  map_mul' a b := by ext; rfl

中文:
定义 GroupLike.toUnits
  签名: : GroupLike R A ->* Aˣ where
  定义体: {
    val := a
    inv := antipode R a
    val_inv := a.2.mul_antipode_cancel
    inv_val := a.2.antipode_mul_cancel
  }
  map_one' := by ext; rfl
  map_mul' a b := by ext; rfl
-/
def GroupLike.toUnits : GroupLike R A ->* Aˣ where
  toFun a := {
    val := a
    inv := antipode R a
    val_inv := a.2.mul_antipode_cancel
    inv_val := a.2.antipode_mul_cancel
  }
  map_one' := by ext; rfl
  map_mul' a b := by ext; rfl

/--
lemma `IsGroupLikeElem.isUnit` / 引理 `IsGroupLikeElem.isUnit`

English:
lemma IsGroupLikeElem.isUnit
  given: (ha : IsGroupLikeElem R a)
  statement: IsUnit a
  proof: (GroupLike.toUnits R ⟨a, ha⟩).isUnit

中文:
引理 IsGroupLikeElem.isUnit
  条件: (ha : IsGroupLikeElem R a)
  结论: IsUnit a
  证明: (GroupLike.toUnits R ⟨a, ha⟩).isUnit

Depends on / 依赖: GroupLike, GroupLike.toUnits, isUnit, toUnits
-/
lemma IsGroupLikeElem.isUnit (ha : IsGroupLikeElem R a) : IsUnit a :=
  (GroupLike.toUnits R ⟨a, ha⟩).isUnit

/--
lemma `IsGroupLikeElem.antipode` / 引理 `IsGroupLikeElem.antipode`

English:
lemma IsGroupLikeElem.antipode
  given: (ha : IsGroupLikeElem R a)
  proof: ha.of_mul_eq_one ha.mul_antipode_cancel ha.antipode_mul_cancel

中文:
引理 IsGroupLikeElem.antipode
  条件: (ha : IsGroupLikeElem R a)
  证明: ha.of_mul_eq_one ha.mul_antipode_cancel ha.antipode_mul_cancel
-/
@[simp] protected lemma IsGroupLikeElem.antipode (ha : IsGroupLikeElem R a) :
    IsGroupLikeElem R (antipode R a) :=
  ha.of_mul_eq_one ha.mul_antipode_cancel ha.antipode_mul_cancel

/--
lemma `IsGroupLikeElem.antipode_antipode` / 引理 `IsGroupLikeElem.antipode_antipode`

English:
lemma IsGroupLikeElem.antipode_antipode
  given: (ha : IsGroupLikeElem R a)
  proof: left_inv_eq_right_inv ha.antipode.antipode_mul_cancel ha.antipode_mul_cancel

中文:
引理 IsGroupLikeElem.antipode_antipode
  条件: (ha : IsGroupLikeElem R a)
  证明: left_inv_eq_right_inv ha.antipode.antipode_mul_cancel ha.antipode_mul_cancel
-/
@[simp] lemma IsGroupLikeElem.antipode_antipode (ha : IsGroupLikeElem R a) :
    antipode R (antipode R a) = a :=
  left_inv_eq_right_inv ha.antipode.antipode_mul_cancel ha.antipode_mul_cancel

namespace GroupLike

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (GroupLike R A)
  body: ⟨antipode R a, a.2.antipode⟩

中文:
实例 :
  签名: Inv (GroupLike R A)
  定义体: ⟨antipode R a, a.2.antipode⟩

Depends on / 依赖: antipode
-/
instance : Inv (GroupLike R A) where inv a := ⟨antipode R a, a.2.antipode⟩

/--
lemma `val_inv` / 引理 `val_inv`

English:
lemma val_inv
  given: (a : GroupLike R A)
  statement: ↑(a⁻¹) = (antipode R a : A)
  proof: rfl

中文:
引理 val_inv
  条件: (a : GroupLike R A)
  结论: ↑(a⁻¹) = (antipode R a : A)
  证明: rfl
-/
@[simp] lemma val_inv (a : GroupLike R A) : ↑(a⁻¹) = (antipode R a : A) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (GroupLike R A)
  body: by ext; simp

中文:
实例 :
  签名: Group (GroupLike R A)
  定义体: by ext; simp
-/
instance : Group (GroupLike R A) where
  inv_mul_cancel a := by ext; simp

end GroupLike
end Semiring

variable [CommSemiring R] [CommSemiring A] [HopfAlgebra R A] {a b : A}

/--
Instance `GroupLike.instCommGroup` / 实例 `GroupLike.instCommGroup`

English:
instance GroupLike.instCommGroup
  signature: : CommGroup (GroupLike R A) where
  body: instCommMonoid
  __ := instGroup

中文:
实例 GroupLike.instCommGroup
  签名: : CommGroup (GroupLike R A) where
  定义体: instCommMonoid
  __ := instGroup

Depends on / 依赖: instCommMonoid
-/
instance GroupLike.instCommGroup : CommGroup (GroupLike R A) where
  __ := instCommMonoid
  __ := instGroup
