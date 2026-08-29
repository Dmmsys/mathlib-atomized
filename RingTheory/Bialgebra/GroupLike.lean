/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Group-like elements in a bialgebra

This file proves that group-like elements in a bialgebra form a monoid.
-/

@[expose] public section

open Coalgebra Bialgebra

variable {R A : Type*}

section Semiring
variable [CommSemiring R] [Semiring A] [Bialgebra R A] {a b : A}

/--
lemma `IsGroupLikeElem.one` / 引理 `IsGroupLikeElem.one`

English:
lemma IsGroupLikeElem.one
  statement: IsGroupLikeElem R (1 : A) where
  proof: counit_one
  comul_eq_tmul_self := comul_one

中文:
引理 IsGroupLikeElem.one
  结论: IsGroupLikeElem R (1 : A) where
  证明: counit_one
  comul_eq_tmul_self := comul_one

Depends on / 依赖: counit_one
-/
lemma IsGroupLikeElem.one : IsGroupLikeElem R (1 : A) where
  counit_eq_one := counit_one
  comul_eq_tmul_self := comul_one

/--
lemma `IsGroupLikeElem.mul` / 引理 `IsGroupLikeElem.mul`

English:
lemma IsGroupLikeElem.mul
  given: (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b)
  proof: by simp [ha, hb]
  comul_eq_tmul_self := by simp [ha, hb]

中文:
引理 IsGroupLikeElem.mul
  条件: (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b)
  证明: by simp [ha, hb]
  comul_eq_tmul_self := by simp [ha, hb]

Depends on / 依赖: comul_eq_tmul_self
-/
lemma IsGroupLikeElem.mul (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b) :
    IsGroupLikeElem R (a * b) where
  counit_eq_one := by simp [ha, hb]
  comul_eq_tmul_self := by simp [ha, hb]

variable (R A) in
/--
Definition of `groupLikeSubmonoid` / `groupLikeSubmonoid` 的定义

English:
definition groupLikeSubmonoid
  signature: : Submonoid A where
  body: {a | IsGroupLikeElem R a}
  one_mem' := .one
  mul_mem' := .mul

中文:
定义 groupLikeSubmonoid
  签名: : Submonoid A where
  定义体: {a | IsGroupLikeElem R a}
  one_mem' := .one
  mul_mem' := .mul

Depends on / 依赖: IsGroupLikeElem
-/
def groupLikeSubmonoid : Submonoid A where
  carrier := {a | IsGroupLikeElem R a}
  one_mem' := .one
  mul_mem' := .mul

/--
lemma `IsGroupLikeElem.pow` / 引理 `IsGroupLikeElem.pow`

English:
lemma IsGroupLikeElem.pow
  given: {n : Nat} (ha : IsGroupLikeElem R a)
  statement: IsGroupLikeElem R (a ^ n)
  proof: (groupLikeSubmonoid R A).pow_mem ha _

中文:
引理 IsGroupLikeElem.pow
  条件: {n : 自然数} (ha : IsGroupLikeElem R a)
  结论: IsGroupLikeElem R (a ^ n)
  证明: (groupLikeSubmonoid R A).pow_mem ha _

Depends on / 依赖: groupLikeSubmonoid, pow_mem
-/
lemma IsGroupLikeElem.pow {n : Nat} (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (a ^ n) :=
  (groupLikeSubmonoid R A).pow_mem ha _

/--
lemma `IsGroupLikeElem.of_mul_eq_one` / 引理 `IsGroupLikeElem.of_mul_eq_one`

English:
lemma IsGroupLikeElem.of_mul_eq_one
  given: (hab : a * b = 1) (hba : b * a = 1) (ha : IsGroupLikeElem R a)
  proof: left_inv_eq_right_inv (a := counit a) (by simp [← counit_mul, hba]) (by simp [ha])
  comul_eq_tmul_self := left_inv_eq_right_inv (a := comul a) (by simp [← comul_mul, hba])
    (by simp [ha, hab, Algebra.TensorProduct.one_def])

中文:
引理 IsGroupLikeElem.of_mul_eq_one
  条件: (hab : a * b = 1) (hba : b * a = 1) (ha : IsGroupLikeElem R a)
  证明: left_inv_eq_right_inv (a := counit a) (by simp [← counit_mul, hba]) (by simp [ha])
  comul_eq_tmul_self := left_inv_eq_right_inv (a := comul a) (by simp [← comul_mul, hba])
    (by simp [ha, hab, Algebra.TensorProduct.one_def])

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, TensorProduct, comul_eq_tmul_self, comul_mul, counit, counit_mul, left_inv_eq_right_inv, one_def
-/
lemma IsGroupLikeElem.of_mul_eq_one (hab : a * b = 1) (hba : b * a = 1) (ha : IsGroupLikeElem R a) :
    IsGroupLikeElem R b where
  counit_eq_one :=
    left_inv_eq_right_inv (a := counit a) (by simp [← counit_mul, hba]) (by simp [ha])
  comul_eq_tmul_self := left_inv_eq_right_inv (a := comul a) (by simp [← comul_mul, hba])
    (by simp [ha, hab, Algebra.TensorProduct.one_def])

/--
lemma `isGroupLikeElem_iff_of_mul_eq_one` / 引理 `isGroupLikeElem_iff_of_mul_eq_one`

English:
lemma isGroupLikeElem_iff_of_mul_eq_one
  given: (hab : a * b = 1) (hba : b * a = 1)
  proof: ⟨.of_mul_eq_one hab hba, .of_mul_eq_one hba hab⟩

中文:
引理 isGroupLikeElem_iff_of_mul_eq_one
  条件: (hab : a * b = 1) (hba : b * a = 1)
  证明: ⟨.of_mul_eq_one hab hba, .of_mul_eq_one hba hab⟩

Depends on / 依赖: of_mul_eq_one
-/
lemma isGroupLikeElem_iff_of_mul_eq_one (hab : a * b = 1) (hba : b * a = 1) :
    IsGroupLikeElem R a ↔ IsGroupLikeElem R b := ⟨.of_mul_eq_one hab hba, .of_mul_eq_one hba hab⟩

/--
lemma `isGroupLikeElem_unitsInv` / 引理 `isGroupLikeElem_unitsInv`

English:
lemma isGroupLikeElem_unitsInv
  given: {u : Aˣ}
  proof: isGroupLikeElem_iff_of_mul_eq_one (by simp) (by simp)

alias ⟨IsGroupLikeElem.of_unitsInv, IsGroupLikeElem.unitsInv⟩ := isGroupLikeElem_unitsInv

中文:
引理 isGroupLikeElem_unitsInv
  条件: {u : Aˣ}
  证明: isGroupLikeElem_iff_of_mul_eq_one (by simp) (by simp)

alias ⟨IsGroupLikeElem.of_unitsInv, IsGroupLikeElem.unitsInv⟩ := isGroupLikeElem_unitsInv
-/
@[simp] lemma isGroupLikeElem_unitsInv {u : Aˣ} :
    IsGroupLikeElem R u⁻¹.val ↔ IsGroupLikeElem R u.val :=
  isGroupLikeElem_iff_of_mul_eq_one (by simp) (by simp)

alias ⟨IsGroupLikeElem.of_unitsInv, IsGroupLikeElem.unitsInv⟩ := isGroupLikeElem_unitsInv

namespace GroupLike

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (GroupLike R A)
  body: ⟨1, .one⟩

中文:
实例 :
  签名: One (GroupLike R A)
  定义体: ⟨1, .one⟩
-/
instance : One (GroupLike R A) where one := ⟨1, .one⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (GroupLike R A)
  body: ⟨a * b, a.2.mul b.2⟩

中文:
实例 :
  签名: Mul (GroupLike R A)
  定义体: ⟨a * b, a.2.mul b.2⟩
-/
instance : Mul (GroupLike R A) where mul a b := ⟨a * b, a.2.mul b.2⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (GroupLike R A) Nat
  body: ⟨a ^ n, a.2.pow⟩

中文:
实例 :
  签名: Pow (GroupLike R A) 自然数
  定义体: ⟨a ^ n, a.2.pow⟩
-/
instance : Pow (GroupLike R A) Nat where pow a n := ⟨a ^ n, a.2.pow⟩

/--
lemma `val_one` / 引理 `val_one`

English:
lemma val_one
  statement: (1 : GroupLike R A) = (1 : A)
  proof: rfl

中文:
引理 val_one
  结论: (1 : GroupLike R A) = (1 : A)
  证明: rfl
-/
@[simp] lemma val_one : (1 : GroupLike R A) = (1 : A) := rfl
/--
lemma `val_mul` / 引理 `val_mul`

English:
lemma val_mul
  given: (a b : GroupLike R A)
  statement: ↑(a * b) = (a * b : A)
  proof: rfl

中文:
引理 val_mul
  条件: (a b : GroupLike R A)
  结论: ↑(a * b) = (a * b : A)
  证明: rfl
-/
@[simp] lemma val_mul (a b : GroupLike R A) : ↑(a * b) = (a * b : A) := rfl
/--
lemma `val_pow` / 引理 `val_pow`

English:
lemma val_pow
  given: (a : GroupLike R A) (n : Nat)
  statement: ↑(a ^ n) = (a ^ n : A)
  proof: rfl

中文:
引理 val_pow
  条件: (a : GroupLike R A) (n : 自然数)
  结论: ↑(a ^ n) = (a ^ n : A)
  证明: rfl
-/
@[simp] lemma val_pow (a : GroupLike R A) (n : Nat) : ↑(a ^ n) = (a ^ n : A) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (GroupLike R A)
  body: val_injective.monoid val val_one val_mul val_pow

中文:
实例 :
  签名: Monoid (GroupLike R A)
  定义体: val_injective.monoid val val_one val_mul val_pow

Depends on / 依赖: monoid, val_injective, val_injective.monoid, val_mul, val_one, val_pow
-/
instance : Monoid (GroupLike R A) := val_injective.monoid val val_one val_mul val_pow

variable (R A) in
/--
Definition of `valMonoidHom` / `valMonoidHom` 的定义

English:
definition valMonoidHom
  signature: : GroupLike R A ->* A where
  body: val
  map_one' := val_one
  map_mul' := val_mul

中文:
定义 valMonoidHom
  签名: : GroupLike R A ->* A where
  定义体: val
  map_one' := val_one
  map_mul' := val_mul
-/
@[simps] def valMonoidHom : GroupLike R A ->* A where
  toFun := val
  map_one' := val_one
  map_mul' := val_mul

end GroupLike
end Semiring

variable [CommSemiring R] [CommSemiring A] [Bialgebra R A] {a b : A}

/--
Instance `GroupLike.instCommMonoid` / 实例 `GroupLike.instCommMonoid`

English:
instance GroupLike.instCommMonoid
  signature: : CommMonoid (GroupLike R A)
  body: val_injective.commMonoid val val_one val_mul val_pow

中文:
实例 GroupLike.instCommMonoid
  签名: : CommMonoid (GroupLike R A)
  定义体: val_injective.commMonoid val val_one val_mul val_pow

Depends on / 依赖: commMonoid, val_injective, val_injective.commMonoid, val_mul, val_one, val_pow
-/
instance GroupLike.instCommMonoid : CommMonoid (GroupLike R A) :=
  val_injective.commMonoid val val_one val_mul val_pow
