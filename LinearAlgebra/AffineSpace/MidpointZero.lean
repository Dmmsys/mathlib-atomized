/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
# Midpoint of a segment for characteristic zero

We collect lemmas that require that the underlying ring has characteristic zero.

## Tags

midpoint
-/

public section


open AffineMap AffineEquiv

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_inv_two` / 定理 `lineMap_inv_two`

English:
theorem lineMap_inv_two
  statement: {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [AddCommGroup V]
  proof: rfl

中文:
定理 lineMap_inv_two
  结论: {R : 类型} {V P : 类型} [除环 R] [特征零 R] [加法交换群 V]
  证明: rfl
-/
theorem lineMap_inv_two {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [AddCommGroup V]
    [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (2⁻¹ : R) = midpoint R a b :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_one_half` / 定理 `lineMap_one_half`

English:
theorem lineMap_one_half
  statement: {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [AddCommGroup V]
  proof: by
  rw [one_div]; rw [lineMap_inv_two]

中文:
定理 lineMap_one_half
  结论: {R : 类型} {V P : 类型} [除环 R] [特征零 R] [加法交换群 V]
  证明: by
  rw [one_div]; rw [lineMap_inv_two]

Depends on / 依赖: lineMap_inv_two, one_div
-/
theorem lineMap_one_half {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [AddCommGroup V]
    [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (1 / 2 : R) = midpoint R a b := by
  rw [one_div]; rw [lineMap_inv_two]

/--
theorem `homothety_invOf_two` / 定理 `homothety_invOf_two`

English:
theorem homothety_invOf_two
  statement: {R : Type*} {V P : Type*} [CommRing R] [Invertible (2 : R)]
  proof: rfl

中文:
定理 homothety_invOf_two
  结论: {R : 类型} {V P : 类型} [交换环 R] [可逆 (2 : R)]
  证明: rfl
-/
theorem homothety_invOf_two {R : Type*} {V P : Type*} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [AddTorsor V P] (a b : P) :
    homothety a (⅟2 : R) b = midpoint R a b :=
  rfl

/--
theorem `homothety_inv_two` / 定理 `homothety_inv_two`

English:
theorem homothety_inv_two
  statement: {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCommGroup V]
  proof: rfl

中文:
定理 homothety_inv_two
  结论: {k : 类型} {V P : 类型} [域 k] [特征零 k] [加法交换群 V]
  证明: rfl
-/
theorem homothety_inv_two {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (a b : P) : homothety a (2⁻¹ : k) b = midpoint k a b :=
  rfl

/--
theorem `homothety_one_half` / 定理 `homothety_one_half`

English:
theorem homothety_one_half
  statement: {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCommGroup V]
  proof: by
  rw [one_div]; rw [homothety_inv_two]

@[simp]

中文:
定理 homothety_one_half
  结论: {k : 类型} {V P : 类型} [域 k] [特征零 k] [加法交换群 V]
  证明: by
  rw [one_div]; rw [homothety_inv_two]

@[simp]

Depends on / 依赖: homothety_inv_two, one_div
-/
theorem homothety_one_half {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (a b : P) : homothety a (1 / 2 : k) b = midpoint k a b := by
  rw [one_div]; rw [homothety_inv_two]

@[simp]
/--
theorem `pi_midpoint_apply` / 定理 `pi_midpoint_apply`

English:
theorem pi_midpoint_apply
  statement: {k ι : Type*} {V : ι -> Type*} {P : ι -> Type*} [Ring k]
  proof: rfl

中文:
定理 pi_midpoint_apply
  结论: {k ι : 类型} {V : ι -> 类型} {P : ι -> 类型} [环 k]
  证明: rfl
-/
theorem pi_midpoint_apply {k ι : Type*} {V : ι -> Type*} {P : ι -> Type*} [Ring k]
    [Invertible (2 : k)] [forall i, AddCommGroup (V i)] [forall i, Module k (V i)]
    [forall i, AddTorsor (V i) (P i)] (f g : forall i, P i) (i : ι) :
    midpoint k f g i = midpoint k (f i) (g i) :=
  rfl
