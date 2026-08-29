/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Lattice.Nat

/-!
# Definition of nilpotent elements

This file proves basic facts about nilpotent elements.
For results that require further theory, see `Mathlib/RingTheory/Nilpotent/Basic.lean`
and `Mathlib/RingTheory/Nilpotent/Lemmas.lean`.

## Main definitions

  * `Commute.isNilpotent_mul_left`
  * `Commute.isNilpotent_mul_right`
  * `nilpotencyClass`

-/

@[expose] public section

open Set

variable {R S : Type*} {x y : R}

/--
theorem `IsNilpotent.map` / 定理 `IsNilpotent.map`

English:
theorem IsNilpotent.map
  statement: [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
  proof: by
  use hr.choose
  rw [← map_pow]; rw [hr.choose_spec]; rw [map_zero]

中文:
定理 IsNilpotent.map
  结论: [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : 类型}
  证明: by
  use hr.choose
  rw [← map_pow]; rw [hr.choose_spec]; rw [map_zero]

Depends on / 依赖: choose_spec, hr.choose, hr.choose_spec, map_pow, map_zero
-/
theorem IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpotent r) (f : F) :
    IsNilpotent (f r) := by
  use hr.choose
  rw [← map_pow]; rw [hr.choose_spec]; rw [map_zero]

/--
lemma `IsNilpotent.map_iff` / 引理 `IsNilpotent.map_iff`

English:
lemma IsNilpotent.map_iff
  statement: [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
  proof: ⟨fun ⟨k, hk⟩ => ⟨k, (map_eq_zero_iff f hf).mp by rwa [map_pow]⟩, fun h => h.map f⟩

中文:
引理 IsNilpotent.map_iff
  结论: [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : 类型}
  证明: ⟨fun ⟨k, hk⟩ => ⟨k, (map_eq_zero_iff f hf).mp by rwa [map_pow]⟩, fun h => h.map f⟩

Depends on / 依赖: h.map, map_eq_zero_iff, map_pow
-/
lemma IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F} (hf : Function.Injective f) :
    IsNilpotent (f r) ↔ IsNilpotent r :=
⟨fun ⟨k, hk⟩ => ⟨k, (map_eq_zero_iff f hf).mp by rwa [map_pow]⟩, fun h => h.map f⟩

/--
theorem `IsUnit.isNilpotent_mul_unit_of_commute_iff` / 定理 `IsUnit.isNilpotent_mul_unit_of_commute_iff`

English:
theorem IsUnit.isNilpotent_mul_unit_of_commute_iff
  statement: [MonoidWithZero R] {r u : R}
  proof: exists_congr fun n => by rw [h_comm.mul_pow, (hu.pow n).mul_left_eq_zero]

中文:
定理 IsUnit.isNilpotent_mul_unit_of_commute_iff
  结论: [MonoidWithZero R] {r u : R}
  证明: exists_congr fun n => by rw [h_comm.mul_pow, (hu.pow n).mul_left_eq_zero]

Depends on / 依赖: exists_congr, h_comm, h_comm.mul_pow, hu.pow, mul_left_eq_zero, mul_pow
-/
theorem IsUnit.isNilpotent_mul_unit_of_commute_iff [MonoidWithZero R] {r u : R}
    (hu : IsUnit u) (h_comm : Commute r u) :
    IsNilpotent (r * u) ↔ IsNilpotent r :=
  exists_congr fun n => by rw [h_comm.mul_pow, (hu.pow n).mul_left_eq_zero]

/--
theorem `IsUnit.isNilpotent_unit_mul_of_commute_iff` / 定理 `IsUnit.isNilpotent_unit_mul_of_commute_iff`

English:
theorem IsUnit.isNilpotent_unit_mul_of_commute_iff
  statement: [MonoidWithZero R] {r u : R}
  proof: h_comm ▸ hu.isNilpotent_mul_unit_of_commute_iff h_comm

中文:
定理 IsUnit.isNilpotent_unit_mul_of_commute_iff
  结论: [MonoidWithZero R] {r u : R}
  证明: h_comm ▸ hu.isNilpotent_mul_unit_of_commute_iff h_comm

Depends on / 依赖: h_comm, hu.isNilpotent_mul_unit_of_commute_iff, isNilpotent_mul_unit_of_commute_iff
-/
theorem IsUnit.isNilpotent_unit_mul_of_commute_iff [MonoidWithZero R] {r u : R}
    (hu : IsUnit u) (h_comm : Commute r u) :
    IsNilpotent (u * r) ↔ IsNilpotent r :=
  h_comm ▸ hu.isNilpotent_mul_unit_of_commute_iff h_comm

section NilpotencyClass

section ZeroPow

variable [Zero R] [Pow R Nat]

variable (x) in
/--
Definition of `nilpotencyClass` / `nilpotencyClass` 的定义

English:
definition nilpotencyClass
  signature: : Nat
  body: sInf {k | x ^ k = 0}

中文:
定义 nilpotencyClass
  签名: : 自然数
  定义体: sInf {k | x ^ k = 0}
-/
noncomputable def nilpotencyClass : Nat := sInf {k | x ^ k = 0}

/--
lemma `nilpotencyClass_eq_zero_of_subsingleton` / 引理 `nilpotencyClass_eq_zero_of_subsingleton`

English:
lemma nilpotencyClass_eq_zero_of_subsingleton
  given: [Subsingleton R]
  proof: by
  let s : Set Nat := {k | x ^ k = 0}
  suffices s = univ by change sInf _ = 0; simp [s] at this; simp [this]
  exact eq_univ_iff_forall.mpr fun k => Subsingleton.elim _ _

中文:
引理 nilpotencyClass_eq_zero_of_subsingleton
  条件: [Subsingleton R]
  证明: by
  let s : Set Nat := {k | x ^ k = 0}
  suffices s = univ by change sInf _ = 0; simp [s] at this; simp [this]
  exact eq_univ_iff_forall.mpr fun k => Subsingleton.elim _ _
-/
@[simp] lemma nilpotencyClass_eq_zero_of_subsingleton [Subsingleton R] :
    nilpotencyClass x = 0 := by
  let s : Set Nat := {k | x ^ k = 0}
  suffices s = univ by change sInf _ = 0; simp [s] at this; simp [this]
  exact eq_univ_iff_forall.mpr fun k => Subsingleton.elim _ _

/--
lemma `isNilpotent_of_pos_nilpotencyClass` / 引理 `isNilpotent_of_pos_nilpotencyClass`

English:
lemma isNilpotent_of_pos_nilpotencyClass
  given: (hx : 0 < nilpotencyClass x)
  proof: by
  let s : Set Nat := {k | x ^ k = 0}
  change s.Nonempty
  change 0 < sInf s at hx
  by_contra contra
  simp [not_nonempty_iff_eq_empty.mp contra] at hx

中文:
引理 isNilpotent_of_pos_nilpotencyClass
  条件: (hx : 0 < nilpotencyClass x)
  证明: by
  let s : Set Nat := {k | x ^ k = 0}
  change s.Nonempty
  change 0 < sInf s at hx
  by_contra contra
  simp [not_nonempty_iff_eq_empty.mp contra] at hx

Depends on / 依赖: Nonempty, contra, not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty.mp, s.Nonempty
-/
lemma isNilpotent_of_pos_nilpotencyClass (hx : 0 < nilpotencyClass x) :
    IsNilpotent x := by
  let s : Set Nat := {k | x ^ k = 0}
  change s.Nonempty
  change 0 < sInf s at hx
  by_contra contra
  simp [not_nonempty_iff_eq_empty.mp contra] at hx

/--
lemma `pow_nilpotencyClass` / 引理 `pow_nilpotencyClass`

English:
lemma pow_nilpotencyClass
  given: (hx : IsNilpotent x)
  statement: x ^ (nilpotencyClass x) = 0
  proof: Nat.sInf_mem hx

中文:
引理 pow_nilpotencyClass
  条件: (hx : IsNilpotent x)
  结论: x ^ (nilpotencyClass x) = 0
  证明: Nat.sInf_mem hx

Depends on / 依赖: Nat.sInf_mem, sInf_mem
-/
lemma pow_nilpotencyClass (hx : IsNilpotent x) : x ^ (nilpotencyClass x) = 0 :=
  Nat.sInf_mem hx

end ZeroPow

section MonoidWithZero

variable [MonoidWithZero R]

/--
lemma `nilpotencyClass_eq_succ_iff` / 引理 `nilpotencyClass_eq_succ_iff`

English:
lemma nilpotencyClass_eq_succ_iff
  given: {k : Nat}
  proof: by
  let s : Set Nat := {k | x ^ k = 0}
  have : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s := fun k₁ k₂ h_le hk₁ => pow_eq_zero_of_le h_le hk₁
  simp [s, nilpotencyClass, Nat.sInf_upward_closed_eq_succ_iff this]

中文:
引理 nilpotencyClass_eq_succ_iff
  条件: {k : 自然数}
  证明: by
  let s : Set Nat := {k | x ^ k = 0}
  have : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s := fun k₁ k₂ h_le hk₁ => pow_eq_zero_of_le h_le hk₁
  simp [s, nilpotencyClass, Nat.sInf_upward_closed_eq_succ_iff this]

Depends on / 依赖: Nat.sInf_upward_closed_eq_succ_iff, h_le, nilpotencyClass, pow_eq_zero_of_le, sInf_upward_closed_eq_succ_iff
-/
lemma nilpotencyClass_eq_succ_iff {k : Nat} :
    nilpotencyClass x = k + 1 ↔ x ^ (k + 1) = 0 ∧ x ^ k != 0 := by
  let s : Set Nat := {k | x ^ k = 0}
  have : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s := fun k₁ k₂ h_le hk₁ => pow_eq_zero_of_le h_le hk₁
  simp [s, nilpotencyClass, Nat.sInf_upward_closed_eq_succ_iff this]

/--
lemma `nilpotencyClass_zero` / 引理 `nilpotencyClass_zero`

English:
lemma nilpotencyClass_zero
  given: [Nontrivial R]
  proof: nilpotencyClass_eq_succ_iff.mpr by constructor <;> simp

中文:
引理 nilpotencyClass_zero
  条件: [Nontrivial R]
  证明: nilpotencyClass_eq_succ_iff.mpr by constructor <;> simp
-/
@[simp] lemma nilpotencyClass_zero [Nontrivial R] :
    nilpotencyClass (0 : R) = 1 :=
nilpotencyClass_eq_succ_iff.mpr by constructor <;> simp

/--
lemma `pos_nilpotencyClass_iff` / 引理 `pos_nilpotencyClass_iff`

English:
lemma pos_nilpotencyClass_iff
  given: [Nontrivial R]
  proof: by
  refine ⟨isNilpotent_of_pos_nilpotencyClass, fun hx => Nat.pos_of_ne_zero fun hx' => ?_⟩
  replace hx := pow_nilpotencyClass hx
  rw [hx']; rw [pow_zero] at hx
  exact one_ne_zero hx

中文:
引理 pos_nilpotencyClass_iff
  条件: [Nontrivial R]
  证明: by
  refine ⟨isNilpotent_of_pos_nilpotencyClass, fun hx => Nat.pos_of_ne_zero fun hx' => ?_⟩
  replace hx := pow_nilpotencyClass hx
  rw [hx']; rw [pow_zero] at hx
  exact one_ne_zero hx
-/
@[simp] lemma pos_nilpotencyClass_iff [Nontrivial R] :
    0 < nilpotencyClass x ↔ IsNilpotent x := by
  refine ⟨isNilpotent_of_pos_nilpotencyClass, fun hx => Nat.pos_of_ne_zero fun hx' => ?_⟩
  replace hx := pow_nilpotencyClass hx
  rw [hx']; rw [pow_zero] at hx
  exact one_ne_zero hx

/--
lemma `pow_pred_nilpotencyClass` / 引理 `pow_pred_nilpotencyClass`

English:
lemma pow_pred_nilpotencyClass
  given: [Nontrivial R] (hx : IsNilpotent x)
  proof: (nilpotencyClass_eq_succ_iff.mp <| Nat.eq_add_of_sub_eq (pos_nilpotencyClass_iff.mpr hx) rfl).2

中文:
引理 pow_pred_nilpotencyClass
  条件: [Nontrivial R] (hx : IsNilpotent x)
  证明: (nilpotencyClass_eq_succ_iff.mp <| Nat.eq_add_of_sub_eq (pos_nilpotencyClass_iff.mpr hx) rfl).2

Depends on / 依赖: Nat.eq_add_of_sub_eq, eq_add_of_sub_eq, nilpotencyClass_eq_succ_iff, nilpotencyClass_eq_succ_iff.mp, pos_nilpotencyClass_iff, pos_nilpotencyClass_iff.mpr
-/
lemma pow_pred_nilpotencyClass [Nontrivial R] (hx : IsNilpotent x) :
    x ^ (nilpotencyClass x - 1) != 0 :=
  (nilpotencyClass_eq_succ_iff.mp <| Nat.eq_add_of_sub_eq (pos_nilpotencyClass_iff.mpr hx) rfl).2

/--
lemma `eq_zero_of_nilpotencyClass_eq_one` / 引理 `eq_zero_of_nilpotencyClass_eq_one`

English:
lemma eq_zero_of_nilpotencyClass_eq_one
  given: (hx : nilpotencyClass x = 1)
  proof: by
  have : IsNilpotent x := isNilpotent_of_pos_nilpotencyClass (hx ▸ Nat.one_pos)
  rw [← pow_nilpotencyClass this]; rw [hx]; rw [pow_one]

中文:
引理 eq_zero_of_nilpotencyClass_eq_one
  条件: (hx : nilpotencyClass x = 1)
  证明: by
  have : IsNilpotent x := isNilpotent_of_pos_nilpotencyClass (hx ▸ Nat.one_pos)
  rw [← pow_nilpotencyClass this]; rw [hx]; rw [pow_one]

Depends on / 依赖: IsNilpotent, Nat.one_pos, isNilpotent_of_pos_nilpotencyClass, one_pos, pow_nilpotencyClass, pow_one
-/
lemma eq_zero_of_nilpotencyClass_eq_one (hx : nilpotencyClass x = 1) :
    x = 0 := by
  have : IsNilpotent x := isNilpotent_of_pos_nilpotencyClass (hx ▸ Nat.one_pos)
  rw [← pow_nilpotencyClass this]; rw [hx]; rw [pow_one]

/--
lemma `nilpotencyClass_eq_one` / 引理 `nilpotencyClass_eq_one`

English:
lemma nilpotencyClass_eq_one
  given: [Nontrivial R]
  proof: ⟨eq_zero_of_nilpotencyClass_eq_one, fun hx => hx ▸ nilpotencyClass_zero⟩

中文:
引理 nilpotencyClass_eq_one
  条件: [Nontrivial R]
  证明: ⟨eq_zero_of_nilpotencyClass_eq_one, fun hx => hx ▸ nilpotencyClass_zero⟩
-/
@[simp] lemma nilpotencyClass_eq_one [Nontrivial R] :
    nilpotencyClass x = 1 ↔ x = 0 :=
  ⟨eq_zero_of_nilpotencyClass_eq_one, fun hx => hx ▸ nilpotencyClass_zero⟩

end MonoidWithZero

end NilpotencyClass

/--
theorem `isReduced_of_injective` / 定理 `isReduced_of_injective`

English:
theorem isReduced_of_injective
  statement: [MonoidWithZero R] [MonoidWithZero S] {F : Type*}
  proof: by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  exact (hx.map f).eq_zero

中文:
定理 isReduced_of_injective
  结论: [MonoidWithZero R] [MonoidWithZero S] {F : 类型}
  证明: by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  exact (hx.map f).eq_zero

Depends on / 依赖: IsComplete, IsComplete.completeSpace_coe, c.isComplete, completeSpace_coe, eq_zero, hx.map, isComplete, map_zero
-/
theorem isReduced_of_injective [MonoidWithZero R] [MonoidWithZero S] {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S]
    (f : F) (hf : Function.Injective f) [IsReduced S] :
    IsReduced R := by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  exact (hx.map f).eq_zero

instance (ι) (R : ι -> Type*) [forall i, Zero (R i)] [forall i, Pow (R i) Nat]
    [forall i, IsReduced (R i)] : IsReduced (forall i, R i) where
  eq_zero _ := fun ⟨n, hn⟩ => funext fun i => IsReduced.eq_zero _ ⟨n, congr_fun hn i⟩

/--
Definition of `IsRadical` / `IsRadical` 的定义

English:
definition IsRadical
  signature: [Dvd R] [Pow R Nat] (y : R)
  body: forall (n : Nat) (x), y ∣ x ^ n -> y ∣ x

中文:
定义 IsRadical
  签名: [Dvd R] [Pow R 自然数] (y : R)
  定义体: forall (n : Nat) (x), y ∣ x ^ n -> y ∣ x
-/
def IsRadical [Dvd R] [Pow R Nat] (y : R) : Prop :=
  forall (n : Nat) (x), y ∣ x ^ n -> y ∣ x

/--
theorem `isRadical_iff_pow_one_lt` / 定理 `isRadical_iff_pow_one_lt`

English:
theorem isRadical_iff_pow_one_lt
  given: [Monoid R] (k : Nat) (hk : 1 < k)
  proof: ⟨(· k), k.pow_imp_self_of_one_lt hk _ fun _ _ h => .inl (dvd_mul_of_dvd_left h _)⟩

中文:
定理 isRadical_iff_pow_one_lt
  条件: [Monoid R] (k : 自然数) (hk : 1 < k)
  证明: ⟨(· k), k.pow_imp_self_of_one_lt hk _ fun _ _ h => .inl (dvd_mul_of_dvd_left h _)⟩

Depends on / 依赖: dvd_mul_of_dvd_left, k.pow_imp_self_of_one_lt, pow_imp_self_of_one_lt
-/
theorem isRadical_iff_pow_one_lt [Monoid R] (k : Nat) (hk : 1 < k) :
    IsRadical y ↔ forall x, y ∣ x ^ k -> y ∣ x :=
  ⟨(· k), k.pow_imp_self_of_one_lt hk _ fun _ _ h => .inl (dvd_mul_of_dvd_left h _)⟩

namespace Commute

section Semiring

variable [Semiring R]

/--
theorem `isNilpotent_mul_right` / 定理 `isNilpotent_mul_right`

English:
theorem isNilpotent_mul_right
  given: (h_comm : Commute x y) (h : IsNilpotent x)
  statement: IsNilpotent (x * y)
  proof: by
  obtain ⟨n, hn⟩ := h
  use n
  rw [h_comm.mul_pow]; rw [hn]; rw [zero_mul]

中文:
定理 isNilpotent_mul_right
  条件: (h_comm : Commute x y) (h : IsNilpotent x)
  结论: IsNilpotent (x * y)
  证明: by
  obtain ⟨n, hn⟩ := h
  use n
  rw [h_comm.mul_pow]; rw [hn]; rw [zero_mul]

Depends on / 依赖: h_comm, h_comm.mul_pow, mul_pow, zero_mul
-/
theorem isNilpotent_mul_right (h_comm : Commute x y) (h : IsNilpotent x) : IsNilpotent (x * y) := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [h_comm.mul_pow]; rw [hn]; rw [zero_mul]

/--
theorem `isNilpotent_mul_left` / 定理 `isNilpotent_mul_left`

English:
theorem isNilpotent_mul_left
  given: (h_comm : Commute x y) (h : IsNilpotent y)
  statement: IsNilpotent (x * y)
  proof: by
  rw [h_comm.eq]
  exact h_comm.symm.isNilpotent_mul_right h

中文:
定理 isNilpotent_mul_left
  条件: (h_comm : Commute x y) (h : IsNilpotent y)
  结论: IsNilpotent (x * y)
  证明: by
  rw [h_comm.eq]
  exact h_comm.symm.isNilpotent_mul_right h

Depends on / 依赖: h_comm, h_comm.eq, h_comm.symm.isNilpotent_mul_right, isNilpotent_mul_right
-/
theorem isNilpotent_mul_left (h_comm : Commute x y) (h : IsNilpotent y) : IsNilpotent (x * y) := by
  rw [h_comm.eq]
  exact h_comm.symm.isNilpotent_mul_right h

end Semiring

end Commute
