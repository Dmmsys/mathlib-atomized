/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Cycles of a permutation

This file starts the theory of cycles in permutations.

## Main definitions

In the following, `f : Equiv.Perm β`.

* `Equiv.Perm.SameCycle`: `f.SameCycle x y` when `x` and `y` are in the same cycle of `f`.
* `Equiv.Perm.IsCycle`: `f` is a cycle if any two nonfixed points of `f` are related by repeated
  applications of `f`, and `f` is not the identity.
* `Equiv.Perm.IsCycleOn`: `f` is a cycle on a set `s` when any two points of `s` are related by
  repeated applications of `f`.

## Notes

`Equiv.Perm.IsCycle` and `Equiv.Perm.IsCycleOn` are different in three ways:
* `IsCycle` is about the entire type while `IsCycleOn` is restricted to a set.
* `IsCycle` forbids the identity while `IsCycleOn` allows it (if `s` is a subsingleton).
* `IsCycleOn` forbids fixed points on `s` (if `s` is nontrivial), while `IsCycle` allows them.
-/

@[expose] public section


open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

/-! ### `SameCycle` -/

section SameCycle

variable {f g : Perm α} {p : α -> Prop} {x y z : α}

/--
Definition of `SameCycle` / `SameCycle` 的定义

English:
definition SameCycle
  signature: (f : Perm α) (x y : α)
  body: exists i : Int, (f ^ i) x = y

@[refl]

中文:
定义 SameCycle
  签名: (f : 置换 α) (x y : α)
  定义体: exists i : Int, (f ^ i) x = y

@[refl]
-/
def SameCycle (f : Perm α) (x y : α) : Prop :=
  exists i : Int, (f ^ i) x = y

@[refl]
/--
theorem `SameCycle.refl` / 定理 `SameCycle.refl`

English:
theorem SameCycle.refl
  given: (f : Perm α) (x : α)
  statement: SameCycle f x x
  proof: ⟨0, rfl⟩

中文:
定理 SameCycle.refl
  条件: (f : 置换 α) (x : α)
  结论: SameCycle f x x
  证明: ⟨0, rfl⟩
-/
theorem SameCycle.refl (f : Perm α) (x : α) : SameCycle f x x :=
  ⟨0, rfl⟩

/--
theorem `SameCycle.rfl` / 定理 `SameCycle.rfl`

English:
theorem SameCycle.rfl
  statement: SameCycle f x x
  proof: SameCycle.refl _ _

中文:
定理 SameCycle.rfl
  结论: SameCycle f x x
  证明: SameCycle.refl _ _

Depends on / 依赖: SameCycle, SameCycle.refl
-/
theorem SameCycle.rfl : SameCycle f x x :=
  SameCycle.refl _ _

/--
theorem `_root_.Eq.sameCycle` / 定理 `_root_.Eq.sameCycle`

English:
theorem _root_.Eq.sameCycle
  given: (h : x = y) (f : Perm α)
  statement: f.SameCycle x y
  proof: by rw [h]

@[symm]

中文:
定理 _root_.相等.sameCycle
  条件: (h : x = y) (f : 置换 α)
  结论: f.SameCycle x y
  证明: by rw [h]

@[symm]
-/
protected theorem _root_.Eq.sameCycle (h : x = y) (f : Perm α) : f.SameCycle x y := by rw [h]

@[symm]
/--
theorem `SameCycle.symm` / 定理 `SameCycle.symm`

English:
theorem SameCycle.symm
  statement: SameCycle f x y -> SameCycle f y x
  proof: fun ⟨i, hi⟩ =>
  ⟨-i, by simp [zpow_neg, ← hi]⟩

中文:
定理 SameCycle.symm
  结论: SameCycle f x y -> SameCycle f y x
  证明: fun ⟨i, hi⟩ =>
  ⟨-i, by simp [zpow_neg, ← hi]⟩
-/
theorem SameCycle.symm : SameCycle f x y -> SameCycle f y x := fun ⟨i, hi⟩ =>
  ⟨-i, by simp [zpow_neg, ← hi]⟩

/--
theorem `sameCycle_comm` / 定理 `sameCycle_comm`

English:
theorem sameCycle_comm
  statement: SameCycle f x y ↔ SameCycle f y x
  proof: ⟨SameCycle.symm, SameCycle.symm⟩

@[trans]

中文:
定理 sameCycle_comm
  结论: SameCycle f x y ↔ SameCycle f y x
  证明: ⟨SameCycle.symm, SameCycle.symm⟩

@[trans]

Depends on / 依赖: SameCycle, SameCycle.symm
-/
theorem sameCycle_comm : SameCycle f x y ↔ SameCycle f y x :=
  ⟨SameCycle.symm, SameCycle.symm⟩

@[trans]
/--
theorem `SameCycle.trans` / 定理 `SameCycle.trans`

English:
theorem SameCycle.trans
  statement: SameCycle f x y -> SameCycle f y z -> SameCycle f x z
  proof: fun ⟨i, hi⟩ ⟨j, hj⟩ => ⟨j + i, by rw [zpow_add, mul_apply, hi, hj]⟩

中文:
定理 SameCycle.trans
  结论: SameCycle f x y -> SameCycle f y z -> SameCycle f x z
  证明: fun ⟨i, hi⟩ ⟨j, hj⟩ => ⟨j + i, by rw [zpow_add, mul_apply, hi, hj]⟩

Depends on / 依赖: mul_apply, zpow_add
-/
theorem SameCycle.trans : SameCycle f x y -> SameCycle f y z -> SameCycle f x z :=
  fun ⟨i, hi⟩ ⟨j, hj⟩ => ⟨j + i, by rw [zpow_add, mul_apply, hi, hj]⟩

variable (f) in
/--
theorem `SameCycle.equivalence` / 定理 `SameCycle.equivalence`

English:
theorem SameCycle.equivalence
  statement: Equivalence (SameCycle f)
  proof: ⟨SameCycle.refl f, SameCycle.symm, SameCycle.trans⟩

中文:
定理 SameCycle.equivalence
  结论: 等价 (SameCycle f)
  证明: ⟨SameCycle.refl f, SameCycle.symm, SameCycle.trans⟩

Depends on / 依赖: SameCycle, SameCycle.refl, SameCycle.symm, SameCycle.trans
-/
theorem SameCycle.equivalence : Equivalence (SameCycle f) :=
  ⟨SameCycle.refl f, SameCycle.symm, SameCycle.trans⟩

/-- The setoid defined by the `SameCycle` relation. -/
@[instance_reducible]
/--
Definition of `SameCycle.setoid` / `SameCycle.setoid` 的定义

English:
definition SameCycle.setoid
  signature: (f : Perm α)
  body: f.SameCycle
  iseqv := SameCycle.equivalence f

@[simp]

中文:
定义 SameCycle.setoid
  签名: (f : 置换 α)
  定义体: f.SameCycle
  iseqv := SameCycle.equivalence f

@[simp]

Depends on / 依赖: SameCycle, f.SameCycle
-/
def SameCycle.setoid (f : Perm α) : Setoid α where
  r := f.SameCycle
  iseqv := SameCycle.equivalence f

@[simp]
/--
theorem `sameCycle_one` / 定理 `sameCycle_one`

English:
theorem sameCycle_one
  statement: SameCycle 1 x y ↔ x = y
  proof: by simp [SameCycle]

@[simp]

中文:
定理 sameCycle_one
  结论: SameCycle 1 x y ↔ x = y
  证明: by simp [SameCycle]

@[simp]

Depends on / 依赖: SameCycle
-/
theorem sameCycle_one : SameCycle 1 x y ↔ x = y := by simp [SameCycle]

@[simp]
/--
theorem `sameCycle_inv` / 定理 `sameCycle_inv`

English:
theorem sameCycle_inv
  statement: SameCycle f⁻¹ x y ↔ SameCycle f x y
  proof: (Equiv.neg _).exists_congr_left.trans by simp [SameCycle]

alias ⟨SameCycle.of_inv, SameCycle.inv⟩ := sameCycle_inv

@[simp]

中文:
定理 sameCycle_inv
  结论: SameCycle f⁻¹ x y ↔ SameCycle f x y
  证明: (Equiv.neg _).exists_congr_left.trans by simp [SameCycle]

alias ⟨SameCycle.of_inv, SameCycle.inv⟩ := sameCycle_inv

@[simp]

Depends on / 依赖: Equiv.neg, SameCycle, exists_congr_left, exists_congr_left.trans
-/
theorem sameCycle_inv : SameCycle f⁻¹ x y ↔ SameCycle f x y :=
(Equiv.neg _).exists_congr_left.trans by simp [SameCycle]

alias ⟨SameCycle.of_inv, SameCycle.inv⟩ := sameCycle_inv

@[simp]
/--
theorem `sameCycle_conj` / 定理 `sameCycle_conj`

English:
theorem sameCycle_conj
  statement: SameCycle (g * f * g⁻¹) x y ↔ SameCycle f (g⁻¹ x) (g⁻¹ y)
  proof: exists_congr fun i => by simp [conj_zpow, eq_symm_apply]

中文:
定理 sameCycle_conj
  结论: SameCycle (g * f * g⁻¹) x y ↔ SameCycle f (g⁻¹ x) (g⁻¹ y)
  证明: exists_congr fun i => by simp [conj_zpow, eq_symm_apply]

Depends on / 依赖: conj_zpow, eq_symm_apply, exists_congr
-/
theorem sameCycle_conj : SameCycle (g * f * g⁻¹) x y ↔ SameCycle f (g⁻¹ x) (g⁻¹ y) :=
  exists_congr fun i => by simp [conj_zpow, eq_symm_apply]

/--
theorem `SameCycle.conj` / 定理 `SameCycle.conj`

English:
theorem SameCycle.conj
  statement: SameCycle f x y -> SameCycle (g * f * g⁻¹) (g x) (g y)
  proof: by
  simp [sameCycle_conj]

中文:
定理 SameCycle.conj
  结论: SameCycle f x y -> SameCycle (g * f * g⁻¹) (g x) (g y)
  证明: by
  simp [sameCycle_conj]

Depends on / 依赖: sameCycle_conj
-/
theorem SameCycle.conj : SameCycle f x y -> SameCycle (g * f * g⁻¹) (g x) (g y) := by
  simp [sameCycle_conj]

/--
theorem `SameCycle.apply_eq_self_iff` / 定理 `SameCycle.apply_eq_self_iff`

English:
theorem SameCycle.apply_eq_self_iff
  statement: SameCycle f x y -> (f x = x ↔ f y = y)
  proof: fun ⟨i, hi⟩ => by
  rw [← hi]; rw [← mul_apply]; rw [← zpow_one_add]; rw [add_comm]; rw [zpow_add_one]; rw [mul_apply]; rw [(f ^ i).injective.eq_iff]

中文:
定理 SameCycle.apply_eq_self_iff
  结论: SameCycle f x y -> (f x = x ↔ f y = y)
  证明: fun ⟨i, hi⟩ => by
  rw [← hi]; rw [← mul_apply]; rw [← zpow_one_add]; rw [add_comm]; rw [zpow_add_one]; rw [mul_apply]; rw [(f ^ i).injective.eq_iff]

Depends on / 依赖: add_comm, eq_iff, injective, injective.eq_iff, mul_apply, zpow_add_one, zpow_one_add
-/
theorem SameCycle.apply_eq_self_iff : SameCycle f x y -> (f x = x ↔ f y = y) := fun ⟨i, hi⟩ => by
  rw [← hi]; rw [← mul_apply]; rw [← zpow_one_add]; rw [add_comm]; rw [zpow_add_one]; rw [mul_apply]; rw [(f ^ i).injective.eq_iff]

/--
theorem `SameCycle.eq_of_left` / 定理 `SameCycle.eq_of_left`

English:
theorem SameCycle.eq_of_left
  given: (h : SameCycle f x y) (hx : IsFixedPt f x)
  statement: x = y
  proof: let ⟨_, hn⟩ := h
  (hx.perm_zpow _).eq.symm.trans hn

中文:
定理 SameCycle.eq_of_left
  条件: (h : SameCycle f x y) (hx : IsFixedPt f x)
  结论: x = y
  证明: let ⟨_, hn⟩ := h
  (hx.perm_zpow _).eq.symm.trans hn

Depends on / 依赖: eq.symm.trans, hx.perm_zpow, perm_zpow
-/
theorem SameCycle.eq_of_left (h : SameCycle f x y) (hx : IsFixedPt f x) : x = y :=
  let ⟨_, hn⟩ := h
  (hx.perm_zpow _).eq.symm.trans hn

/--
theorem `SameCycle.eq_of_right` / 定理 `SameCycle.eq_of_right`

English:
theorem SameCycle.eq_of_right
  given: (h : SameCycle f x y) (hy : IsFixedPt f y)
  statement: x = y
  proof: h.eq_of_left h.apply_eq_self_iff.2 hy

@[simp]

中文:
定理 SameCycle.eq_of_right
  条件: (h : SameCycle f x y) (hy : IsFixedPt f y)
  结论: x = y
  证明: h.eq_of_left h.apply_eq_self_iff.2 hy

@[simp]

Depends on / 依赖: apply_eq_self_iff, eq_of_left, h.apply_eq_self_iff, h.eq_of_left
-/
theorem SameCycle.eq_of_right (h : SameCycle f x y) (hy : IsFixedPt f y) : x = y :=
h.eq_of_left h.apply_eq_self_iff.2 hy

@[simp]
/--
theorem `sameCycle_apply_left` / 定理 `sameCycle_apply_left`

English:
theorem sameCycle_apply_left
  statement: SameCycle f (f x) y ↔ SameCycle f x y
  proof: (Equiv.addRight 1).exists_congr_left.trans by
    simp [zpow_sub, SameCycle, Int.add_neg_one, Function.comp]

@[simp]

中文:
定理 sameCycle_apply_left
  结论: SameCycle f (f x) y ↔ SameCycle f x y
  证明: (Equiv.addRight 1).exists_congr_left.trans by
    simp [zpow_sub, SameCycle, Int.add_neg_one, Function.comp]

@[simp]

Depends on / 依赖: Equiv.addRight, Function, Function.comp, Int.add_neg_one, SameCycle, addRight, add_neg_one, exists_congr_left, exists_congr_left.trans, zpow_sub
-/
theorem sameCycle_apply_left : SameCycle f (f x) y ↔ SameCycle f x y :=
(Equiv.addRight 1).exists_congr_left.trans by
    simp [zpow_sub, SameCycle, Int.add_neg_one, Function.comp]

@[simp]
/--
theorem `sameCycle_apply_right` / 定理 `sameCycle_apply_right`

English:
theorem sameCycle_apply_right
  statement: SameCycle f x (f y) ↔ SameCycle f x y
  proof: by
  rw [sameCycle_comm]; rw [sameCycle_apply_left]; rw [sameCycle_comm]

@[simp]

中文:
定理 sameCycle_apply_right
  结论: SameCycle f x (f y) ↔ SameCycle f x y
  证明: by
  rw [sameCycle_comm]; rw [sameCycle_apply_left]; rw [sameCycle_comm]

@[simp]

Depends on / 依赖: sameCycle_apply_left, sameCycle_comm
-/
theorem sameCycle_apply_right : SameCycle f x (f y) ↔ SameCycle f x y := by
  rw [sameCycle_comm]; rw [sameCycle_apply_left]; rw [sameCycle_comm]

@[simp]
/--
theorem `sameCycle_symm_apply_left` / 定理 `sameCycle_symm_apply_left`

English:
theorem sameCycle_symm_apply_left
  statement: SameCycle f (f.symm x) y ↔ SameCycle f x y
  proof: by
  rw [← sameCycle_apply_left]; rw [apply_symm_apply]

@[simp]

中文:
定理 sameCycle_symm_apply_left
  结论: SameCycle f (f.symm x) y ↔ SameCycle f x y
  证明: by
  rw [← sameCycle_apply_left]; rw [apply_symm_apply]

@[simp]

Depends on / 依赖: apply_symm_apply, sameCycle_apply_left
-/
theorem sameCycle_symm_apply_left : SameCycle f (f.symm x) y ↔ SameCycle f x y := by
  rw [← sameCycle_apply_left]; rw [apply_symm_apply]

@[simp]
/--
theorem `sameCycle_symm_apply_right` / 定理 `sameCycle_symm_apply_right`

English:
theorem sameCycle_symm_apply_right
  statement: SameCycle f x (f.symm y) ↔ SameCycle f x y
  proof: by
  rw [← sameCycle_apply_right]; rw [apply_symm_apply]

@[simp]

中文:
定理 sameCycle_symm_apply_right
  结论: SameCycle f x (f.symm y) ↔ SameCycle f x y
  证明: by
  rw [← sameCycle_apply_right]; rw [apply_symm_apply]

@[simp]

Depends on / 依赖: apply_symm_apply, sameCycle_apply_right
-/
theorem sameCycle_symm_apply_right : SameCycle f x (f.symm y) ↔ SameCycle f x y := by
  rw [← sameCycle_apply_right]; rw [apply_symm_apply]

@[simp]
/--
theorem `sameCycle_zpow_left` / 定理 `sameCycle_zpow_left`

English:
theorem sameCycle_zpow_left
  given: {n : Int}
  statement: SameCycle f ((f ^ n) x) y ↔ SameCycle f x y
  proof: (Equiv.addRight (n : Int)).exists_congr_left.trans by simp [SameCycle, zpow_add]

@[simp]

中文:
定理 sameCycle_zpow_left
  条件: {n : 整数}
  结论: SameCycle f ((f ^ n) x) y ↔ SameCycle f x y
  证明: (Equiv.addRight (n : Int)).exists_congr_left.trans by simp [SameCycle, zpow_add]

@[simp]

Depends on / 依赖: Equiv.addRight, SameCycle, addRight, exists_congr_left, exists_congr_left.trans, zpow_add
-/
theorem sameCycle_zpow_left {n : Int} : SameCycle f ((f ^ n) x) y ↔ SameCycle f x y :=
(Equiv.addRight (n : Int)).exists_congr_left.trans by simp [SameCycle, zpow_add]

@[simp]
/--
theorem `sameCycle_zpow_right` / 定理 `sameCycle_zpow_right`

English:
theorem sameCycle_zpow_right
  given: {n : Int}
  statement: SameCycle f x ((f ^ n) y) ↔ SameCycle f x y
  proof: by
  rw [sameCycle_comm]; rw [sameCycle_zpow_left]; rw [sameCycle_comm]

@[simp]

中文:
定理 sameCycle_zpow_right
  条件: {n : 整数}
  结论: SameCycle f x ((f ^ n) y) ↔ SameCycle f x y
  证明: by
  rw [sameCycle_comm]; rw [sameCycle_zpow_left]; rw [sameCycle_comm]

@[simp]

Depends on / 依赖: sameCycle_comm, sameCycle_zpow_left
-/
theorem sameCycle_zpow_right {n : Int} : SameCycle f x ((f ^ n) y) ↔ SameCycle f x y := by
  rw [sameCycle_comm]; rw [sameCycle_zpow_left]; rw [sameCycle_comm]

@[simp]
/--
theorem `sameCycle_pow_left` / 定理 `sameCycle_pow_left`

English:
theorem sameCycle_pow_left
  given: {n : Nat}
  statement: SameCycle f ((f ^ n) x) y ↔ SameCycle f x y
  proof: by
  rw [← zpow_natCast]; rw [sameCycle_zpow_left]

@[simp]

中文:
定理 sameCycle_pow_left
  条件: {n : 自然数}
  结论: SameCycle f ((f ^ n) x) y ↔ SameCycle f x y
  证明: by
  rw [← zpow_natCast]; rw [sameCycle_zpow_left]

@[simp]

Depends on / 依赖: sameCycle_zpow_left, zpow_natCast
-/
theorem sameCycle_pow_left {n : Nat} : SameCycle f ((f ^ n) x) y ↔ SameCycle f x y := by
  rw [← zpow_natCast]; rw [sameCycle_zpow_left]

@[simp]
/--
theorem `sameCycle_pow_right` / 定理 `sameCycle_pow_right`

English:
theorem sameCycle_pow_right
  given: {n : Nat}
  statement: SameCycle f x ((f ^ n) y) ↔ SameCycle f x y
  proof: by
  rw [← zpow_natCast]; rw [sameCycle_zpow_right]

alias ⟨SameCycle.of_apply_left, SameCycle.apply_left⟩ := sameCycle_apply_left

alias ⟨SameCycle.of_apply_right, SameCycle.apply_right⟩ := sameCycle_apply_right

alias ⟨SameCycle.of_symm_apply_left, SameCycle.symm_apply_left⟩ := sameCycle_symm_appl

中文:
定理 sameCycle_pow_right
  条件: {n : 自然数}
  结论: SameCycle f x ((f ^ n) y) ↔ SameCycle f x y
  证明: by
  rw [← zpow_natCast]; rw [sameCycle_zpow_right]

alias ⟨SameCycle.of_apply_left, SameCycle.apply_left⟩ := sameCycle_apply_left

alias ⟨SameCycle.of_apply_right, SameCycle.apply_right⟩ := sameCycle_apply_right

alias ⟨SameCycle.of_symm_apply_left, SameCycle.symm_apply_left⟩ := sameCycle_symm_appl

Depends on / 依赖: sameCycle_zpow_right, zpow_natCast
-/
theorem sameCycle_pow_right {n : Nat} : SameCycle f x ((f ^ n) y) ↔ SameCycle f x y := by
  rw [← zpow_natCast]; rw [sameCycle_zpow_right]

alias ⟨SameCycle.of_apply_left, SameCycle.apply_left⟩ := sameCycle_apply_left

alias ⟨SameCycle.of_apply_right, SameCycle.apply_right⟩ := sameCycle_apply_right

alias ⟨SameCycle.of_symm_apply_left, SameCycle.symm_apply_left⟩ := sameCycle_symm_apply_left

alias ⟨SameCycle.of_symm_apply_right, SameCycle.symm_apply_right⟩ := sameCycle_symm_apply_right

alias ⟨SameCycle.of_pow_left, SameCycle.pow_left⟩ := sameCycle_pow_left

alias ⟨SameCycle.of_pow_right, SameCycle.pow_right⟩ := sameCycle_pow_right

alias ⟨SameCycle.of_zpow_left, SameCycle.zpow_left⟩ := sameCycle_zpow_left

alias ⟨SameCycle.of_zpow_right, SameCycle.zpow_right⟩ := sameCycle_zpow_right

/--
theorem `SameCycle.of_pow` / 定理 `SameCycle.of_pow`

English:
theorem SameCycle.of_pow
  given: {n : Nat}
  statement: SameCycle (f ^ n) x y -> SameCycle f x y
  proof: fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩

中文:
定理 SameCycle.of_pow
  条件: {n : 自然数}
  结论: SameCycle (f ^ n) x y -> SameCycle f x y
  证明: fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩
-/
theorem SameCycle.of_pow {n : Nat} : SameCycle (f ^ n) x y -> SameCycle f x y := fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩

/--
theorem `SameCycle.of_zpow` / 定理 `SameCycle.of_zpow`

English:
theorem SameCycle.of_zpow
  given: {n : Int}
  statement: SameCycle (f ^ n) x y -> SameCycle f x y
  proof: fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩

@[simp]

中文:
定理 SameCycle.of_zpow
  条件: {n : 整数}
  结论: SameCycle (f ^ n) x y -> SameCycle f x y
  证明: fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩

@[simp]
-/
theorem SameCycle.of_zpow {n : Int} : SameCycle (f ^ n) x y -> SameCycle f x y := fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩

@[simp]
/--
theorem `sameCycle_subtypePerm` / 定理 `sameCycle_subtypePerm`

English:
theorem sameCycle_subtypePerm
  given: {h} {x y : { x // p x }}
  proof: exists_congr fun n => by simp [Subtype.ext_iff]

alias ⟨_, SameCycle.subtypePerm⟩ := sameCycle_subtypePerm

@[simp]

中文:
定理 sameCycle_subtypePerm
  条件: {h} {x y : { x // p x }}
  证明: exists_congr fun n => by simp [Subtype.ext_iff]

alias ⟨_, SameCycle.subtypePerm⟩ := sameCycle_subtypePerm

@[simp]

Depends on / 依赖: Subtype, Subtype.ext_iff, exists_congr, ext_iff
-/
theorem sameCycle_subtypePerm {h} {x y : { x // p x }} :
    (f.subtypePerm h).SameCycle x y ↔ f.SameCycle x y :=
  exists_congr fun n => by simp [Subtype.ext_iff]

alias ⟨_, SameCycle.subtypePerm⟩ := sameCycle_subtypePerm

@[simp]
/--
theorem `sameCycle_extendDomain` / 定理 `sameCycle_extendDomain`

English:
theorem sameCycle_extendDomain
  given: {p : β -> Prop} [DecidablePred p] {f : α ≃ Subtype p}
  proof: exists_congr fun n => by
    rw [← extendDomain_zpow]; rw [extendDomain_apply_image]; rw [Subtype.coe_inj]; rw [f.injective.eq_iff]

alias ⟨_, SameCycle.extendDomain⟩ := sameCycle_extendDomain

中文:
定理 sameCycle_extendDomain
  条件: {p : β -> 命题} [DecidablePred p] {f : α ≃ 子类型 p}
  证明: exists_congr fun n => by
    rw [← extendDomain_zpow]; rw [extendDomain_apply_image]; rw [Subtype.coe_inj]; rw [f.injective.eq_iff]

alias ⟨_, SameCycle.extendDomain⟩ := sameCycle_extendDomain

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj, eq_iff, exists_congr, extendDomain_apply_image, extendDomain_zpow, f.injective.eq_iff, injective
-/
theorem sameCycle_extendDomain {p : β -> Prop} [DecidablePred p] {f : α ≃ Subtype p} :
    SameCycle (g.extendDomain f) (f x) (f y) ↔ g.SameCycle x y :=
  exists_congr fun n => by
    rw [← extendDomain_zpow]; rw [extendDomain_apply_image]; rw [Subtype.coe_inj]; rw [f.injective.eq_iff]

alias ⟨_, SameCycle.extendDomain⟩ := sameCycle_extendDomain

/--
theorem `SameCycle.exists_pow_eq'` / 定理 `SameCycle.exists_pow_eq'`

English:
theorem SameCycle.exists_pow_eq'
  given: [Finite α]
  statement: SameCycle f x y -> exists i < orderOf f, (f ^ i) x = y
  proof: by
  rintro ⟨k, rfl⟩
  use (k % orderOf f).natAbs
  have h₀ := Int.natCast_pos.mpr (orderOf_pos f)
  have h₁ := Int.emod_nonneg k h₀.ne'
  rw [← zpow_natCast]; rw [Int.natAbs_of_nonneg h₁]; rw [zpow_mod_orderOf]
  refine ⟨?_, by rfl⟩
  rw [← Int.ofNat_lt]; rw [Int.natAbs_of_nonneg h₁]
  exact Int.em

中文:
定理 SameCycle.存在_pow_eq'
  条件: [有限 α]
  结论: SameCycle f x y -> 存在 i < orderOf f, (f ^ i) x = y
  证明: by
  rintro ⟨k, rfl⟩
  use (k % orderOf f).natAbs
  have h₀ := Int.natCast_pos.mpr (orderOf_pos f)
  have h₁ := Int.emod_nonneg k h₀.ne'
  rw [← zpow_natCast]; rw [Int.natAbs_of_nonneg h₁]; rw [zpow_mod_orderOf]
  refine ⟨?_, by rfl⟩
  rw [← Int.ofNat_lt]; rw [Int.natAbs_of_nonneg h₁]
  exact Int.em

Depends on / 依赖: Int.emod_lt_of_pos, Int.emod_nonneg, Int.natAbs_of_nonneg, Int.natCast_pos.mpr, Int.ofNat_lt, emod_lt_of_pos, emod_nonneg, natAbs, natAbs_of_nonneg, natCast_pos, ofNat_lt, orderOf, orderOf_pos, zpow_mod_orderOf, zpow_natCast
-/
theorem SameCycle.exists_pow_eq' [Finite α] : SameCycle f x y -> exists i < orderOf f, (f ^ i) x = y := by
  rintro ⟨k, rfl⟩
  use (k % orderOf f).natAbs
  have h₀ := Int.natCast_pos.mpr (orderOf_pos f)
  have h₁ := Int.emod_nonneg k h₀.ne'
  rw [← zpow_natCast]; rw [Int.natAbs_of_nonneg h₁]; rw [zpow_mod_orderOf]
  refine ⟨?_, by rfl⟩
  rw [← Int.ofNat_lt]; rw [Int.natAbs_of_nonneg h₁]
  exact Int.emod_lt_of_pos _ h₀

/--
theorem `SameCycle.exists_pow_eq''` / 定理 `SameCycle.exists_pow_eq''`

English:
theorem SameCycle.exists_pow_eq''
  given: [Finite α] (h : SameCycle f x y)
  proof: by
  obtain ⟨_ | i, hi, rfl⟩ := h.exists_pow_eq'
  · refine ⟨orderOf f, orderOf_pos f, le_rfl, ?_⟩
    rw [pow_orderOf_eq_one]; rw [pow_zero]
  · exact ⟨i.succ, i.zero_lt_succ, hi.le, by rfl⟩

中文:
定理 SameCycle.存在_pow_eq''
  条件: [有限 α] (h : SameCycle f x y)
  证明: by
  obtain ⟨_ | i, hi, rfl⟩ := h.exists_pow_eq'
  · refine ⟨orderOf f, orderOf_pos f, le_rfl, ?_⟩
    rw [pow_orderOf_eq_one]; rw [pow_zero]
  · exact ⟨i.succ, i.zero_lt_succ, hi.le, by rfl⟩

Depends on / 依赖: exists_pow_eq, h.exists_pow_eq, hi.le, i.succ, i.zero_lt_succ, le_rfl, orderOf, orderOf_pos, pow_orderOf_eq_one, pow_zero, zero_lt_succ
-/
theorem SameCycle.exists_pow_eq'' [Finite α] (h : SameCycle f x y) :
    exists i : Nat, 0 < i ∧ i <= orderOf f ∧ (f ^ i) x = y := by
  obtain ⟨_ | i, hi, rfl⟩ := h.exists_pow_eq'
  · refine ⟨orderOf f, orderOf_pos f, le_rfl, ?_⟩
    rw [pow_orderOf_eq_one]; rw [pow_zero]
  · exact ⟨i.succ, i.zero_lt_succ, hi.le, by rfl⟩

/--
theorem `SameCycle.exists_fin_pow_eq` / 定理 `SameCycle.exists_fin_pow_eq`

English:
theorem SameCycle.exists_fin_pow_eq
  given: [Finite α] (h : SameCycle f x y)
  proof: by
  obtain ⟨i, hi, hx⟩ := SameCycle.exists_pow_eq' h
  exact ⟨⟨i, hi⟩, hx⟩

中文:
定理 SameCycle.存在_fin_pow_eq
  条件: [有限 α] (h : SameCycle f x y)
  证明: by
  obtain ⟨i, hi, hx⟩ := SameCycle.exists_pow_eq' h
  exact ⟨⟨i, hi⟩, hx⟩

Depends on / 依赖: SameCycle, SameCycle.exists_pow_eq, exists_pow_eq
-/
theorem SameCycle.exists_fin_pow_eq [Finite α] (h : SameCycle f x y) :
    exists i : Fin (orderOf f), (f ^ (i : Nat)) x = y := by
  obtain ⟨i, hi, hx⟩ := SameCycle.exists_pow_eq' h
  exact ⟨⟨i, hi⟩, hx⟩

/--
theorem `SameCycle.exists_nat_pow_eq` / 定理 `SameCycle.exists_nat_pow_eq`

English:
theorem SameCycle.exists_nat_pow_eq
  given: [Finite α] (h : SameCycle f x y)
  proof: by
  obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
  exact ⟨i, hi⟩

中文:
定理 SameCycle.存在_nat_pow_eq
  条件: [有限 α] (h : SameCycle f x y)
  证明: by
  obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
  exact ⟨i, hi⟩

Depends on / 依赖: exists_pow_eq, h.exists_pow_eq
-/
theorem SameCycle.exists_nat_pow_eq [Finite α] (h : SameCycle f x y) :
    exists i : Nat, (f ^ i) x = y := by
  obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
  exact ⟨i, hi⟩

instance (f : Perm α) [DecidableRel (SameCycle f)] :
    DecidableRel (SameCycle f⁻¹) := fun x y =>
  decidable_of_iff (f.SameCycle x y) sameCycle_inv.symm

instance (priority := 100) [DecidableEq α] : DecidableRel (SameCycle (1 : Perm α)) := fun x y =>
  decidable_of_iff (x = y) sameCycle_one.symm

end SameCycle

/-!
### `IsCycle`
-/

section IsCycle

variable {f g : Perm α} {x y : α}

/--
Definition of `IsCycle` / `IsCycle` 的定义

English:
definition IsCycle
  signature: (f : Perm α)
  body: exists x, f x != x ∧ forall ⦃y⦄, f y != y -> SameCycle f x y

中文:
定义 是环
  签名: (f : 置换 α)
  定义体: exists x, f x != x ∧ forall ⦃y⦄, f y != y -> SameCycle f x y

Depends on / 依赖: SameCycle
-/
def IsCycle (f : Perm α) : Prop :=
  exists x, f x != x ∧ forall ⦃y⦄, f y != y -> SameCycle f x y

/--
theorem `IsCycle.ne_one` / 定理 `IsCycle.ne_one`

English:
theorem IsCycle.ne_one
  given: (h : IsCycle f)
  statement: f != 1
  proof: fun hf => by simp [hf, IsCycle] at h

@[simp]

中文:
定理 是环.ne_one
  条件: (h : 是环 f)
  结论: f != 1
  证明: fun hf => by simp [hf, IsCycle] at h

@[simp]

Depends on / 依赖: IsCycle
-/
theorem IsCycle.ne_one (h : IsCycle f) : f != 1 := fun hf => by simp [hf, IsCycle] at h

@[simp]
/--
theorem `not_isCycle_one` / 定理 `not_isCycle_one`

English:
theorem not_isCycle_one
  statement: ¬(1 : Perm α).IsCycle
  proof: fun H => H.ne_one rfl

中文:
定理 not_isCycle_one
  结论: ¬(1 : 置换 α).是环
  证明: fun H => H.ne_one rfl

Depends on / 依赖: H.ne_one, ne_one
-/
theorem not_isCycle_one : ¬(1 : Perm α).IsCycle := fun H => H.ne_one rfl

/--
theorem `IsCycle.sameCycle` / 定理 `IsCycle.sameCycle`

English:
theorem IsCycle.sameCycle
  given: (hf : IsCycle f) (hx : f x != x) (hy : f y != y)
  proof: let ⟨g, hg⟩ := hf
  let ⟨a, ha⟩ := hg.2 hx
  let ⟨b, hb⟩ := hg.2 hy
  ⟨b - a, by rw [← ha, ← mul_apply, ← zpow_add, sub_add_cancel, hb]⟩

中文:
定理 是环.sameCycle
  条件: (hf : 是环 f) (hx : f x != x) (hy : f y != y)
  证明: let ⟨g, hg⟩ := hf
  let ⟨a, ha⟩ := hg.2 hx
  let ⟨b, hb⟩ := hg.2 hy
  ⟨b - a, by rw [← ha, ← mul_apply, ← zpow_add, sub_add_cancel, hb]⟩
-/
protected theorem IsCycle.sameCycle (hf : IsCycle f) (hx : f x != x) (hy : f y != y) :
    SameCycle f x y :=
  let ⟨g, hg⟩ := hf
  let ⟨a, ha⟩ := hg.2 hx
  let ⟨b, hb⟩ := hg.2 hy
  ⟨b - a, by rw [← ha, ← mul_apply, ← zpow_add, sub_add_cancel, hb]⟩

/--
theorem `IsCycle.exists_zpow_eq` / 定理 `IsCycle.exists_zpow_eq`

English:
theorem IsCycle.exists_zpow_eq
  statement: IsCycle f -> f x != x -> f y != y -> exists i : Int, (f ^ i) x = y
  proof: IsCycle.sameCycle

中文:
定理 是环.存在_zpow_eq
  结论: 是环 f -> f x != x -> f y != y -> 存在 i : 整数, (f ^ i) x = y
  证明: IsCycle.sameCycle

Depends on / 依赖: IsCycle, IsCycle.sameCycle, sameCycle
-/
theorem IsCycle.exists_zpow_eq : IsCycle f -> f x != x -> f y != y -> exists i : Int, (f ^ i) x = y :=
  IsCycle.sameCycle

/--
theorem `IsCycle.inv` / 定理 `IsCycle.inv`

English:
theorem IsCycle.inv
  given: (hf : IsCycle f)
  statement: IsCycle f⁻¹
  proof: hf.imp fun _ ⟨hx, h⟩ =>
    ⟨inv_eq_iff_eq.not.2 hx.symm, fun _ hy => (h <| inv_eq_iff_eq.not.2 hy.symm).inv⟩

@[simp]

中文:
定理 是环.inv
  条件: (hf : 是环 f)
  结论: 是环 f⁻¹
  证明: hf.imp fun _ ⟨hx, h⟩ =>
    ⟨inv_eq_iff_eq.not.2 hx.symm, fun _ hy => (h <| inv_eq_iff_eq.not.2 hy.symm).inv⟩

@[simp]

Depends on / 依赖: hf.imp, hx.symm, hy.symm, inv_eq_iff_eq, inv_eq_iff_eq.not
-/
theorem IsCycle.inv (hf : IsCycle f) : IsCycle f⁻¹ :=
  hf.imp fun _ ⟨hx, h⟩ =>
    ⟨inv_eq_iff_eq.not.2 hx.symm, fun _ hy => (h <| inv_eq_iff_eq.not.2 hy.symm).inv⟩

@[simp]
/--
theorem `isCycle_inv` / 定理 `isCycle_inv`

English:
theorem isCycle_inv
  statement: IsCycle f⁻¹ ↔ IsCycle f
  proof: ⟨fun h => h.inv, IsCycle.inv⟩

中文:
定理 isCycle_inv
  结论: 是环 f⁻¹ ↔ 是环 f
  证明: ⟨fun h => h.inv, IsCycle.inv⟩

Depends on / 依赖: IsCycle, IsCycle.inv, h.inv
-/
theorem isCycle_inv : IsCycle f⁻¹ ↔ IsCycle f :=
  ⟨fun h => h.inv, IsCycle.inv⟩

/--
theorem `IsCycle.conj` / 定理 `IsCycle.conj`

English:
theorem IsCycle.conj
  statement: IsCycle f -> IsCycle (g * f * g⁻¹)
  proof: by
  rintro ⟨x, hx, h⟩
  refine ⟨g x, by simp [coe_mul, hx], fun y hy => ?_⟩
  simpa using (h <| eq_inv_iff_eq.not.2 hy).conj (g := g)

中文:
定理 是环.conj
  结论: 是环 f -> 是环 (g * f * g⁻¹)
  证明: by
  rintro ⟨x, hx, h⟩
  refine ⟨g x, by simp [coe_mul, hx], fun y hy => ?_⟩
  simpa using (h <| eq_inv_iff_eq.not.2 hy).conj (g := g)

Depends on / 依赖: coe_mul, eq_inv_iff_eq, eq_inv_iff_eq.not
-/
theorem IsCycle.conj : IsCycle f -> IsCycle (g * f * g⁻¹) := by
  rintro ⟨x, hx, h⟩
  refine ⟨g x, by simp [coe_mul, hx], fun y hy => ?_⟩
  simpa using (h <| eq_inv_iff_eq.not.2 hy).conj (g := g)

/--
theorem `IsCycle.extendDomain` / 定理 `IsCycle.extendDomain`

English:
theorem IsCycle.extendDomain
  given: {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p)
  proof: by
  rintro ⟨a, ha, ha'⟩
  refine ⟨f a, ?_, fun b hb => ?_⟩
  · rw [extendDomain_apply_image]
    exact Subtype.coe_injective.ne (f.injective.ne ha)
  have h : b = f (f.symm ⟨b, of_not_not <| hb ∘ extendDomain_apply_not_subtype _ _⟩) := by
    rw [apply_symm_apply]; rw [Subtype.coe_mk]
  rw [h] at h

中文:
定理 是环.extendDomain
  条件: {p : β -> 命题} [DecidablePred p] (f : α ≃ 子类型 p)
  证明: by
  rintro ⟨a, ha, ha'⟩
  refine ⟨f a, ?_, fun b hb => ?_⟩
  · rw [extendDomain_apply_image]
    exact Subtype.coe_injective.ne (f.injective.ne ha)
  have h : b = f (f.symm ⟨b, of_not_not <| hb ∘ extendDomain_apply_not_subtype _ _⟩) := by
    rw [apply_symm_apply]; rw [Subtype.coe_mk]
  rw [h] at h
-/
protected theorem IsCycle.extendDomain {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p) :
    IsCycle g -> IsCycle (g.extendDomain f) := by
  rintro ⟨a, ha, ha'⟩
  refine ⟨f a, ?_, fun b hb => ?_⟩
  · rw [extendDomain_apply_image]
    exact Subtype.coe_injective.ne (f.injective.ne ha)
  have h : b = f (f.symm ⟨b, of_not_not <| hb ∘ extendDomain_apply_not_subtype _ _⟩) := by
    rw [apply_symm_apply]; rw [Subtype.coe_mk]
  rw [h] at hb ⊢
  simp only [extendDomain_apply_image, Subtype.coe_injective.ne_iff, f.injective.ne_iff] at hb
  exact (ha' hb).extendDomain

/--
theorem `isCycle_iff_sameCycle` / 定理 `isCycle_iff_sameCycle`

English:
theorem isCycle_iff_sameCycle
  given: (hx : f x != x)
  statement: IsCycle f ↔ forall {y}, SameCycle f x y ↔ f y != y
  proof: ⟨fun hf y =>
    ⟨fun ⟨i, hi⟩ hy =>
hx by
        rw [← zpow_apply_eq_self_of_apply_eq_self hy i]; rw [(f ^ i).injective.eq_iff] at hi
        rw [hi]; rw [hy],
      hf.exists_zpow_eq hx⟩,
    fun h => ⟨x, hx, fun _ hy => h.2 hy⟩⟩

中文:
定理 isCycle_iff_sameCycle
  条件: (hx : f x != x)
  结论: 是环 f ↔ 对任意 {y}, SameCycle f x y ↔ f y != y
  证明: ⟨fun hf y =>
    ⟨fun ⟨i, hi⟩ hy =>
hx by
        rw [← zpow_apply_eq_self_of_apply_eq_self hy i]; rw [(f ^ i).injective.eq_iff] at hi
        rw [hi]; rw [hy],
      hf.exists_zpow_eq hx⟩,
    fun h => ⟨x, hx, fun _ hy => h.2 hy⟩⟩

Depends on / 依赖: eq_iff, exists_zpow_eq, hf.exists_zpow_eq, injective, injective.eq_iff, zpow_apply_eq_self_of_apply_eq_self
-/
theorem isCycle_iff_sameCycle (hx : f x != x) : IsCycle f ↔ forall {y}, SameCycle f x y ↔ f y != y :=
  ⟨fun hf y =>
    ⟨fun ⟨i, hi⟩ hy =>
hx by
        rw [← zpow_apply_eq_self_of_apply_eq_self hy i]; rw [(f ^ i).injective.eq_iff] at hi
        rw [hi]; rw [hy],
      hf.exists_zpow_eq hx⟩,
    fun h => ⟨x, hx, fun _ hy => h.2 hy⟩⟩

section Finite

variable [Finite α]

/--
theorem `IsCycle.exists_pow_eq` / 定理 `IsCycle.exists_pow_eq`

English:
theorem IsCycle.exists_pow_eq
  given: (hf : IsCycle f) (hx : f x != x) (hy : f y != y)
  proof: by
  let ⟨n, hn⟩ := hf.exists_zpow_eq hx hy
  exact
      ⟨(n % orderOf f).toNat, by
        {have := n.emod_nonneg (Int.natCast_ne_zero.mpr (ne_of_gt (orderOf_pos f)))
         rwa [← zpow_natCast, Int.toNat_of_nonneg this, zpow_mod_orderOf]}⟩

中文:
定理 是环.存在_pow_eq
  条件: (hf : 是环 f) (hx : f x != x) (hy : f y != y)
  证明: by
  let ⟨n, hn⟩ := hf.exists_zpow_eq hx hy
  exact
      ⟨(n % orderOf f).toNat, by
        {have := n.emod_nonneg (Int.natCast_ne_zero.mpr (ne_of_gt (orderOf_pos f)))
         rwa [← zpow_natCast, Int.toNat_of_nonneg this, zpow_mod_orderOf]}⟩

Depends on / 依赖: Int.natCast_ne_zero.mpr, Int.toNat_of_nonneg, emod_nonneg, exists_zpow_eq, hf.exists_zpow_eq, n.emod_nonneg, natCast_ne_zero, ne_of_gt, orderOf, orderOf_pos, toNat_of_nonneg, zpow_mod_orderOf, zpow_natCast
-/
theorem IsCycle.exists_pow_eq (hf : IsCycle f) (hx : f x != x) (hy : f y != y) :
    exists i : Nat, (f ^ i) x = y := by
  let ⟨n, hn⟩ := hf.exists_zpow_eq hx hy
  exact
      ⟨(n % orderOf f).toNat, by
        {have := n.emod_nonneg (Int.natCast_ne_zero.mpr (ne_of_gt (orderOf_pos f)))
         rwa [← zpow_natCast, Int.toNat_of_nonneg this, zpow_mod_orderOf]}⟩

end Finite

variable [DecidableEq α]

/--
theorem `isCycle_swap` / 定理 `isCycle_swap`

English:
theorem isCycle_swap
  given: (hxy : x != y)
  statement: IsCycle (swap x y)
  proof: ⟨y, by rwa [swap_apply_right], fun a (ha : ite (a = x) y (ite (a = y) x a) != a) =>
    if hya : y = a then ⟨0, hya⟩
    else
      ⟨1, by
        rw [zpow_one]; rw [swap_apply_def]
        split_ifs at * <;> tauto⟩⟩

中文:
定理 isCycle_swap
  条件: (hxy : x != y)
  结论: 是环 (swap x y)
  证明: ⟨y, by rwa [swap_apply_right], fun a (ha : ite (a = x) y (ite (a = y) x a) != a) =>
    if hya : y = a then ⟨0, hya⟩
    else
      ⟨1, by
        rw [zpow_one]; rw [swap_apply_def]
        split_ifs at * <;> tauto⟩⟩

Depends on / 依赖: split_ifs, swap_apply_def, swap_apply_right, zpow_one
-/
theorem isCycle_swap (hxy : x != y) : IsCycle (swap x y) :=
  ⟨y, by rwa [swap_apply_right], fun a (ha : ite (a = x) y (ite (a = y) x a) != a) =>
    if hya : y = a then ⟨0, hya⟩
    else
      ⟨1, by
        rw [zpow_one]; rw [swap_apply_def]
        split_ifs at * <;> tauto⟩⟩

/--
theorem `IsSwap.isCycle` / 定理 `IsSwap.isCycle`

English:
theorem IsSwap.isCycle
  statement: IsSwap f -> IsCycle f
  proof: by
  rintro ⟨x, y, hxy, rfl⟩
  exact isCycle_swap hxy

中文:
定理 IsSwap.isCycle
  结论: IsSwap f -> 是环 f
  证明: by
  rintro ⟨x, y, hxy, rfl⟩
  exact isCycle_swap hxy
-/
protected theorem IsSwap.isCycle : IsSwap f -> IsCycle f := by
  rintro ⟨x, y, hxy, rfl⟩
  exact isCycle_swap hxy

/--
theorem `swap_isSwap_iff` / 定理 `swap_isSwap_iff`

English:
theorem swap_isSwap_iff
  given: {a b : α}
  proof: by
  constructor
  · intro h hab
    apply h.isCycle.ne_one
    aesop
  · intro h; use a, b

中文:
定理 swap_isSwap_iff
  条件: {a b : α}
  证明: by
  constructor
  · intro h hab
    apply h.isCycle.ne_one
    aesop
  · intro h; use a, b

Depends on / 依赖: h.isCycle.ne_one, isCycle, ne_one
-/
theorem swap_isSwap_iff {a b : α} :
    (swap a b).IsSwap ↔ a != b := by
  constructor
  · intro h hab
    apply h.isCycle.ne_one
    aesop
  · intro h; use a, b

variable [Fintype α]

/--
theorem `IsCycle.two_le_card_support` / 定理 `IsCycle.two_le_card_support`

English:
theorem IsCycle.two_le_card_support
  given: (h : IsCycle f)
  statement: 2 <= #f.support
  proof: two_le_card_support_of_ne_one h.ne_one

中文:
定理 是环.two_le_card_support
  条件: (h : 是环 f)
  结论: 2 <= #f.support
  证明: two_le_card_support_of_ne_one h.ne_one

Depends on / 依赖: h.ne_one, ne_one, two_le_card_support_of_ne_one
-/
theorem IsCycle.two_le_card_support (h : IsCycle f) : 2 <= #f.support :=
  two_le_card_support_of_ne_one h.ne_one

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IsCycle.zpowersEquivSupport` / `IsCycle.zpowersEquivSupport` 的定义

English:
definition IsCycle.zpowersEquivSupport
  signature: {σ : Perm α} (hσ : IsCycle σ)
  body: Equiv.ofBijective
    (fun (τ : ↥((Subgroup.zpowers σ) : Set (Perm α))) =>
      ⟨(τ : Perm α) (Classical.choose hσ), by
        obtain ⟨τ, n, rfl⟩ := τ
        rw [Subtype.coe_mk]; rw [zpow_apply_mem_support]; rw [mem_support]
        exact (Classical.choose_spec hσ).1⟩)
    (by
      constructor
 

中文:
定义 是环.zpowersEquivSupport
  签名: {σ : 置换 α} (hσ : 是环 σ)
  定义体: Equiv.ofBijective
    (fun (τ : ↥((Subgroup.zpowers σ) : Set (Perm α))) =>
      ⟨(τ : Perm α) (Classical.choose hσ), by
        obtain ⟨τ, n, rfl⟩ := τ
        rw [Subtype.coe_mk]; rw [zpow_apply_mem_support]; rw [mem_support]
        exact (Classical.choose_spec hσ).1⟩)
    (by
      constructor
 

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Equiv.ofBijective, Subgroup, Subgroup.zpowers, Subtype, Subtype.coe_mk, choose_spec, coe_mk, mem_support, ofBijective, simp_rw, zpow_apply_comm, zpow_apply_eq_self_of_apply_eq_self, zpow_apply_mem_support, zpowers
-/
noncomputable def IsCycle.zpowersEquivSupport {σ : Perm α} (hσ : IsCycle σ) :
    (Subgroup.zpowers σ) ≃ σ.support :=
  Equiv.ofBijective
    (fun (τ : ↥((Subgroup.zpowers σ) : Set (Perm α))) =>
      ⟨(τ : Perm α) (Classical.choose hσ), by
        obtain ⟨τ, n, rfl⟩ := τ
        rw [Subtype.coe_mk]; rw [zpow_apply_mem_support]; rw [mem_support]
        exact (Classical.choose_spec hσ).1⟩)
    (by
      constructor
      · rintro ⟨a, m, rfl⟩ ⟨b, n, rfl⟩ h
        ext y
        by_cases hy : σ y = y
        · simp_rw [zpow_apply_eq_self_of_apply_eq_self hy]
        · obtain ⟨i, rfl⟩ := (Classical.choose_spec hσ).2 hy
          rw [Subtype.coe_mk]; rw [Subtype.coe_mk]; rw [zpow_apply_comm σ m i]; rw [zpow_apply_comm σ n i]
          exact congr_arg _ (Subtype.ext_iff.mp h)
      · rintro ⟨y, hy⟩
        rw [mem_support] at hy
        obtain ⟨n, rfl⟩ := (Classical.choose_spec hσ).2 hy
        exact ⟨⟨σ ^ n, n, rfl⟩, rfl⟩)

@[simp]
/--
theorem `IsCycle.zpowersEquivSupport_apply` / 定理 `IsCycle.zpowersEquivSupport_apply`

English:
theorem IsCycle.zpowersEquivSupport_apply
  given: {σ : Perm α} (hσ : IsCycle σ) {n : Nat}
  proof: rfl

@[simp]

中文:
定理 是环.zpowersEquivSupport_apply
  条件: {σ : 置换 α} (hσ : 是环 σ) {n : 自然数}
  证明: rfl

@[simp]
-/
theorem IsCycle.zpowersEquivSupport_apply {σ : Perm α} (hσ : IsCycle σ) {n : Nat} :
    hσ.zpowersEquivSupport ⟨σ ^ n, n, rfl⟩ =
      ⟨(σ ^ n) (Classical.choose hσ),
        pow_apply_mem_support.2 (mem_support.2 (Classical.choose_spec hσ).1)⟩ :=
  rfl

@[simp]
/--
theorem `IsCycle.zpowersEquivSupport_symm_apply` / 定理 `IsCycle.zpowersEquivSupport_symm_apply`

English:
theorem IsCycle.zpowersEquivSupport_symm_apply
  given: {σ : Perm α} (hσ : IsCycle σ) (n : Nat)
  proof: (Equiv.symm_apply_eq _).2 hσ.zpowersEquivSupport_apply

中文:
定理 是环.zpowersEquivSupport_symm_apply
  条件: {σ : 置换 α} (hσ : 是环 σ) (n : 自然数)
  证明: (Equiv.symm_apply_eq _).2 hσ.zpowersEquivSupport_apply

Depends on / 依赖: Equiv.symm_apply_eq, symm_apply_eq, zpowersEquivSupport_apply
-/
theorem IsCycle.zpowersEquivSupport_symm_apply {σ : Perm α} (hσ : IsCycle σ) (n : Nat) :
    hσ.zpowersEquivSupport.symm
        ⟨(σ ^ n) (Classical.choose hσ),
          pow_apply_mem_support.2 (mem_support.2 (Classical.choose_spec hσ).1)⟩ =
      ⟨σ ^ n, n, rfl⟩ :=
  (Equiv.symm_apply_eq _).2 hσ.zpowersEquivSupport_apply

/--
theorem `IsCycle.orderOf` / 定理 `IsCycle.orderOf`

English:
theorem IsCycle.orderOf
  given: (hf : IsCycle f)
  statement: orderOf f = #f.support
  proof: by
  rw [← Fintype.card_zpowers]; rw [← Fintype.card_coe]
  convert! Fintype.card_congr (IsCycle.zpowersEquivSupport hf)

中文:
定理 是环.orderOf
  条件: (hf : 是环 f)
  结论: orderOf f = #f.support
  证明: by
  rw [← Fintype.card_zpowers]; rw [← Fintype.card_coe]
  convert! Fintype.card_congr (IsCycle.zpowersEquivSupport hf)
-/
protected theorem IsCycle.orderOf (hf : IsCycle f) : orderOf f = #f.support := by
  rw [← Fintype.card_zpowers]; rw [← Fintype.card_coe]
  convert! Fintype.card_congr (IsCycle.zpowersEquivSupport hf)

/--
theorem `isCycle_swap_mul_aux₁` / 定理 `isCycle_swap_mul_aux₁`

English:
theorem isCycle_swap_mul_aux₁
  given: {α : Type*} [DecidableEq α]
  proof: by
  intro n
  induction n with
  | zero => exact fun _ h => ⟨0, h⟩
  | succ n hn =>
    intro b x f hb h
    obtain hfbx | hfbx := eq_or_ne (f x) b
    · exact ⟨0, hfbx⟩
    have : f b != b ∧ b != x := ne_and_ne_of_swap_mul_apply_ne_self hb
    have hb' : (swap x (f x) * f) (f.symm b) != f.symm b :

中文:
定理 isCycle_swap_mul_aux₁
  条件: {α : 类型} [DecidableEq α]
  证明: by
  intro n
  induction n with
  | zero => exact fun _ h => ⟨0, h⟩
  | succ n hn =>
    intro b x f hb h
    obtain hfbx | hfbx := eq_or_ne (f x) b
    · exact ⟨0, hfbx⟩
    have : f b != b ∧ b != x := ne_and_ne_of_swap_mul_apply_ne_self hb
    have hb' : (swap x (f x) * f) (f.symm b) != f.symm b :

Depends on / 依赖: AddCommGroup, AddCon, AddCon.Quotient, Quotient, add_comm, eq_iff, eq_or_ne, eq_symm_apply, f.injective, f.injective.eq_iff, f.symm, hfbx.symm, injective, mul_appl, ne_and_ne_of_swap_mul_apply_ne_self, pow_succ, swap_apply_of_ne_of_ne, zpow_add
-/
theorem isCycle_swap_mul_aux₁ {α : Type*} [DecidableEq α] :
    forall (n : Nat) {b x : α} {f : Perm α} (_ : (swap x (f x) * f) b != b) (_ : (f ^ n) (f x) = b),
      exists i : Int, ((swap x (f x) * f) ^ i) (f x) = b := by
  intro n
  induction n with
  | zero => exact fun _ h => ⟨0, h⟩
  | succ n hn =>
    intro b x f hb h
    obtain hfbx | hfbx := eq_or_ne (f x) b
    · exact ⟨0, hfbx⟩
    have : f b != b ∧ b != x := ne_and_ne_of_swap_mul_apply_ne_self hb
    have hb' : (swap x (f x) * f) (f.symm b) != f.symm b := by
      simpa [swap_apply_of_ne_of_ne this.2 hfbx.symm, eq_symm_apply, f.injective.eq_iff]
        using this.1
obtain ⟨i, hi⟩ := hn hb' f.injective by simpa [pow_succ'] using h
    refine ⟨i + 1, ?_⟩
    rw [add_comm]; rw [zpow_add]; rw [mul_apply]; rw [hi]; rw [zpow_one]; rw [mul_apply]; rw [apply_symm_apply]; rw [swap_apply_of_ne_of_ne (ne_and_ne_of_swap_mul_apply_ne_self hb).2 hfbx.symm]

/--
theorem `isCycle_swap_mul_aux₂` / 定理 `isCycle_swap_mul_aux₂`

English:
theorem isCycle_swap_mul_aux₂
  given: {α : Type*} [DecidableEq α]
  proof: eq_or_ne (f x) b
    · exact ⟨0, hfxb⟩
    obtain ⟨hfb, hbx⟩ : f b != b ∧ b != x := ne_and_ne_of_swap_mul_apply_ne_self hb
    replace hb : (swap x (f.symm x) * f⁻¹) (f.symm b) != f.symm b := by
      rw [mul_apply]; rw [swap_apply_def]
      split_ifs <;> simp [symm_apply_eq, eq_symm_apply] at * <;

中文:
定理 isCycle_swap_mul_aux₂
  条件: {α : 类型} [DecidableEq α]
  证明: eq_or_ne (f x) b
    · exact ⟨0, hfxb⟩
    obtain ⟨hfb, hbx⟩ : f b != b ∧ b != x := ne_and_ne_of_swap_mul_apply_ne_self hb
    replace hb : (swap x (f.symm x) * f⁻¹) (f.symm b) != f.symm b := by
      rw [mul_apply]; rw [swap_apply_def]
      split_ifs <;> simp [symm_apply_eq, eq_symm_apply] at * <;

Depends on / 依赖: eq_or_ne
-/
theorem isCycle_swap_mul_aux₂ {α : Type*} [DecidableEq α] :
    forall (n : Int) {b x : α} {f : Perm α}, (swap x (f x) * f) b != b -> (f ^ n) (f x) = b ->
      exists i : Int, ((swap x (f x) * f) ^ i) (f x) = b
  | (n : Nat), _, _, _, hb, h => isCycle_swap_mul_aux₁ n hb h
  | .negSucc n, b, x, f, hb, h => by
    obtain hfxb | hfxb := eq_or_ne (f x) b
    · exact ⟨0, hfxb⟩
    obtain ⟨hfb, hbx⟩ : f b != b ∧ b != x := ne_and_ne_of_swap_mul_apply_ne_self hb
    replace hb : (swap x (f.symm x) * f⁻¹) (f.symm b) != f.symm b := by
      rw [mul_apply]; rw [swap_apply_def]
      split_ifs <;> simp [symm_apply_eq, eq_symm_apply] at * <;> tauto
obtain ⟨i, hi⟩ := isCycle_swap_mul_aux₁ n hb by
      rw [← mul_apply]; rw [← pow_succ]; simpa [pow_succ', eq_symm_apply] using! h
    refine ⟨-i, (swap x (f⁻¹ x) * f⁻¹).injective ?_⟩
    convert! hi using 1
    · rw [zpow_neg, ← inv_zpow, ← mul_apply, mul_inv_rev, swap_inv, mul_swap_eq_swap_mul]
      simp [swap_comm _ x, ← mul_apply, -coe_mul, ← inv_def, -coe_inv, ← inv_def, mul_assoc _ f⁻¹,
        ← mul_zpow_mul, mul_assoc _ _ f]
      simp
    · exact swap_apply_of_ne_of_ne (by simpa [eq_comm, eq_symm_apply, symm_apply_eq] using! hfxb)
        (by simpa [eq_comm, eq_symm_apply, symm_apply_eq])

/--
theorem `IsCycle.eq_swap_of_apply_apply_eq_self` / 定理 `IsCycle.eq_swap_of_apply_apply_eq_self`

English:
theorem IsCycle.eq_swap_of_apply_apply_eq_self
  statement: {α : Type*} [DecidableEq α] {f : Perm α}
  proof: Equiv.ext fun y =>
    let ⟨z, hz⟩ := hf
    let ⟨i, hi⟩ := hz.2 hfx
    if hyx : y = x then by simp [hyx]
    else
      if hfyx : y = f x then by simp [hfyx, hffx]
      else by
        rw [swap_apply_of_ne_of_ne hyx hfyx]
        refine by_contradiction fun hy => ?_
        obtain ⟨j, hj⟩ := hz.2

中文:
定理 是环.eq_swap_of_apply_apply_eq_self
  结论: {α : 类型} [DecidableEq α] {f : 置换 α}
  证明: Equiv.ext fun y =>
    let ⟨z, hz⟩ := hf
    let ⟨i, hi⟩ := hz.2 hfx
    if hyx : y = x then by simp [hyx]
    else
      if hfyx : y = f x then by simp [hfyx, hffx]
      else by
        rw [swap_apply_of_ne_of_ne hyx hfyx]
        refine by_contradiction fun hy => ?_
        obtain ⟨j, hj⟩ := hz.2

Depends on / 依赖: Equiv.ext, by_contradiction, mul_apply, sub_add_cancel, swap_apply_of_ne_of_ne, zpow_add, zpow_apply_eq_of_apply_apply_eq_self
-/
theorem IsCycle.eq_swap_of_apply_apply_eq_self {α : Type*} [DecidableEq α] {f : Perm α}
    (hf : IsCycle f) {x : α} (hfx : f x != x) (hffx : f (f x) = x) : f = swap x (f x) :=
  Equiv.ext fun y =>
    let ⟨z, hz⟩ := hf
    let ⟨i, hi⟩ := hz.2 hfx
    if hyx : y = x then by simp [hyx]
    else
      if hfyx : y = f x then by simp [hfyx, hffx]
      else by
        rw [swap_apply_of_ne_of_ne hyx hfyx]
        refine by_contradiction fun hy => ?_
        obtain ⟨j, hj⟩ := hz.2 hy
        rw [← sub_add_cancel j i]; rw [zpow_add]; rw [mul_apply]; rw [hi] at hj
        rcases zpow_apply_eq_of_apply_apply_eq_self hffx (j - i) with hji | hji
        · rw [← hj, hji] at hyx
          tauto
        · rw [← hj, hji] at hfyx
          tauto

/--
theorem `IsCycle.swap_mul` / 定理 `IsCycle.swap_mul`

English:
theorem IsCycle.swap_mul
  statement: {α : Type*} [DecidableEq α] {f : Perm α} (hf : IsCycle f) {x : α}
  proof: by
  refine ⟨f x, ?_, fun y hy => ?_⟩
  · simp [swap_apply_def, mul_apply, if_neg hffx, f.injective.eq_iff, hx]
  obtain ⟨i, rfl⟩ := hf.exists_zpow_eq hx (ne_and_ne_of_swap_mul_apply_ne_self hy).1
  exact isCycle_swap_mul_aux₂ (i - 1) hy (by simp [← mul_apply, -coe_mul, ← zpow_add_one])

中文:
定理 是环.swap_mul
  结论: {α : 类型} [DecidableEq α] {f : 置换 α} (hf : 是环 f) {x : α}
  证明: by
  refine ⟨f x, ?_, fun y hy => ?_⟩
  · simp [swap_apply_def, mul_apply, if_neg hffx, f.injective.eq_iff, hx]
  obtain ⟨i, rfl⟩ := hf.exists_zpow_eq hx (ne_and_ne_of_swap_mul_apply_ne_self hy).1
  exact isCycle_swap_mul_aux₂ (i - 1) hy (by simp [← mul_apply, -coe_mul, ← zpow_add_one])

Depends on / 依赖: coe_mul, eq_iff, exists_zpow_eq, f.injective.eq_iff, hf.exists_zpow_eq, if_neg, injective, mul_apply, ne_and_ne_of_swap_mul_apply_ne_self, swap_apply_def, zpow_add_one
-/
theorem IsCycle.swap_mul {α : Type*} [DecidableEq α] {f : Perm α} (hf : IsCycle f) {x : α}
    (hx : f x != x) (hffx : f (f x) != x) : IsCycle (swap x (f x) * f) := by
  refine ⟨f x, ?_, fun y hy => ?_⟩
  · simp [swap_apply_def, mul_apply, if_neg hffx, f.injective.eq_iff, hx]
  obtain ⟨i, rfl⟩ := hf.exists_zpow_eq hx (ne_and_ne_of_swap_mul_apply_ne_self hy).1
  exact isCycle_swap_mul_aux₂ (i - 1) hy (by simp [← mul_apply, -coe_mul, ← zpow_add_one])

/--
theorem `IsCycle.sign` / 定理 `IsCycle.sign`

English:
theorem IsCycle.sign
  given: {f : Perm α} (hf : IsCycle f)
  statement: sign f = -(-1) ^ #f.support
  proof: let ⟨x, hx⟩ := hf
  calc
    Perm.sign f = Perm.sign (swap x (f x) * (swap x (f x) * f)) := by simp
    _ = -(-1) ^ #f.support :=
      if h1 : f (f x) = x then by
        have h : swap x (f x) * f = 1 := by
          simp only [mul_def, one_def]
          rw [hf.eq_swap_of_apply_apply_eq_self hx.1 

中文:
定理 是环.sign
  条件: {f : 置换 α} (hf : 是环 f)
  结论: sign f = -(-1) ^ #f.support
  证明: let ⟨x, hx⟩ := hf
  calc
    Perm.sign f = Perm.sign (swap x (f x) * (swap x (f x) * f)) := by simp
    _ = -(-1) ^ #f.support :=
      if h1 : f (f x) = x then by
        have h : swap x (f x) * f = 1 := by
          simp only [mul_def, one_def]
          rw [hf.eq_swap_of_apply_apply_eq_self hx.1 

Depends on / 依赖: Perm.sign, card_support_swap, eq_swap_of_apply_apply_eq_self, f.support, hf.eq_swap_of_apply_apply_eq_self, mul_def, one_def, sign_mul, sign_one, sign_swap, support, swap_apply_left, swap_swap
-/
theorem IsCycle.sign {f : Perm α} (hf : IsCycle f) : sign f = -(-1) ^ #f.support :=
  let ⟨x, hx⟩ := hf
  calc
    Perm.sign f = Perm.sign (swap x (f x) * (swap x (f x) * f)) := by simp
    _ = -(-1) ^ #f.support :=
      if h1 : f (f x) = x then by
        have h : swap x (f x) * f = 1 := by
          simp only [mul_def, one_def]
          rw [hf.eq_swap_of_apply_apply_eq_self hx.1 h1]; rw [swap_apply_left]; rw [swap_swap]
        rw [sign_mul]; rw [sign_swap hx.1.symm]; rw [h]; rw [sign_one]; rw [hf.eq_swap_of_apply_apply_eq_self hx.1 h1]; rw [card_support_swap hx.1.symm]
        rfl
      else by
        have h : #(swap x (f x) * f).support + 1 = #f.support := by
          rw [← insert_erase (mem_support.2 hx.1)]; rw [support_swap_mul_eq _ _ h1]; rw [card_insert_of_notMem (notMem_erase _ _)]; rw [sdiff_singleton_eq_erase]
        rw [sign_mul]; rw [sign_swap hx.1.symm]; rw [(hf.swap_mul hx.1 h1).sign]; rw [← h]
        simp only [mul_neg, neg_mul, one_mul, neg_neg, pow_add, pow_one, mul_one]
termination_by #f.support

/--
theorem `IsCycle.of_pow` / 定理 `IsCycle.of_pow`

English:
theorem IsCycle.of_pow
  given: {n : Nat} (h1 : IsCycle (f ^ n)) (h2 : f.support subseteq (f ^ n).support)
  proof: by
  have key : forall x : α, (f ^ n) x != x ↔ f x != x := by
    simp_rw [← mem_support, ← Finset.ext_iff]
    exact (support_pow_le _ n).antisymm h2
  obtain ⟨x, hx1, hx2⟩ := h1
  refine ⟨x, (key x).mp hx1, fun y hy => ?_⟩
  obtain ⟨i, _⟩ := hx2 ((key y).mpr hy)
  exact ⟨n * i, by rwa [zpow_mul]⟩

中文:
定理 是环.of_pow
  条件: {n : 自然数} (h1 : 是环 (f ^ n)) (h2 : f.support subseteq (f ^ n).support)
  证明: by
  have key : forall x : α, (f ^ n) x != x ↔ f x != x := by
    simp_rw [← mem_support, ← Finset.ext_iff]
    exact (support_pow_le _ n).antisymm h2
  obtain ⟨x, hx1, hx2⟩ := h1
  refine ⟨x, (key x).mp hx1, fun y hy => ?_⟩
  obtain ⟨i, _⟩ := hx2 ((key y).mpr hy)
  exact ⟨n * i, by rwa [zpow_mul]⟩

Depends on / 依赖: Finset, Finset.ext_iff, antisymm, ext_iff, mem_support, simp_rw, support_pow_le, zpow_mul
-/
theorem IsCycle.of_pow {n : Nat} (h1 : IsCycle (f ^ n)) (h2 : f.support subseteq (f ^ n).support) :
    IsCycle f := by
  have key : forall x : α, (f ^ n) x != x ↔ f x != x := by
    simp_rw [← mem_support, ← Finset.ext_iff]
    exact (support_pow_le _ n).antisymm h2
  obtain ⟨x, hx1, hx2⟩ := h1
  refine ⟨x, (key x).mp hx1, fun y hy => ?_⟩
  obtain ⟨i, _⟩ := hx2 ((key y).mpr hy)
  exact ⟨n * i, by rwa [zpow_mul]⟩

-- The lemma `support_zpow_le` is relevant. It means that `h2` is equivalent to
-- `σ.support = (σ ^ n).support`, as well as to `#σ.support ≤ #(σ ^ n).support`.
/--
theorem `IsCycle.of_zpow` / 定理 `IsCycle.of_zpow`

English:
theorem IsCycle.of_zpow
  given: {n : Int} (h1 : IsCycle (f ^ n)) (h2 : f.support subseteq (f ^ n).support)
  proof: by
  cases n
  · exact h1.of_pow h2
  · simp only [zpow_negSucc, Perm.support_inv] at h1 h2
    exact (inv_inv (f ^ _) ▸ h1.inv).of_pow h2

中文:
定理 是环.of_zpow
  条件: {n : 整数} (h1 : 是环 (f ^ n)) (h2 : f.support subseteq (f ^ n).support)
  证明: by
  cases n
  · exact h1.of_pow h2
  · simp only [zpow_negSucc, Perm.support_inv] at h1 h2
    exact (inv_inv (f ^ _) ▸ h1.inv).of_pow h2

Depends on / 依赖: Perm.support_inv, h1.inv, h1.of_pow, inv_inv, of_pow, support_inv, zpow_negSucc
-/
theorem IsCycle.of_zpow {n : Int} (h1 : IsCycle (f ^ n)) (h2 : f.support subseteq (f ^ n).support) :
    IsCycle f := by
  cases n
  · exact h1.of_pow h2
  · simp only [zpow_negSucc, Perm.support_inv] at h1 h2
    exact (inv_inv (f ^ _) ▸ h1.inv).of_pow h2

/--
theorem `nodup_of_pairwise_disjoint_cycles` / 定理 `nodup_of_pairwise_disjoint_cycles`

English:
theorem nodup_of_pairwise_disjoint_cycles
  statement: {l : List (Perm β)} (h1 : forall f in l, IsCycle f)
  proof: nodup_of_pairwise_disjoint (fun h => (h1 1 h).ne_one rfl) h2

中文:
定理 nodup_of_pairwise_disjoint_cycles
  结论: {l : 列表 (置换 β)} (h1 : 对任意 f in l, 是环 f)
  证明: nodup_of_pairwise_disjoint (fun h => (h1 1 h).ne_one rfl) h2

Depends on / 依赖: ne_one, nodup_of_pairwise_disjoint
-/
theorem nodup_of_pairwise_disjoint_cycles {l : List (Perm β)} (h1 : forall f in l, IsCycle f)
    (h2 : l.Pairwise Disjoint) : l.Nodup :=
  nodup_of_pairwise_disjoint (fun h => (h1 1 h).ne_one rfl) h2

/--
theorem `IsCycle.support_congr` / 定理 `IsCycle.support_congr`

English:
theorem IsCycle.support_congr
  statement: (hf : IsCycle f) (hg : IsCycle g) (h : f.support subseteq g.support)
  proof: by
  have : f.support = g.support := by
    refine le_antisymm h ?_
    intro z hz
    obtain ⟨x, hx, _⟩ := id hf
    have hx' : g x != x := by rwa [← h' x (mem_support.mpr hx)]
    obtain ⟨m, hm⟩ := hg.exists_pow_eq hx' (mem_support.mp hz)
    have h'' : forall x in f.support inter g.support, f x =

中文:
定理 是环.support_congr
  结论: (hf : 是环 f) (hg : 是环 g) (h : f.support subseteq g.support)
  证明: by
  have : f.support = g.support := by
    refine le_antisymm h ?_
    intro z hz
    obtain ⟨x, hx, _⟩ := id hf
    have hx' : g x != x := by rwa [← h' x (mem_support.mpr hx)]
    obtain ⟨m, hm⟩ := hg.exists_pow_eq hx' (mem_support.mp hz)
    have h'' : forall x in f.support inter g.support, f x =

Depends on / 依赖: Equiv.Perm.sup, exists_pow_eq, f.support, g.support, hg.exists_pow_eq, le_antisymm, mem_inter_of_mem, mem_of_mem_inter_left, mem_support, mem_support.mp, mem_support.mpr, pow_apply_mem_support, pow_eq_on_of_mem_support, support
-/
theorem IsCycle.support_congr (hf : IsCycle f) (hg : IsCycle g) (h : f.support subseteq g.support)
    (h' : forall x in f.support, f x = g x) : f = g := by
  have : f.support = g.support := by
    refine le_antisymm h ?_
    intro z hz
    obtain ⟨x, hx, _⟩ := id hf
    have hx' : g x != x := by rwa [← h' x (mem_support.mpr hx)]
    obtain ⟨m, hm⟩ := hg.exists_pow_eq hx' (mem_support.mp hz)
    have h'' : forall x in f.support inter g.support, f x = g x := by
      intro x hx
      exact h' x (mem_of_mem_inter_left hx)
    rwa [← hm, ←
      pow_eq_on_of_mem_support h'' _ x
        (mem_inter_of_mem (mem_support.mpr hx) (mem_support.mpr hx')),
      pow_apply_mem_support, mem_support]
  refine Equiv.Perm.support_congr h ?_
  simpa [← this] using h'

/--
theorem `IsCycle.eq_on_support_inter_nonempty_congr` / 定理 `IsCycle.eq_on_support_inter_nonempty_congr`

English:
theorem IsCycle.eq_on_support_inter_nonempty_congr
  statement: (hf : IsCycle f) (hg : IsCycle g)
  proof: by
  have hx'' : x in g.support := by rwa [mem_support, ← hx, ← mem_support]
  have : f.support subseteq g.support := by
    intro y hy
    obtain ⟨k, rfl⟩ := hf.exists_pow_eq (mem_support.mp hx') (mem_support.mp hy)
    rwa [pow_eq_on_of_mem_support h _ _ (mem_inter_of_mem hx' hx''), pow_apply_mem_

中文:
定理 是环.eq_on_support_inter_nonempty_congr
  结论: (hf : 是环 f) (hg : 是环 g)
  证明: by
  have hx'' : x in g.support := by rwa [mem_support, ← hx, ← mem_support]
  have : f.support subseteq g.support := by
    intro y hy
    obtain ⟨k, rfl⟩ := hf.exists_pow_eq (mem_support.mp hx') (mem_support.mp hy)
    rwa [pow_eq_on_of_mem_support h _ _ (mem_inter_of_mem hx' hx''), pow_apply_mem_

Depends on / 依赖: exists_pow_eq, f.support, g.support, hf.exists_pow_eq, hf.support_congr, inter_eq_left, inter_eq_left.mpr, mem_inter_of_mem, mem_support, mem_support.mp, pow_apply_mem_support, pow_eq_on_of_mem_support, subseteq, support, support_congr
-/
theorem IsCycle.eq_on_support_inter_nonempty_congr (hf : IsCycle f) (hg : IsCycle g)
    (h : forall x in f.support inter g.support, f x = g x)
    (hx : f x = g x) (hx' : x in f.support) : f = g := by
  have hx'' : x in g.support := by rwa [mem_support, ← hx, ← mem_support]
  have : f.support subseteq g.support := by
    intro y hy
    obtain ⟨k, rfl⟩ := hf.exists_pow_eq (mem_support.mp hx') (mem_support.mp hy)
    rwa [pow_eq_on_of_mem_support h _ _ (mem_inter_of_mem hx' hx''), pow_apply_mem_support]
  rw [inter_eq_left.mpr this] at h
  exact hf.support_congr hg this h

/--
theorem `IsCycle.support_pow_eq_iff` / 定理 `IsCycle.support_pow_eq_iff`

English:
theorem IsCycle.support_pow_eq_iff
  given: (hf : IsCycle f) {n : Nat}
  proof: by
  rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h H
    refine hf.ne_one ?_
    rw [← support_eq_empty_iff]; rw [← h]; rw [H]; rw [support_one]
  · intro H
    apply le_antisymm (support_pow_le _ n) _
    intro x hx
    contrapose H
    ext z
    by_cases hz : f z = z
    · rw [pow_appl

中文:
定理 是环.support_pow_eq_iff
  条件: (hf : 是环 f) {n : 自然数}
  证明: by
  rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h H
    refine hf.ne_one ?_
    rw [← support_eq_empty_iff]; rw [← h]; rw [H]; rw [support_one]
  · intro H
    apply le_antisymm (support_pow_le _ n) _
    intro x hx
    contrapose H
    ext z
    by_cases hz : f z = z
    · rw [pow_appl

Depends on / 依赖: Commute, Commute.pow_pow_self, contrapose, exists_pow_eq, hf.exists_pow_eq, hf.ne_one, injective, le_antisymm, mem_support, mem_support.mp, mul_apply, ne_one, one_apply, orderOf_dvd_iff_pow_eq_one, pow_apply_eq_self_of_apply_eq_self, pow_pow_self, support_eq_empty_iff, support_one, support_pow_le
-/
theorem IsCycle.support_pow_eq_iff (hf : IsCycle f) {n : Nat} :
    support (f ^ n) = support f ↔ ¬orderOf f ∣ n := by
  rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h H
    refine hf.ne_one ?_
    rw [← support_eq_empty_iff]; rw [← h]; rw [H]; rw [support_one]
  · intro H
    apply le_antisymm (support_pow_le _ n) _
    intro x hx
    contrapose H
    ext z
    by_cases hz : f z = z
    · rw [pow_apply_eq_self_of_apply_eq_self hz, one_apply]
    · obtain ⟨k, rfl⟩ := hf.exists_pow_eq hz (mem_support.mp hx)
      apply (f ^ k).injective
      rw [← mul_apply]; rw [(Commute.pow_pow_self _ _ _).eq]; rw [mul_apply]
      simpa using H

/--
theorem `IsCycle.support_pow_of_pos_of_lt_orderOf` / 定理 `IsCycle.support_pow_of_pos_of_lt_orderOf`

English:
theorem IsCycle.support_pow_of_pos_of_lt_orderOf
  statement: (hf : IsCycle f) {n : Nat} (npos : 0 < n)
  proof: hf.support_pow_eq_iff.2 Nat.not_dvd_of_pos_of_lt npos hn

中文:
定理 是环.support_pow_of_pos_of_lt_orderOf
  结论: (hf : 是环 f) {n : 自然数} (npos : 0 < n)
  证明: hf.support_pow_eq_iff.2 Nat.not_dvd_of_pos_of_lt npos hn

Depends on / 依赖: Nat.not_dvd_of_pos_of_lt, hf.support_pow_eq_iff, not_dvd_of_pos_of_lt, support_pow_eq_iff
-/
theorem IsCycle.support_pow_of_pos_of_lt_orderOf (hf : IsCycle f) {n : Nat} (npos : 0 < n)
    (hn : n < orderOf f) : (f ^ n).support = f.support :=
hf.support_pow_eq_iff.2 Nat.not_dvd_of_pos_of_lt npos hn

/--
theorem `IsCycle.pow_iff` / 定理 `IsCycle.pow_iff`

English:
theorem IsCycle.pow_iff
  given: [Finite β] {f : Perm β} (hf : IsCycle f) {n : Nat}
  proof: by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      have hr : support (f ^ n) = support f := by
        rw [hf.support_pow_eq_iff]
        rintro ⟨k, rfl⟩
        refine h.ne_one ?_
        simp [pow_mul, pow_orderOf_eq_one]
      have : orderOf (f ^ n) = orderOf f := by 

中文:
定理 是环.pow_iff
  条件: [有限 β] {f : 置换 β} (hf : 是环 f) {n : 自然数}
  证明: by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      have hr : support (f ^ n) = support f := by
        rw [hf.support_pow_eq_iff]
        rintro ⟨k, rfl⟩
        refine h.ne_one ?_
        simp [pow_mul, pow_orderOf_eq_one]
      have : orderOf (f ^ n) = orderOf f := by 

Depends on / 依赖: Nat.coprime_iff_gcd_eq_one, Nat.div_eq_self, Nat.gcd_comm, absurd, classical, coprime_iff_gcd_eq_one, div_eq_self, exists_pow_eq_self_of_coprime, gcd_comm, h.ne_one, h.orderOf, hf.orderOf, hf.support_pow_eq_iff, ne_one, nonempty_fintype, orderOf, orderOf_pos, orderOf_pow, pow_mul, pow_orderOf_eq_one
-/
theorem IsCycle.pow_iff [Finite β] {f : Perm β} (hf : IsCycle f) {n : Nat} :
    IsCycle (f ^ n) ↔ n.Coprime (orderOf f) := by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      have hr : support (f ^ n) = support f := by
        rw [hf.support_pow_eq_iff]
        rintro ⟨k, rfl⟩
        refine h.ne_one ?_
        simp [pow_mul, pow_orderOf_eq_one]
      have : orderOf (f ^ n) = orderOf f := by rw [h.orderOf, hr, hf.orderOf]
      rw [orderOf_pow]; rw [Nat.div_eq_self] at this
      rcases this with h | _
      · exact absurd h (orderOf_pos _).ne'
      · rwa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    · intro h
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
      have hf' : IsCycle ((f ^ n) ^ m) := by rwa [hm]
      refine hf'.of_pow fun x hx => ?_
      rw [hm]
      exact support_pow_le _ n hx

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
/--
theorem `IsCycle.pow_eq_one_iff` / 定理 `IsCycle.pow_eq_one_iff`

English:
theorem IsCycle.pow_eq_one_iff
  given: [Finite β] {f : Perm β} (hf : IsCycle f) {n : Nat}
  proof: by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := id hf
      exact ⟨x, hx, by simp [h]⟩
    · rintro ⟨x, hx, hx'⟩
      by_cases h : support (f ^ n) = support f
      · rw [← mem_support, ← h, mem_support] at hx
        contradiction
      · rw [hf

中文:
定理 是环.pow_eq_one_iff
  条件: [有限 β] {f : 置换 β} (hf : 是环 f) {n : 自然数}
  证明: by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := id hf
      exact ⟨x, hx, by simp [h]⟩
    · rintro ⟨x, hx, hx'⟩
      by_cases h : support (f ^ n) = support f
      · rw [← mem_support, ← h, mem_support] at hx
        contradiction
      · rw [hf

Depends on / 依赖: Classical, Classical.not_not, classical, hf.support_pow_eq_iff, mem_support, nonempty_fintype, not_not, one_pow, pow_mul, pow_orderOf_eq_one, support, support_pow_eq_iff
-/
theorem IsCycle.pow_eq_one_iff [Finite β] {f : Perm β} (hf : IsCycle f) {n : Nat} :
    f ^ n = 1 ↔ exists x, f x != x ∧ (f ^ n) x = x := by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := id hf
      exact ⟨x, hx, by simp [h]⟩
    · rintro ⟨x, hx, hx'⟩
      by_cases h : support (f ^ n) = support f
      · rw [← mem_support, ← h, mem_support] at hx
        contradiction
      · rw [hf.support_pow_eq_iff, Classical.not_not] at h
        obtain ⟨k, rfl⟩ := h
        rw [pow_mul]; rw [pow_orderOf_eq_one]; rw [one_pow]

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
/--
theorem `IsCycle.pow_eq_one_iff'` / 定理 `IsCycle.pow_eq_one_iff'`

English:
theorem IsCycle.pow_eq_one_iff'
  statement: [Finite β] {f : Perm β} (hf : IsCycle f) {n : Nat} {x : β}
  proof: ⟨fun h => DFunLike.congr_fun h x, fun h => hf.pow_eq_one_iff.2 ⟨x, hx, h⟩⟩

中文:
定理 是环.pow_eq_one_iff'
  结论: [有限 β] {f : 置换 β} (hf : 是环 f) {n : 自然数} {x : β}
  证明: ⟨fun h => DFunLike.congr_fun h x, fun h => hf.pow_eq_one_iff.2 ⟨x, hx, h⟩⟩

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, hf.pow_eq_one_iff, pow_eq_one_iff
-/
theorem IsCycle.pow_eq_one_iff' [Finite β] {f : Perm β} (hf : IsCycle f) {n : Nat} {x : β}
    (hx : f x != x) : f ^ n = 1 ↔ (f ^ n) x = x :=
  ⟨fun h => DFunLike.congr_fun h x, fun h => hf.pow_eq_one_iff.2 ⟨x, hx, h⟩⟩

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
/--
theorem `IsCycle.pow_eq_one_iff''` / 定理 `IsCycle.pow_eq_one_iff''`

English:
theorem IsCycle.pow_eq_one_iff''
  given: [Finite β] {f : Perm β} (hf : IsCycle f) {n : Nat}
  proof: ⟨fun h _ hx => (hf.pow_eq_one_iff' hx).1 h, fun h =>
    let ⟨_, hx, _⟩ := id hf
    (hf.pow_eq_one_iff' hx).2 (h _ hx)⟩

中文:
定理 是环.pow_eq_one_iff''
  条件: [有限 β] {f : 置换 β} (hf : 是环 f) {n : 自然数}
  证明: ⟨fun h _ hx => (hf.pow_eq_one_iff' hx).1 h, fun h =>
    let ⟨_, hx, _⟩ := id hf
    (hf.pow_eq_one_iff' hx).2 (h _ hx)⟩

Depends on / 依赖: hf.pow_eq_one_iff, pow_eq_one_iff
-/
theorem IsCycle.pow_eq_one_iff'' [Finite β] {f : Perm β} (hf : IsCycle f) {n : Nat} :
    f ^ n = 1 ↔ forall x, f x != x -> (f ^ n) x = x :=
  ⟨fun h _ hx => (hf.pow_eq_one_iff' hx).1 h, fun h =>
    let ⟨_, hx, _⟩ := id hf
    (hf.pow_eq_one_iff' hx).2 (h _ hx)⟩

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
/--
theorem `IsCycle.pow_eq_pow_iff` / 定理 `IsCycle.pow_eq_pow_iff`

English:
theorem IsCycle.pow_eq_pow_iff
  given: [Finite β] {f : Perm β} (hf : IsCycle f) {a b : Nat}
  proof: by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := id hf
      exact ⟨x, hx, by simp [h]⟩
    · rintro ⟨x, hx, hx'⟩
      wlog hab : a <= b generalizing a b
      · exact (this hx'.symm (le_of_not_ge hab)).symm
      suffices f ^ (b - a) = 1 by
     

中文:
定理 是环.pow_eq_pow_iff
  条件: [有限 β] {f : 置换 β} (hf : 是环 f) {a b : 自然数}
  证明: by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := id hf
      exact ⟨x, hx, by simp [h]⟩
    · rintro ⟨x, hx, hx'⟩
      wlog hab : a <= b generalizing a b
      · exact (this hx'.symm (le_of_not_ge hab)).symm
      suffices f ^ (b - a) = 1 by
     

Depends on / 依赖: Equiv.Perm.zpow_apply_comm, classical, f.support, generalizing, hf.pow_eq_one_iff, le_of_not_ge, mem_support, mem_support.mp, mul_inv_eq_one, nonempty_fintype, pow_eq_one_iff, pow_sub, support, zpow_apply_comm
-/
theorem IsCycle.pow_eq_pow_iff [Finite β] {f : Perm β} (hf : IsCycle f) {a b : Nat} :
    f ^ a = f ^ b ↔ exists x, f x != x ∧ (f ^ a) x = (f ^ b) x := by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := id hf
      exact ⟨x, hx, by simp [h]⟩
    · rintro ⟨x, hx, hx'⟩
      wlog hab : a <= b generalizing a b
      · exact (this hx'.symm (le_of_not_ge hab)).symm
      suffices f ^ (b - a) = 1 by
        rw [pow_sub _ hab]; rw [mul_inv_eq_one] at this
        rw [this]
      rw [hf.pow_eq_one_iff]
      by_cases hfa : (f ^ a) x in f.support
      · refine ⟨(f ^ a) x, mem_support.mp hfa, ?_⟩
        simp [pow_sub _ hab, ← hx']
      · have h := @Equiv.Perm.zpow_apply_comm _ f 1 a x
        simp only [zpow_one, zpow_natCast] at h
        rw [notMem_support]; rw [h]; rw [Function.Injective.eq_iff (f ^ a).injective] at hfa
        contradiction

/--
theorem `IsCycle.isCycle_pow_pos_of_lt_prime_order` / 定理 `IsCycle.isCycle_pow_pos_of_lt_prime_order`

English:
theorem IsCycle.isCycle_pow_pos_of_lt_prime_order
  statement: [Finite β] {f : Perm β} (hf : IsCycle f)
  proof: by
  cases nonempty_fintype β
  have : n.Coprime (orderOf f) := by
    refine Nat.Coprime.symm ?_
    rw [Nat.Prime.coprime_iff_not_dvd hf']
    exact Nat.not_dvd_of_pos_of_lt hn hn'
  exact (pow_iff hf).mpr this

中文:
定理 是环.isCycle_pow_pos_of_lt_prime_order
  结论: [有限 β] {f : 置换 β} (hf : 是环 f)
  证明: by
  cases nonempty_fintype β
  have : n.Coprime (orderOf f) := by
    refine Nat.Coprime.symm ?_
    rw [Nat.Prime.coprime_iff_not_dvd hf']
    exact Nat.not_dvd_of_pos_of_lt hn hn'
  exact (pow_iff hf).mpr this

Depends on / 依赖: Coprime, Nat.Coprime.symm, Nat.Prime.coprime_iff_not_dvd, Nat.not_dvd_of_pos_of_lt, coprime_iff_not_dvd, n.Coprime, nonempty_fintype, not_dvd_of_pos_of_lt, orderOf, pow_iff
-/
theorem IsCycle.isCycle_pow_pos_of_lt_prime_order [Finite β] {f : Perm β} (hf : IsCycle f)
    (hf' : (orderOf f).Prime) (n : Nat) (hn : 0 < n) (hn' : n < orderOf f) : IsCycle (f ^ n) := by
  cases nonempty_fintype β
  have : n.Coprime (orderOf f) := by
    refine Nat.Coprime.symm ?_
    rw [Nat.Prime.coprime_iff_not_dvd hf']
    exact Nat.not_dvd_of_pos_of_lt hn hn'
  exact (pow_iff hf).mpr this

end IsCycle

open Equiv

/--
theorem `_root_.Int.addLeft_one_isCycle` / 定理 `_root_.Int.addLeft_one_isCycle`

English:
theorem _root_.Int.addLeft_one_isCycle
  statement: (Equiv.addLeft 1 : Perm Int).IsCycle
  proof: ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩

中文:
定理 _root_.整数.addLeft_one_isCycle
  结论: (等价.addLeft 1 : 置换 整数).是环
  证明: ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩

Depends on / 依赖: one_ne_zero
-/
theorem _root_.Int.addLeft_one_isCycle : (Equiv.addLeft 1 : Perm Int).IsCycle :=
  ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩

/--
theorem `_root_.Int.addRight_one_isCycle` / 定理 `_root_.Int.addRight_one_isCycle`

English:
theorem _root_.Int.addRight_one_isCycle
  statement: (Equiv.addRight 1 : Perm Int).IsCycle
  proof: ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩

中文:
定理 _root_.整数.addRight_one_isCycle
  结论: (等价.addRight 1 : 置换 整数).是环
  证明: ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩

Depends on / 依赖: one_ne_zero
-/
theorem _root_.Int.addRight_one_isCycle : (Equiv.addRight 1 : Perm Int).IsCycle :=
  ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩

section Conjugation

variable [Fintype α] [DecidableEq α] {σ τ : Perm α}

/--
theorem `IsCycle.isConj` / 定理 `IsCycle.isConj`

English:
theorem IsCycle.isConj
  given: (hσ : IsCycle σ) (hτ : IsCycle τ) (h : #σ.support = #τ.support)
  proof: by
  refine
    isConj_of_support_equiv
      (hσ.zpowersEquivSupport.symm.trans <|
        (zpowersEquivZPowers <| by rw [hσ.orderOf, h, hτ.orderOf]).trans hτ.zpowersEquivSupport)
      ?_
  intro x hx
  simp only [Equiv.trans_apply]
  obtain ⟨n, rfl⟩ := hσ.exists_pow_eq (Classical.choose_spec hσ).

中文:
定理 是环.isConj
  条件: (hσ : 是环 σ) (hτ : 是环 τ) (h : #σ.support = #τ.support)
  证明: by
  refine
    isConj_of_support_equiv
      (hσ.zpowersEquivSupport.symm.trans <|
        (zpowersEquivZPowers <| by rw [hσ.orderOf, h, hτ.orderOf]).trans hτ.zpowersEquivSupport)
      ?_
  intro x hx
  simp only [Equiv.trans_apply]
  obtain ⟨n, rfl⟩ := hσ.exists_pow_eq (Classical.choose_spec hσ).

Depends on / 依赖: Classical, Classical.choose_spec, Equiv.trans_apply, Perm.mul_apply, choose_spec, exists_pow_eq, isConj_of_support_equiv, mem_support, mul_apply, orderOf, pow_succ, trans_apply, zpowersEquivSupport, zpowersEquivSupport.symm.trans, zpowersEquivZPowers
-/
theorem IsCycle.isConj (hσ : IsCycle σ) (hτ : IsCycle τ) (h : #σ.support = #τ.support) :
    IsConj σ τ := by
  refine
    isConj_of_support_equiv
      (hσ.zpowersEquivSupport.symm.trans <|
        (zpowersEquivZPowers <| by rw [hσ.orderOf, h, hτ.orderOf]).trans hτ.zpowersEquivSupport)
      ?_
  intro x hx
  simp only [Equiv.trans_apply]
  obtain ⟨n, rfl⟩ := hσ.exists_pow_eq (Classical.choose_spec hσ).1 (mem_support.1 hx)
  simp [← Perm.mul_apply, ← pow_succ']

/--
theorem `IsCycle.isConj_iff` / 定理 `IsCycle.isConj_iff`

English:
theorem IsCycle.isConj_iff
  given: (hσ : IsCycle σ) (hτ : IsCycle τ)
  proof: by
    obtain ⟨π, rfl⟩ := (_root_.isConj_iff).1 h
    exact card_support_conj.symm
  mpr := hσ.isConj hτ

中文:
定理 是环.isConj_iff
  条件: (hσ : 是环 σ) (hτ : 是环 τ)
  证明: by
    obtain ⟨π, rfl⟩ := (_root_.isConj_iff).1 h
    exact card_support_conj.symm
  mpr := hσ.isConj hτ

Depends on / 依赖: _root_, _root_.isConj_iff, card_support_conj, card_support_conj.symm, isConj, isConj_iff
-/
theorem IsCycle.isConj_iff (hσ : IsCycle σ) (hτ : IsCycle τ) :
    IsConj σ τ ↔ #σ.support = #τ.support where
  mp h := by
    obtain ⟨π, rfl⟩ := (_root_.isConj_iff).1 h
    exact card_support_conj.symm
  mpr := hσ.isConj hτ

end Conjugation

/-! ### `IsCycleOn` -/

section IsCycleOn

variable {f g : Perm α} {s t : Set α} {a b x y : α}

/--
Definition of `IsCycleOn` / `IsCycleOn` 的定义

English:
definition IsCycleOn
  signature: (f : Perm α) (s : Set α)
  body: Set.BijOn f s s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> f.SameCycle x y

@[simp]

中文:
定义 IsCycleOn
  签名: (f : 置换 α) (s : 集合 α)
  定义体: Set.BijOn f s s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> f.SameCycle x y

@[simp]

Depends on / 依赖: SameCycle, Set.BijOn, f.SameCycle
-/
def IsCycleOn (f : Perm α) (s : Set α) : Prop :=
  Set.BijOn f s s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> f.SameCycle x y

@[simp]
/--
theorem `isCycleOn_empty` / 定理 `isCycleOn_empty`

English:
theorem isCycleOn_empty
  statement: f.IsCycleOn ∅
  proof: by simp [IsCycleOn]

@[simp]

中文:
定理 isCycleOn_empty
  结论: f.IsCycleOn ∅
  证明: by simp [IsCycleOn]

@[simp]

Depends on / 依赖: IsCycleOn
-/
theorem isCycleOn_empty : f.IsCycleOn ∅ := by simp [IsCycleOn]

@[simp]
/--
theorem `isCycleOn_one` / 定理 `isCycleOn_one`

English:
theorem isCycleOn_one
  statement: (1 : Perm α).IsCycleOn s ↔ s.Subsingleton
  proof: by
  simp [IsCycleOn, Set.bijOn_id, Set.Subsingleton]

alias ⟨IsCycleOn.subsingleton, _root_.Set.Subsingleton.isCycleOn_one⟩ := isCycleOn_one

@[simp]

中文:
定理 isCycleOn_one
  结论: (1 : 置换 α).IsCycleOn s ↔ s.子单例
  证明: by
  simp [IsCycleOn, Set.bijOn_id, Set.Subsingleton]

alias ⟨IsCycleOn.subsingleton, _root_.Set.Subsingleton.isCycleOn_one⟩ := isCycleOn_one

@[simp]

Depends on / 依赖: IsCycleOn, Set.Subsingleton, Set.bijOn_id, Subsingleton, bijOn_id
-/
theorem isCycleOn_one : (1 : Perm α).IsCycleOn s ↔ s.Subsingleton := by
  simp [IsCycleOn, Set.bijOn_id, Set.Subsingleton]

alias ⟨IsCycleOn.subsingleton, _root_.Set.Subsingleton.isCycleOn_one⟩ := isCycleOn_one

@[simp]
/--
theorem `isCycleOn_singleton` / 定理 `isCycleOn_singleton`

English:
theorem isCycleOn_singleton
  statement: f.IsCycleOn {a} ↔ f a = a
  proof: by simp [IsCycleOn, SameCycle.rfl]

中文:
定理 isCycleOn_singleton
  结论: f.IsCycleOn {a} ↔ f a = a
  证明: by simp [IsCycleOn, SameCycle.rfl]

Depends on / 依赖: IsCycleOn, SameCycle, SameCycle.rfl
-/
theorem isCycleOn_singleton : f.IsCycleOn {a} ↔ f a = a := by simp [IsCycleOn, SameCycle.rfl]

/--
theorem `isCycleOn_of_subsingleton` / 定理 `isCycleOn_of_subsingleton`

English:
theorem isCycleOn_of_subsingleton
  given: [Subsingleton α] (f : Perm α) (s : Set α)
  statement: f.IsCycleOn s
  proof: ⟨s.bijOn_of_subsingleton _, fun x _ y _ => (Subsingleton.elim x y).sameCycle _⟩

@[simp]

中文:
定理 isCycleOn_of_subsingleton
  条件: [子单例 α] (f : 置换 α) (s : 集合 α)
  结论: f.IsCycleOn s
  证明: ⟨s.bijOn_of_subsingleton _, fun x _ y _ => (Subsingleton.elim x y).sameCycle _⟩

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, bijOn_of_subsingleton, s.bijOn_of_subsingleton, sameCycle
-/
theorem isCycleOn_of_subsingleton [Subsingleton α] (f : Perm α) (s : Set α) : f.IsCycleOn s :=
  ⟨s.bijOn_of_subsingleton _, fun x _ y _ => (Subsingleton.elim x y).sameCycle _⟩

@[simp]
/--
theorem `isCycleOn_inv` / 定理 `isCycleOn_inv`

English:
theorem isCycleOn_inv
  statement: f⁻¹.IsCycleOn s ↔ f.IsCycleOn s
  proof: by
  simp only [IsCycleOn, sameCycle_inv, and_congr_left_iff]
  exact fun _ => ⟨fun h => Set.BijOn.perm_inv h, fun h => Set.BijOn.perm_inv h⟩

alias ⟨IsCycleOn.of_inv, IsCycleOn.inv⟩ := isCycleOn_inv

中文:
定理 isCycleOn_inv
  结论: f⁻¹.IsCycleOn s ↔ f.IsCycleOn s
  证明: by
  simp only [IsCycleOn, sameCycle_inv, and_congr_left_iff]
  exact fun _ => ⟨fun h => Set.BijOn.perm_inv h, fun h => Set.BijOn.perm_inv h⟩

alias ⟨IsCycleOn.of_inv, IsCycleOn.inv⟩ := isCycleOn_inv

Depends on / 依赖: IsCycleOn, Set.BijOn.perm_inv, and_congr_left_iff, perm_inv, sameCycle_inv
-/
theorem isCycleOn_inv : f⁻¹.IsCycleOn s ↔ f.IsCycleOn s := by
  simp only [IsCycleOn, sameCycle_inv, and_congr_left_iff]
  exact fun _ => ⟨fun h => Set.BijOn.perm_inv h, fun h => Set.BijOn.perm_inv h⟩

alias ⟨IsCycleOn.of_inv, IsCycleOn.inv⟩ := isCycleOn_inv

/--
theorem `IsCycleOn.conj` / 定理 `IsCycleOn.conj`

English:
theorem IsCycleOn.conj
  given: (h : f.IsCycleOn s)
  statement: (g * f * g⁻¹).IsCycleOn ((g : Perm α) '' s)
  proof: ⟨(g.bijOn_image.comp h.1).comp g.bijOn_symm_image, fun x hx y hy => by
    rw [Equiv.image_eq_preimage_symm] at hx hy
    convert! Equiv.Perm.SameCycle.conj (h.2 hx hy) (g := g) <;> simp⟩

中文:
定理 IsCycleOn.conj
  条件: (h : f.IsCycleOn s)
  结论: (g * f * g⁻¹).IsCycleOn ((g : 置换 α) '' s)
  证明: ⟨(g.bijOn_image.comp h.1).comp g.bijOn_symm_image, fun x hx y hy => by
    rw [Equiv.image_eq_preimage_symm] at hx hy
    convert! Equiv.Perm.SameCycle.conj (h.2 hx hy) (g := g) <;> simp⟩

Depends on / 依赖: Equiv.Perm.SameCycle.conj, Equiv.image_eq_preimage_symm, SameCycle, bijOn_image, bijOn_symm_image, convert, g.bijOn_image.comp, g.bijOn_symm_image, image_eq_preimage_symm
-/
theorem IsCycleOn.conj (h : f.IsCycleOn s) : (g * f * g⁻¹).IsCycleOn ((g : Perm α) '' s) :=
  ⟨(g.bijOn_image.comp h.1).comp g.bijOn_symm_image, fun x hx y hy => by
    rw [Equiv.image_eq_preimage_symm] at hx hy
    convert! Equiv.Perm.SameCycle.conj (h.2 hx hy) (g := g) <;> simp⟩

/--
theorem `isCycleOn_swap` / 定理 `isCycleOn_swap`

English:
theorem isCycleOn_swap
  given: [DecidableEq α] (hab : a != b)
  statement: (swap a b).IsCycleOn {a, b}
  proof: ⟨bijOn_swap (by simp) (by simp), fun x hx y hy => by
    rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff] at hx hy
    obtain rfl | rfl := hx <;> obtain rfl | rfl := hy
    · exact ⟨0, by rw [zpow_zero, coe_one, id]⟩
    · exact ⟨1, by rw [zpow_one, swap_apply_left]⟩
    · exact ⟨1, by rw [zpow_o

中文:
定理 isCycleOn_swap
  条件: [DecidableEq α] (hab : a != b)
  结论: (swap a b).IsCycleOn {a, b}
  证明: ⟨bijOn_swap (by simp) (by simp), fun x hx y hy => by
    rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff] at hx hy
    obtain rfl | rfl := hx <;> obtain rfl | rfl := hy
    · exact ⟨0, by rw [zpow_zero, coe_one, id]⟩
    · exact ⟨1, by rw [zpow_one, swap_apply_left]⟩
    · exact ⟨1, by rw [zpow_o

Depends on / 依赖: Set.mem_insert_iff, Set.mem_singleton_iff, bijOn_swap, coe_one, mem_insert_iff, mem_singleton_iff, swap_apply_left, swap_apply_right, zpow_one, zpow_zero
-/
theorem isCycleOn_swap [DecidableEq α] (hab : a != b) : (swap a b).IsCycleOn {a, b} :=
  ⟨bijOn_swap (by simp) (by simp), fun x hx y hy => by
    rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff] at hx hy
    obtain rfl | rfl := hx <;> obtain rfl | rfl := hy
    · exact ⟨0, by rw [zpow_zero, coe_one, id]⟩
    · exact ⟨1, by rw [zpow_one, swap_apply_left]⟩
    · exact ⟨1, by rw [zpow_one, swap_apply_right]⟩
    · exact ⟨0, by rw [zpow_zero, coe_one, id]⟩⟩

/--
theorem `IsCycleOn.apply_ne` / 定理 `IsCycleOn.apply_ne`

English:
theorem IsCycleOn.apply_ne
  given: (hf : f.IsCycleOn s) (hs : s.Nontrivial) (ha : a in s)
  proof: by
  obtain ⟨b, hb, hba⟩ := hs.exists_ne a
  obtain ⟨n, rfl⟩ := hf.2 ha hb
  exact fun h => hba (IsFixedPt.perm_zpow h n)

中文:
定理 IsCycleOn.apply_ne
  条件: (hf : f.IsCycleOn s) (hs : s.非平凡) (ha : a in s)
  证明: by
  obtain ⟨b, hb, hba⟩ := hs.exists_ne a
  obtain ⟨n, rfl⟩ := hf.2 ha hb
  exact fun h => hba (IsFixedPt.perm_zpow h n)
-/
protected theorem IsCycleOn.apply_ne (hf : f.IsCycleOn s) (hs : s.Nontrivial) (ha : a in s) :
    f a != a := by
  obtain ⟨b, hb, hba⟩ := hs.exists_ne a
  obtain ⟨n, rfl⟩ := hf.2 ha hb
  exact fun h => hba (IsFixedPt.perm_zpow h n)

/--
theorem `IsCycle.isCycleOn` / 定理 `IsCycle.isCycleOn`

English:
theorem IsCycle.isCycleOn
  given: (hf : f.IsCycle)
  statement: f.IsCycleOn { x | f x != x }
  proof: ⟨f.bijOn fun _ => f.apply_eq_iff_eq.not, fun _ ha _ => hf.sameCycle ha⟩

中文:
定理 是环.isCycleOn
  条件: (hf : f.是环)
  结论: f.IsCycleOn { x | f x != x }
  证明: ⟨f.bijOn fun _ => f.apply_eq_iff_eq.not, fun _ ha _ => hf.sameCycle ha⟩
-/
protected theorem IsCycle.isCycleOn (hf : f.IsCycle) : f.IsCycleOn { x | f x != x } :=
  ⟨f.bijOn fun _ => f.apply_eq_iff_eq.not, fun _ ha _ => hf.sameCycle ha⟩

/--
theorem `isCycle_iff_exists_isCycleOn` / 定理 `isCycle_iff_exists_isCycleOn`

English:
theorem isCycle_iff_exists_isCycleOn
  proof: by
  refine ⟨fun hf => ⟨{ x | f x != x }, ?_, hf.isCycleOn, fun _ => id⟩, ?_⟩
  · obtain ⟨a, ha⟩ := hf
    exact ⟨f a, f.injective.ne ha.1, a, ha.1, ha.1⟩
  · rintro ⟨s, hs, hf, hsf⟩
    obtain ⟨a, ha⟩ := hs.nonempty
exact ⟨a, hf.apply_ne hs ha, fun b hb => hf.2 ha hsf hb⟩

中文:
定理 isCycle_iff_存在_isCycleOn
  证明: by
  refine ⟨fun hf => ⟨{ x | f x != x }, ?_, hf.isCycleOn, fun _ => id⟩, ?_⟩
  · obtain ⟨a, ha⟩ := hf
    exact ⟨f a, f.injective.ne ha.1, a, ha.1, ha.1⟩
  · rintro ⟨s, hs, hf, hsf⟩
    obtain ⟨a, ha⟩ := hs.nonempty
exact ⟨a, hf.apply_ne hs ha, fun b hb => hf.2 ha hsf hb⟩

Depends on / 依赖: apply_ne, f.injective.ne, hf.apply_ne, hf.isCycleOn, hs.nonempty, injective, isCycleOn, nonempty
-/
theorem isCycle_iff_exists_isCycleOn :
    f.IsCycle ↔ exists s : Set α, s.Nontrivial ∧ f.IsCycleOn s ∧ forall ⦃x⦄, ¬IsFixedPt f x -> x in s := by
  refine ⟨fun hf => ⟨{ x | f x != x }, ?_, hf.isCycleOn, fun _ => id⟩, ?_⟩
  · obtain ⟨a, ha⟩ := hf
    exact ⟨f a, f.injective.ne ha.1, a, ha.1, ha.1⟩
  · rintro ⟨s, hs, hf, hsf⟩
    obtain ⟨a, ha⟩ := hs.nonempty
exact ⟨a, hf.apply_ne hs ha, fun b hb => hf.2 ha hsf hb⟩

/--
theorem `IsCycleOn.apply_mem_iff` / 定理 `IsCycleOn.apply_mem_iff`

English:
theorem IsCycleOn.apply_mem_iff
  given: (hf : f.IsCycleOn s)
  statement: f x in s ↔ x in s
  proof: ⟨fun hx => by simpa using hf.1.perm_inv.1 hx, fun hx => hf.1.mapsTo hx⟩

中文:
定理 IsCycleOn.apply_mem_iff
  条件: (hf : f.IsCycleOn s)
  结论: f x in s ↔ x in s
  证明: ⟨fun hx => by simpa using hf.1.perm_inv.1 hx, fun hx => hf.1.mapsTo hx⟩

Depends on / 依赖: mapsTo, perm_inv
-/
theorem IsCycleOn.apply_mem_iff (hf : f.IsCycleOn s) : f x in s ↔ x in s :=
  ⟨fun hx => by simpa using hf.1.perm_inv.1 hx, fun hx => hf.1.mapsTo hx⟩

/--
theorem `IsCycleOn.isCycle_subtypePerm` / 定理 `IsCycleOn.isCycle_subtypePerm`

English:
theorem IsCycleOn.isCycle_subtypePerm
  given: (hf : f.IsCycleOn s) (hs : s.Nontrivial)
  proof: by
  obtain ⟨a, ha⟩ := hs.nonempty
  exact
    ⟨⟨a, ha⟩, ne_of_apply_ne ((↑) : s -> α) (hf.apply_ne hs ha), fun b _ =>
      (hf.2 (⟨a, ha⟩ : s).2 b.2).subtypePerm⟩

中文:
定理 IsCycleOn.isCycle_subtypePerm
  条件: (hf : f.IsCycleOn s) (hs : s.非平凡)
  证明: by
  obtain ⟨a, ha⟩ := hs.nonempty
  exact
    ⟨⟨a, ha⟩, ne_of_apply_ne ((↑) : s -> α) (hf.apply_ne hs ha), fun b _ =>
      (hf.2 (⟨a, ha⟩ : s).2 b.2).subtypePerm⟩

Depends on / 依赖: apply_ne, hf.apply_ne, hs.nonempty, ne_of_apply_ne, nonempty, subtypePerm
-/
theorem IsCycleOn.isCycle_subtypePerm (hf : f.IsCycleOn s) (hs : s.Nontrivial) :
    (f.subtypePerm fun _ => hf.apply_mem_iff : Perm s).IsCycle := by
  obtain ⟨a, ha⟩ := hs.nonempty
  exact
    ⟨⟨a, ha⟩, ne_of_apply_ne ((↑) : s -> α) (hf.apply_ne hs ha), fun b _ =>
      (hf.2 (⟨a, ha⟩ : s).2 b.2).subtypePerm⟩

/--
theorem `IsCycleOn.subtypePerm` / 定理 `IsCycleOn.subtypePerm`

English:
theorem IsCycleOn.subtypePerm
  given: (hf : f.IsCycleOn s)
  proof: by
  obtain hs | hs := s.subsingleton_or_nontrivial
  · have := hs.coe_sort
    exact isCycleOn_of_subsingleton _ _
  convert! (hf.isCycle_subtypePerm hs).isCycleOn
  rw [eq_comm]; rw [Set.eq_univ_iff_forall]
  exact fun x => ne_of_apply_ne ((↑) : s -> α) (hf.apply_ne hs x.2)

中文:
定理 IsCycleOn.subtypePerm
  条件: (hf : f.IsCycleOn s)
  证明: by
  obtain hs | hs := s.subsingleton_or_nontrivial
  · have := hs.coe_sort
    exact isCycleOn_of_subsingleton _ _
  convert! (hf.isCycle_subtypePerm hs).isCycleOn
  rw [eq_comm]; rw [Set.eq_univ_iff_forall]
  exact fun x => ne_of_apply_ne ((↑) : s -> α) (hf.apply_ne hs x.2)
-/
protected theorem IsCycleOn.subtypePerm (hf : f.IsCycleOn s) :
    (f.subtypePerm fun _ => hf.apply_mem_iff : Perm s).IsCycleOn _root_.Set.univ := by
  obtain hs | hs := s.subsingleton_or_nontrivial
  · have := hs.coe_sort
    exact isCycleOn_of_subsingleton _ _
  convert! (hf.isCycle_subtypePerm hs).isCycleOn
  rw [eq_comm]; rw [Set.eq_univ_iff_forall]
  exact fun x => ne_of_apply_ne ((↑) : s -> α) (hf.apply_ne hs x.2)

-- TODO: Theory of order of an element under an action
/--
theorem `IsCycleOn.pow_apply_eq` / 定理 `IsCycleOn.pow_apply_eq`

English:
theorem IsCycleOn.pow_apply_eq
  given: {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s) {n : Nat}
  proof: by
  obtain rfl | hs := Finset.eq_singleton_or_nontrivial ha
  · rw [coe_singleton, isCycleOn_singleton] at hf
    simpa using! IsFixedPt.iterate hf n
  classical
    have h (x : s) : ¬f x = x := hf.apply_ne hs x.2
    have := (hf.isCycle_subtypePerm hs).orderOf
    simp only [coe_sort_coe, support_

中文:
定理 IsCycleOn.pow_apply_eq
  条件: {s : 有限集 α} (hf : f.IsCycleOn s) (ha : a in s) {n : 自然数}
  证明: by
  obtain rfl | hs := Finset.eq_singleton_or_nontrivial ha
  · rw [coe_singleton, isCycleOn_singleton] at hf
    simpa using! IsFixedPt.iterate hf n
  classical
    have h (x : s) : ¬f x = x := hf.apply_ne hs x.2
    have := (hf.isCycle_subtypePerm hs).orderOf
    simp only [coe_sort_coe, support_

Depends on / 依赖: Finset, Finset.eq_singleton_or_nontrivial, IsFixedPt, IsFixedPt.iterate, apply_ne, card_attach, classical, coe_singleton, coe_sort_coe, eq_singleton_or_nontrivial, filter_true_of_mem, hf.apply_ne, hf.isCycle_subtypePerm, imp_self, implies_true, isCycleOn_singleton, isCycle_subtypePerm, iterate, mem_attach, ne_eq
-/
theorem IsCycleOn.pow_apply_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s) {n : Nat} :
    (f ^ n) a = a ↔ #s ∣ n := by
  obtain rfl | hs := Finset.eq_singleton_or_nontrivial ha
  · rw [coe_singleton, isCycleOn_singleton] at hf
    simpa using! IsFixedPt.iterate hf n
  classical
    have h (x : s) : ¬f x = x := hf.apply_ne hs x.2
    have := (hf.isCycle_subtypePerm hs).orderOf
    simp only [coe_sort_coe, support_subtypePerm, ne_eq, h, not_false_eq_true, univ_eq_attach,
      mem_attach, imp_self, implies_true, filter_true_of_mem, card_attach] at this
    rw [← this]; rw [orderOf_dvd_iff_pow_eq_one]; rw [(hf.isCycle_subtypePerm hs).pow_eq_one_iff'
        (ne_of_apply_ne ((↑) : s -> α) <| hf.apply_ne hs (⟨a]; rw [ha⟩ : s).2)]
    simp [-SetLike.coe_sort_coe]

/--
theorem `IsCycleOn.zpow_apply_eq` / 定理 `IsCycleOn.zpow_apply_eq`

English:
theorem IsCycleOn.zpow_apply_eq
  given: {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s)

中文:
定理 IsCycleOn.zpow_apply_eq
  条件: {s : 有限集 α} (hf : f.IsCycleOn s) (ha : a in s)
-/
theorem IsCycleOn.zpow_apply_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s) :
    forall {n : Int}, (f ^ n) a = a ↔ (#s : Int) ∣ n
  | Int.ofNat _ => (hf.pow_apply_eq ha).trans Int.natCast_dvd_natCast.symm
  | Int.negSucc n => by
    rw [zpow_negSucc]; rw [← inv_pow]
    exact (hf.inv.pow_apply_eq ha).trans (dvd_neg.trans Int.natCast_dvd_natCast).symm

/--
theorem `IsCycleOn.pow_apply_eq_pow_apply` / 定理 `IsCycleOn.pow_apply_eq_pow_apply`

English:
theorem IsCycleOn.pow_apply_eq_pow_apply
  statement: {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s)
  proof: by
  rw [Nat.modEq_iff_dvd]; rw [← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_symm_apply, eq_comm]

中文:
定理 IsCycleOn.pow_apply_eq_pow_apply
  结论: {s : 有限集 α} (hf : f.IsCycleOn s) (ha : a in s)
  证明: by
  rw [Nat.modEq_iff_dvd]; rw [← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_symm_apply, eq_comm]

Depends on / 依赖: Nat.modEq_iff_dvd, eq_comm, eq_symm_apply, hf.zpow_apply_eq, modEq_iff_dvd, sub_eq_neg_add, zpow_add, zpow_apply_eq
-/
theorem IsCycleOn.pow_apply_eq_pow_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s)
    {m n : Nat} : (f ^ m) a = (f ^ n) a ↔ m ≡ n [MOD #s] := by
  rw [Nat.modEq_iff_dvd]; rw [← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_symm_apply, eq_comm]

/--
theorem `IsCycleOn.zpow_apply_eq_zpow_apply` / 定理 `IsCycleOn.zpow_apply_eq_zpow_apply`

English:
theorem IsCycleOn.zpow_apply_eq_zpow_apply
  statement: {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s)
  proof: by
  rw [Int.modEq_iff_dvd]; rw [← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_symm_apply, eq_comm]

中文:
定理 IsCycleOn.zpow_apply_eq_zpow_apply
  结论: {s : 有限集 α} (hf : f.IsCycleOn s) (ha : a in s)
  证明: by
  rw [Int.modEq_iff_dvd]; rw [← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_symm_apply, eq_comm]

Depends on / 依赖: Int.modEq_iff_dvd, eq_comm, eq_symm_apply, hf.zpow_apply_eq, modEq_iff_dvd, sub_eq_neg_add, zpow_add, zpow_apply_eq
-/
theorem IsCycleOn.zpow_apply_eq_zpow_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s)
    {m n : Int} : (f ^ m) a = (f ^ n) a ↔ m ≡ n [ZMOD #s] := by
  rw [Int.modEq_iff_dvd]; rw [← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_symm_apply, eq_comm]

/--
theorem `IsCycleOn.pow_card_apply` / 定理 `IsCycleOn.pow_card_apply`

English:
theorem IsCycleOn.pow_card_apply
  given: {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s)
  proof: (hf.pow_apply_eq ha).2 dvd_rfl

中文:
定理 IsCycleOn.pow_card_apply
  条件: {s : 有限集 α} (hf : f.IsCycleOn s) (ha : a in s)
  证明: (hf.pow_apply_eq ha).2 dvd_rfl

Depends on / 依赖: dvd_rfl, hf.pow_apply_eq, pow_apply_eq
-/
theorem IsCycleOn.pow_card_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s) :
    (f ^ #s) a = a :=
  (hf.pow_apply_eq ha).2 dvd_rfl

/--
theorem `IsCycleOn.exists_pow_eq` / 定理 `IsCycleOn.exists_pow_eq`

English:
theorem IsCycleOn.exists_pow_eq
  given: {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s) (hb : b in s)
  proof: by
  obtain ⟨n, rfl⟩ := hf.2 ha hb
  obtain ⟨k, hk⟩ := (Int.mod_modEq n #s).symm.dvd
  refine ⟨n.natMod #s, Int.natMod_lt (Nonempty.card_pos ⟨a, ha⟩).ne', ?_⟩
  rw [← zpow_natCast]; rw [Int.natMod]; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ <| Nat.cast_ne_zero.2
      (Nonempty.card_pos ⟨a]; rw [ha

中文:
定理 IsCycleOn.存在_pow_eq
  条件: {s : 有限集 α} (hf : f.IsCycleOn s) (ha : a in s) (hb : b in s)
  证明: by
  obtain ⟨n, rfl⟩ := hf.2 ha hb
  obtain ⟨k, hk⟩ := (Int.mod_modEq n #s).symm.dvd
  refine ⟨n.natMod #s, Int.natMod_lt (Nonempty.card_pos ⟨a, ha⟩).ne', ?_⟩
  rw [← zpow_natCast]; rw [Int.natMod]; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ <| Nat.cast_ne_zero.2
      (Nonempty.card_pos ⟨a]; rw [ha

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Int.emod_nonneg, Int.mod_modEq, Int.natMod, Int.natMod_lt, Int.toNat_of_nonneg, IsFixedPt, IsFixedPt.perm_zpow, Nat.cast_ne_zero, Nonempty, Nonempty.card_pos, apply_eq_iff_eq, card_pos, cast_ne_zero, coe_mul, comp_apply, emod_nonneg, hf.pow_card_apply, mod_modEq
-/
theorem IsCycleOn.exists_pow_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a in s) (hb : b in s) :
    exists n < #s, (f ^ n) a = b := by
  obtain ⟨n, rfl⟩ := hf.2 ha hb
  obtain ⟨k, hk⟩ := (Int.mod_modEq n #s).symm.dvd
  refine ⟨n.natMod #s, Int.natMod_lt (Nonempty.card_pos ⟨a, ha⟩).ne', ?_⟩
  rw [← zpow_natCast]; rw [Int.natMod]; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ <| Nat.cast_ne_zero.2
      (Nonempty.card_pos ⟨a]; rw [ha⟩).ne')]; rw [sub_eq_iff_eq_add'.1 hk]; rw [zpow_add]; rw [zpow_mul]
  simp only [zpow_natCast, coe_mul, comp_apply, EmbeddingLike.apply_eq_iff_eq]
  exact IsFixedPt.perm_zpow (hf.pow_card_apply ha) _

/--
theorem `IsCycleOn.exists_pow_eq'` / 定理 `IsCycleOn.exists_pow_eq'`

English:
theorem IsCycleOn.exists_pow_eq'
  given: (hs : s.Finite) (hf : f.IsCycleOn s) (ha : a in s) (hb : b in s)
  proof: by
  lift s to Finset α using hs
  obtain ⟨n, -, hn⟩ := hf.exists_pow_eq ha hb
  exact ⟨n, hn⟩

中文:
定理 IsCycleOn.存在_pow_eq'
  条件: (hs : s.有限) (hf : f.IsCycleOn s) (ha : a in s) (hb : b in s)
  证明: by
  lift s to Finset α using hs
  obtain ⟨n, -, hn⟩ := hf.exists_pow_eq ha hb
  exact ⟨n, hn⟩

Depends on / 依赖: Finset, exists_pow_eq, hf.exists_pow_eq
-/
theorem IsCycleOn.exists_pow_eq' (hs : s.Finite) (hf : f.IsCycleOn s) (ha : a in s) (hb : b in s) :
    exists n : Nat, (f ^ n) a = b := by
  lift s to Finset α using hs
  obtain ⟨n, -, hn⟩ := hf.exists_pow_eq ha hb
  exact ⟨n, hn⟩

/--
theorem `IsCycleOn.range_pow` / 定理 `IsCycleOn.range_pow`

English:
theorem IsCycleOn.range_pow
  given: (hs : s.Finite) (h : f.IsCycleOn s) (ha : a in s)
  proof: Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => h.1.mapsTo.perm_pow _ ha) fun _ =>
    h.exists_pow_eq' hs ha

中文:
定理 IsCycleOn.range_pow
  条件: (hs : s.有限) (h : f.IsCycleOn s) (ha : a in s)
  证明: Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => h.1.mapsTo.perm_pow _ ha) fun _ =>
    h.exists_pow_eq' hs ha

Depends on / 依赖: Set.Subset.antisymm, Set.range_subset_iff, Subset, antisymm, exists_pow_eq, h.exists_pow_eq, mapsTo, mapsTo.perm_pow, perm_pow, range_subset_iff
-/
theorem IsCycleOn.range_pow (hs : s.Finite) (h : f.IsCycleOn s) (ha : a in s) :
    Set.range (fun n => (f ^ n) a : Nat -> α) = s :=
  Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => h.1.mapsTo.perm_pow _ ha) fun _ =>
    h.exists_pow_eq' hs ha

/--
theorem `IsCycleOn.range_zpow` / 定理 `IsCycleOn.range_zpow`

English:
theorem IsCycleOn.range_zpow
  given: (h : f.IsCycleOn s) (ha : a in s)
  proof: Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => (h.1.perm_zpow _).mapsTo ha) h.2 ha

中文:
定理 IsCycleOn.range_zpow
  条件: (h : f.IsCycleOn s) (ha : a in s)
  证明: Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => (h.1.perm_zpow _).mapsTo ha) h.2 ha

Depends on / 依赖: Set.Subset.antisymm, Set.range_subset_iff, Subset, antisymm, mapsTo, perm_zpow, range_subset_iff
-/
theorem IsCycleOn.range_zpow (h : f.IsCycleOn s) (ha : a in s) :
    Set.range (fun n => (f ^ n) a : Int -> α) = s :=
Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => (h.1.perm_zpow _).mapsTo ha) h.2 ha

/--
theorem `IsCycleOn.of_pow` / 定理 `IsCycleOn.of_pow`

English:
theorem IsCycleOn.of_pow
  given: {n : Nat} (hf : (f ^ n).IsCycleOn s) (h : Set.BijOn f s s)
  statement: f.IsCycleOn s
  proof: ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_pow⟩

中文:
定理 IsCycleOn.of_pow
  条件: {n : 自然数} (hf : (f ^ n).IsCycleOn s) (h : 集合.双射限制 f s s)
  结论: f.IsCycleOn s
  证明: ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_pow⟩

Depends on / 依赖: of_pow
-/
theorem IsCycleOn.of_pow {n : Nat} (hf : (f ^ n).IsCycleOn s) (h : Set.BijOn f s s) : f.IsCycleOn s :=
  ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_pow⟩

/--
theorem `IsCycleOn.of_zpow` / 定理 `IsCycleOn.of_zpow`

English:
theorem IsCycleOn.of_zpow
  given: {n : Int} (hf : (f ^ n).IsCycleOn s) (h : Set.BijOn f s s)
  proof: ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_zpow⟩

中文:
定理 IsCycleOn.of_zpow
  条件: {n : 整数} (hf : (f ^ n).IsCycleOn s) (h : 集合.双射限制 f s s)
  证明: ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_zpow⟩

Depends on / 依赖: of_zpow
-/
theorem IsCycleOn.of_zpow {n : Int} (hf : (f ^ n).IsCycleOn s) (h : Set.BijOn f s s) :
    f.IsCycleOn s :=
  ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_zpow⟩

/--
theorem `IsCycleOn.extendDomain` / 定理 `IsCycleOn.extendDomain`

English:
theorem IsCycleOn.extendDomain
  statement: {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p)
  proof: ⟨h.1.extendDomain, by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (h.2 ha hb).extendDomain⟩

中文:
定理 IsCycleOn.extendDomain
  结论: {p : β -> 命题} [DecidablePred p] (f : α ≃ 子类型 p)
  证明: ⟨h.1.extendDomain, by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (h.2 ha hb).extendDomain⟩

Depends on / 依赖: extendDomain
-/
theorem IsCycleOn.extendDomain {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p)
    (h : g.IsCycleOn s) : (g.extendDomain f).IsCycleOn ((↑) ∘ f '' s) :=
  ⟨h.1.extendDomain, by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (h.2 ha hb).extendDomain⟩

/--
theorem `IsCycleOn.countable` / 定理 `IsCycleOn.countable`

English:
theorem IsCycleOn.countable
  given: (hs : f.IsCycleOn s)
  statement: s.Countable
  proof: by
  obtain rfl | ⟨a, ha⟩ := s.eq_empty_or_nonempty
  · exact Set.countable_empty
  · exact (Set.countable_range fun n : Int => (⇑(f ^ n) : α -> α) a).mono (hs.2 ha)

中文:
定理 IsCycleOn.countable
  条件: (hs : f.IsCycleOn s)
  结论: s.可数
  证明: by
  obtain rfl | ⟨a, ha⟩ := s.eq_empty_or_nonempty
  · exact Set.countable_empty
  · exact (Set.countable_range fun n : Int => (⇑(f ^ n) : α -> α) a).mono (hs.2 ha)
-/
protected theorem IsCycleOn.countable (hs : f.IsCycleOn s) : s.Countable := by
  obtain rfl | ⟨a, ha⟩ := s.eq_empty_or_nonempty
  · exact Set.countable_empty
  · exact (Set.countable_range fun n : Int => (⇑(f ^ n) : α -> α) a).mono (hs.2 ha)


end IsCycleOn

end Equiv.Perm

namespace List

section

variable [DecidableEq α] {l : List α}

/--
theorem `Nodup.isCycleOn_formPerm` / 定理 `Nodup.isCycleOn_formPerm`

English:
theorem Nodup.isCycleOn_formPerm
  given: (h : l.Nodup)
  proof: by
  refine ⟨l.formPerm.bijOn fun _ => List.formPerm_mem_iff_mem, fun a ha b hb => ?_⟩
  rw [Set.mem_ofPred]; rw [← List.idxOf_lt_length_iff] at ha hb
  rw [← List.getElem_idxOf ha]; rw [← List.getElem_idxOf hb]
  refine ⟨l.idxOf b - l.idxOf a, ?_⟩
  simp only [sub_eq_neg_add, zpow_add, zpow_neg, Eq

中文:
定理 Nodup.isCycleOn_formPerm
  条件: (h : l.Nodup)
  证明: by
  refine ⟨l.formPerm.bijOn fun _ => List.formPerm_mem_iff_mem, fun a ha b hb => ?_⟩
  rw [Set.mem_ofPred]; rw [← List.idxOf_lt_length_iff] at ha hb
  rw [← List.getElem_idxOf ha]; rw [← List.getElem_idxOf hb]
  refine ⟨l.idxOf b - l.idxOf a, ?_⟩
  simp only [sub_eq_neg_add, zpow_add, zpow_neg, Eq

Depends on / 依赖: Equiv.Perm.coe_mul, Equiv.Perm.inv_eq_iff_eq, Function, Function.comp, List.formPerm_mem_iff_mem, List.formPerm_pow_apply_getElem, List.getElem_idxOf, List.idxOf_lt_length_iff, Set.mem_ofPred, add_comm, coe_mul, formPerm, formPerm_mem_iff_mem, formPerm_pow_apply_getElem, getElem_idxOf, idxOf_lt_length_iff, inv_eq_iff_eq, l.formPerm.bijOn, l.idxOf, mem_ofPred
-/
theorem Nodup.isCycleOn_formPerm (h : l.Nodup) :
    l.formPerm.IsCycleOn { a | a in l } := by
  refine ⟨l.formPerm.bijOn fun _ => List.formPerm_mem_iff_mem, fun a ha b hb => ?_⟩
  rw [Set.mem_ofPred]; rw [← List.idxOf_lt_length_iff] at ha hb
  rw [← List.getElem_idxOf ha]; rw [← List.getElem_idxOf hb]
  refine ⟨l.idxOf b - l.idxOf a, ?_⟩
  simp only [sub_eq_neg_add, zpow_add, zpow_neg, Equiv.Perm.inv_eq_iff_eq, zpow_natCast,
    Equiv.Perm.coe_mul, List.formPerm_pow_apply_getElem _ h, Function.comp]
  rw [add_comm]

end

end List

namespace Finset

variable [DecidableEq α] [Fintype α]

/--
theorem `exists_cycleOn` / 定理 `exists_cycleOn`

English:
theorem exists_cycleOn
  given: (s : Finset α)
  proof: by
  refine ⟨s.toList.formPerm, ?_, fun x hx => by
    simpa using List.mem_of_formPerm_apply_ne (Perm.mem_support.1 hx)⟩
  convert! s.nodup_toList.isCycleOn_formPerm
  simp

中文:
定理 存在_cycleOn
  条件: (s : 有限集 α)
  证明: by
  refine ⟨s.toList.formPerm, ?_, fun x hx => by
    simpa using List.mem_of_formPerm_apply_ne (Perm.mem_support.1 hx)⟩
  convert! s.nodup_toList.isCycleOn_formPerm
  simp

Depends on / 依赖: List.mem_of_formPerm_apply_ne, Perm.mem_support, convert, formPerm, isCycleOn_formPerm, mem_of_formPerm_apply_ne, mem_support, nodup_toList, s.nodup_toList.isCycleOn_formPerm, s.toList.formPerm, toList
-/
theorem exists_cycleOn (s : Finset α) :
    exists f : Perm α, f.IsCycleOn s ∧ f.support subseteq s := by
  refine ⟨s.toList.formPerm, ?_, fun x hx => by
    simpa using List.mem_of_formPerm_apply_ne (Perm.mem_support.1 hx)⟩
  convert! s.nodup_toList.isCycleOn_formPerm
  simp

end Finset

namespace Set

variable {f : Perm α} {s : Set α}

/--
theorem `Countable.exists_cycleOn` / 定理 `Countable.exists_cycleOn`

English:
theorem Countable.exists_cycleOn
  given: (hs : s.Countable)
  proof: by
  classical
  obtain hs' | hs' := s.finite_or_infinite
  · refine ⟨hs'.toFinset.toList.formPerm, ?_, fun x hx => by
      simpa using List.mem_of_formPerm_apply_ne hx⟩
    convert! hs'.toFinset.nodup_toList.isCycleOn_formPerm
    simp
  · have := hs.to_subtype
    have := hs'.to_subtype
    obtai

中文:
定理 可数.存在_cycleOn
  条件: (hs : s.可数)
  证明: by
  classical
  obtain hs' | hs' := s.finite_or_infinite
  · refine ⟨hs'.toFinset.toList.formPerm, ?_, fun x hx => by
      simpa using List.mem_of_formPerm_apply_ne hx⟩
    convert! hs'.toFinset.nodup_toList.isCycleOn_formPerm
    simp
  · have := hs.to_subtype
    have := hs'.to_subtype
    obtai

Depends on / 依赖: Equiv.addRight, Int.addRight_one_isCycle.isCycleOn.extendDomain, List.mem_of_formPerm_apply_ne, Nonempty, Perm.extendDomain_apply_not_subtype, addRight, addRight_one_isCycle, classical, convert, extendDomain, extendDomain_apply_not_subtype, finite_or_infinite, formPerm, hs.to_subtype, isCycleOn, isCycleOn_formPerm, mem_of_formPerm_apply_ne, nodup_toList, of_not_not, s.finite_or_infinite
-/
theorem Countable.exists_cycleOn (hs : s.Countable) :
    exists f : Perm α, f.IsCycleOn s ∧ { x | f x != x } subseteq s := by
  classical
  obtain hs' | hs' := s.finite_or_infinite
  · refine ⟨hs'.toFinset.toList.formPerm, ?_, fun x hx => by
      simpa using List.mem_of_formPerm_apply_ne hx⟩
    convert! hs'.toFinset.nodup_toList.isCycleOn_formPerm
    simp
  · have := hs.to_subtype
    have := hs'.to_subtype
    obtain ⟨f⟩ : Nonempty (Int ≃ s) := inferInstance
    refine ⟨(Equiv.addRight 1).extendDomain f, ?_, fun x hx =>
of_not_not fun h => hx Perm.extendDomain_apply_not_subtype _ _ h⟩
    convert! Int.addRight_one_isCycle.isCycleOn.extendDomain f
    rw [Set.image_comp]; rw [Equiv.image_eq_preimage_symm]
    ext
    simp

/--
theorem `prod_self_eq_iUnion_perm` / 定理 `prod_self_eq_iUnion_perm`

English:
theorem prod_self_eq_iUnion_perm
  given: (hf : f.IsCycleOn s)
  proof: by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_image]
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := hf.2 hx.1 hx.2
    exact ⟨_, _, hx.1, rfl⟩
  · rintro ⟨n, a, ha, ⟨⟩⟩
    exact ⟨ha, (hf.1.perm_zpow _).mapsTo ha⟩

中文:
定理 prod_self_eq_iUnion_perm
  条件: (hf : f.IsCycleOn s)
  证明: by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_image]
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := hf.2 hx.1 hx.2
    exact ⟨_, _, hx.1, rfl⟩
  · rintro ⟨n, a, ha, ⟨⟩⟩
    exact ⟨ha, (hf.1.perm_zpow _).mapsTo ha⟩

Depends on / 依赖: Set.mem_iUnion, Set.mem_image, Set.mem_prod, mapsTo, mem_iUnion, mem_image, mem_prod, perm_zpow
-/
theorem prod_self_eq_iUnion_perm (hf : f.IsCycleOn s) :
    s ×ˢ s = ⋃ n : Int, (fun a => (a, (f ^ n) a)) '' s := by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_image]
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := hf.2 hx.1 hx.2
    exact ⟨_, _, hx.1, rfl⟩
  · rintro ⟨n, a, ha, ⟨⟩⟩
    exact ⟨ha, (hf.1.perm_zpow _).mapsTo ha⟩

end Set

namespace Finset

variable {f : Perm α} {s : Finset α}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `product_self_eq_disjiUnion_perm_aux` / 定理 `product_self_eq_disjiUnion_perm_aux`

English:
theorem product_self_eq_disjiUnion_perm_aux
  given: (hf : f.IsCycleOn s)
  proof: by
  obtain hs | _ := (s : Set α).subsingleton_or_nontrivial
  · refine Set.Subsingleton.pairwise ?_ _
    simp_rw [Set.Subsingleton, mem_coe, ← card_le_one] at hs ⊢
    rwa [card_range]
  classical
    rintro m hm n hn hmn
    simp only [disjoint_left, Function.onFun, mem_map, Function.Embedding.co

中文:
定理 product_self_eq_disjiUnion_perm_aux
  条件: (hf : f.IsCycleOn s)
  证明: by
  obtain hs | _ := (s : Set α).subsingleton_or_nontrivial
  · refine Set.Subsingleton.pairwise ?_ _
    simp_rw [Set.Subsingleton, mem_coe, ← card_le_one] at hs ⊢
    rwa [card_range]
  classical
    rintro m hm n hn hmn
    simp only [disjoint_left, Function.onFun, mem_map, Function.Embedding.co

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, Function.onFun, Prod.forall, Prod.mk_inj, Set.Subsingleton, Set.Subsingleton.pairwise, Subsingleton, and_imp, card_le_one, card_range, classical, coeFn_mk, disjoint_left, eq_of_lt, forall_exists_index, h.eq_of_lt, hf.pow_apply_eq_pow_apply, hmn.symm
-/
theorem product_self_eq_disjiUnion_perm_aux (hf : f.IsCycleOn s) :
    (range #s : Set Nat).PairwiseDisjoint fun k =>
      s.map ⟨fun i => (i, (f ^ k) i), fun _ _ => congr_arg Prod.fst⟩ := by
  obtain hs | _ := (s : Set α).subsingleton_or_nontrivial
  · refine Set.Subsingleton.pairwise ?_ _
    simp_rw [Set.Subsingleton, mem_coe, ← card_le_one] at hs ⊢
    rwa [card_range]
  classical
    rintro m hm n hn hmn
    simp only [disjoint_left, Function.onFun, mem_map, Function.Embedding.coeFn_mk,
      not_exists, not_and, forall_exists_index, and_imp, Prod.forall, Prod.mk_inj]
    rintro _ _ _ - rfl rfl a ha rfl h
    rw [hf.pow_apply_eq_pow_apply ha] at h
    rw [mem_coe]; rw [mem_range] at hm hn
    exact hmn.symm (h.eq_of_lt_of_lt hn hm)

/--
theorem `product_self_eq_disjiUnion_perm` / 定理 `product_self_eq_disjiUnion_perm`

English:
theorem product_self_eq_disjiUnion_perm
  given: (hf : f.IsCycleOn s)
  proof: by
  ext ⟨a, b⟩
  simp only [mem_product, Equiv.Perm.coe_pow, mem_disjiUnion, mem_range, mem_map,
    Function.Embedding.coeFn_mk, Prod.mk_inj]
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨n, hn, rfl⟩ := hf.exists_pow_eq hx.1 hx.2
    exact ⟨n, hn, a, hx.1, rfl, by rw [f.iterate_eq_pow]⟩
  · rintro ⟨n, -

中文:
定理 product_self_eq_disjiUnion_perm
  条件: (hf : f.IsCycleOn s)
  证明: by
  ext ⟨a, b⟩
  simp only [mem_product, Equiv.Perm.coe_pow, mem_disjiUnion, mem_range, mem_map,
    Function.Embedding.coeFn_mk, Prod.mk_inj]
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨n, hn, rfl⟩ := hf.exists_pow_eq hx.1 hx.2
    exact ⟨n, hn, a, hx.1, rfl, by rw [f.iterate_eq_pow]⟩
  · rintro ⟨n, -

Depends on / 依赖: Embedding, Equiv.Perm.coe_pow, Function, Function.Embedding.coeFn_mk, Prod.mk_inj, coeFn_mk, coe_pow, exists_pow_eq, f.iterate_eq_pow, hf.exists_pow_eq, iterate, iterate_eq_pow, mapsTo, mem_disjiUnion, mem_map, mem_product, mem_range, mk_inj
-/
theorem product_self_eq_disjiUnion_perm (hf : f.IsCycleOn s) :
    s ×ˢ s =
      (range #s).disjiUnion
        (fun k => s.map ⟨fun i => (i, (f ^ k) i), fun _ _ => congr_arg Prod.fst⟩)
        (product_self_eq_disjiUnion_perm_aux hf) := by
  ext ⟨a, b⟩
  simp only [mem_product, Equiv.Perm.coe_pow, mem_disjiUnion, mem_range, mem_map,
    Function.Embedding.coeFn_mk, Prod.mk_inj]
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨n, hn, rfl⟩ := hf.exists_pow_eq hx.1 hx.2
    exact ⟨n, hn, a, hx.1, rfl, by rw [f.iterate_eq_pow]⟩
  · rintro ⟨n, -, a, ha, rfl, rfl⟩
    exact ⟨ha, (hf.1.iterate _).mapsTo ha⟩

end Finset

namespace Finset

variable [Semiring α] [AddCommMonoid β] [Module α β] {s : Finset ι} {σ : Perm ι}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sum_smul_sum_eq_sum_perm` / 定理 `sum_smul_sum_eq_sum_perm`

English:
theorem sum_smul_sum_eq_sum_perm
  given: (hσ : σ.IsCycleOn s) (f : ι -> α) (g : ι -> β)
  proof: by
  rw [sum_smul_sum]; rw [← sum_product']
  simp_rw [product_self_eq_disjiUnion_perm hσ, sum_disjiUnion, sum_map, Embedding.coeFn_mk]

中文:
定理 sum_smul_sum_eq_sum_perm
  条件: (hσ : σ.IsCycleOn s) (f : ι -> α) (g : ι -> β)
  证明: by
  rw [sum_smul_sum]; rw [← sum_product']
  simp_rw [product_self_eq_disjiUnion_perm hσ, sum_disjiUnion, sum_map, Embedding.coeFn_mk]

Depends on / 依赖: Embedding, Embedding.coeFn_mk, coeFn_mk, product_self_eq_disjiUnion_perm, simp_rw, sum_disjiUnion, sum_map, sum_product, sum_smul_sum
-/
theorem sum_smul_sum_eq_sum_perm (hσ : σ.IsCycleOn s) (f : ι -> α) (g : ι -> β) :
    (∑ i in s, f i) • ∑ i in s, g i = ∑ k in range #s, ∑ i in s, f i • g ((σ ^ k) i) := by
  rw [sum_smul_sum]; rw [← sum_product']
  simp_rw [product_self_eq_disjiUnion_perm hσ, sum_disjiUnion, sum_map, Embedding.coeFn_mk]

/--
theorem `sum_mul_sum_eq_sum_perm` / 定理 `sum_mul_sum_eq_sum_perm`

English:
theorem sum_mul_sum_eq_sum_perm
  given: (hσ : σ.IsCycleOn s) (f g : ι -> α)
  proof: sum_smul_sum_eq_sum_perm hσ f g

中文:
定理 sum_mul_sum_eq_sum_perm
  条件: (hσ : σ.IsCycleOn s) (f g : ι -> α)
  证明: sum_smul_sum_eq_sum_perm hσ f g

Depends on / 依赖: sum_smul_sum_eq_sum_perm
-/
theorem sum_mul_sum_eq_sum_perm (hσ : σ.IsCycleOn s) (f g : ι -> α) :
    ((∑ i in s, f i) * ∑ i in s, g i) = ∑ k in range #s, ∑ i in s, f i * g ((σ ^ k) i) :=
  sum_smul_sum_eq_sum_perm hσ f g

end Finset

namespace Equiv.Perm

/--
theorem `subtypePerm_apply_pow_of_mem` / 定理 `subtypePerm_apply_pow_of_mem`

English:
theorem subtypePerm_apply_pow_of_mem
  statement: {g : Perm α} {s : Finset α}
  proof: by
  simp only [subtypePerm_pow, subtypePerm_apply]

中文:
定理 subtypePerm_apply_pow_of_mem
  结论: {g : 置换 α} {s : 有限集 α}
  证明: by
  simp only [subtypePerm_pow, subtypePerm_apply]

Depends on / 依赖: subtypePerm_apply, subtypePerm_pow
-/
theorem subtypePerm_apply_pow_of_mem {g : Perm α} {s : Finset α}
    (hs : forall x : α, g x in s ↔ x in s) {n : Nat} {x : α} (hx : x in s) :
    ((g.subtypePerm hs ^ n) (⟨x, hx⟩ : s) : α) = (g ^ n) x := by
  simp only [subtypePerm_pow, subtypePerm_apply]

/--
theorem `subtypePerm_apply_zpow_of_mem` / 定理 `subtypePerm_apply_zpow_of_mem`

English:
theorem subtypePerm_apply_zpow_of_mem
  statement: {g : Perm α} {s : Finset α}
  proof: by
  simp only [subtypePerm_zpow, subtypePerm_apply]

中文:
定理 subtypePerm_apply_zpow_of_mem
  结论: {g : 置换 α} {s : 有限集 α}
  证明: by
  simp only [subtypePerm_zpow, subtypePerm_apply]

Depends on / 依赖: liftAux, liftAux.smul, subtypePerm_apply, subtypePerm_zpow
-/
theorem subtypePerm_apply_zpow_of_mem {g : Perm α} {s : Finset α}
    (hs : forall x : α, g x in s ↔ x in s) {i : Int} {x : α} (hx : x in s) :
    ((g.subtypePerm hs ^ i) (⟨x, hx⟩ : s) : α) = (g ^ i) x := by
  simp only [subtypePerm_zpow, subtypePerm_apply]

variable [Fintype α] [DecidableEq α]

/--
Definition of `subtypePermOfSupport` / `subtypePermOfSupport` 的定义

English:
definition subtypePermOfSupport
  signature: (c : Perm α)
  body: subtypePerm c fun _ : α => apply_mem_support

中文:
定义 subtypePermOfSupport
  签名: (c : 置换 α)
  定义体: subtypePerm c fun _ : α => apply_mem_support

Depends on / 依赖: apply_mem_support, subtypePerm
-/
def subtypePermOfSupport (c : Perm α) : Perm c.support :=
  subtypePerm c fun _ : α => apply_mem_support

/--
Definition of `subtypePerm_of_support_le` / `subtypePerm_of_support_le` 的定义

English:
definition subtypePerm_of_support_le
  signature: (c : Perm α) {s : Finset α}
  body: subtypePerm c (isInvariant_of_support_le hcs)

中文:
定义 subtypePerm_of_support_le
  签名: (c : 置换 α) {s : 有限集 α}
  定义体: subtypePerm c (isInvariant_of_support_le hcs)

Depends on / 依赖: isInvariant_of_support_le, subtypePerm
-/
def subtypePerm_of_support_le (c : Perm α) {s : Finset α}
    (hcs : c.support subseteq s) : Equiv.Perm s :=
  subtypePerm c (isInvariant_of_support_le hcs)

/--
theorem `IsCycle.nonempty_support` / 定理 `IsCycle.nonempty_support`

English:
theorem IsCycle.nonempty_support
  given: {g : Perm α} (hg : g.IsCycle)
  proof: by
  rw [Finset.nonempty_iff_ne_empty]; rw [ne_eq]; rw [support_eq_empty_iff]
  exact IsCycle.ne_one hg

中文:
定理 是环.nonempty_support
  条件: {g : 置换 α} (hg : g.是环)
  证明: by
  rw [Finset.nonempty_iff_ne_empty]; rw [ne_eq]; rw [support_eq_empty_iff]
  exact IsCycle.ne_one hg

Depends on / 依赖: Finset, Finset.nonempty_iff_ne_empty, IsCycle, IsCycle.ne_one, ne_eq, ne_one, nonempty_iff_ne_empty, support_eq_empty_iff
-/
theorem IsCycle.nonempty_support {g : Perm α} (hg : g.IsCycle) :
    g.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]; rw [ne_eq]; rw [support_eq_empty_iff]
  exact IsCycle.ne_one hg

/--
theorem `IsCycle.commute_iff'` / 定理 `IsCycle.commute_iff'`

English:
theorem IsCycle.commute_iff'
  given: {g c : Perm α} (hc : c.IsCycle)
  proof: by
  constructor
  · intro hgc
    have hgc' := mem_support_iff_of_commute hgc
    use hgc'
    obtain ⟨a, ha⟩ := IsCycle.nonempty_support hc
    obtain ⟨i, hi⟩ := hc.sameCycle (mem_support.mp ha) (mem_support.mp ((hgc' a).mpr ha))
    use i
    ext ⟨x, hx⟩
    simp only [subtypePermOfSupport, Subty

中文:
定理 是环.commute_iff'
  条件: {g c : 置换 α} (hc : c.是环)
  证明: by
  constructor
  · intro hgc
    have hgc' := mem_support_iff_of_commute hgc
    use hgc'
    obtain ⟨a, ha⟩ := IsCycle.nonempty_support hc
    obtain ⟨i, hi⟩ := hc.sameCycle (mem_support.mp ha) (mem_support.mp ((hgc' a).mpr ha))
    use i
    ext ⟨x, hx⟩
    simp only [subtypePermOfSupport, Subty

Depends on / 依赖: Commute, Commute.eq, Commute.zpow_right, IsCycle, IsCycle.nonempty_support, Subtype, Subtype.coe_mk, add_comm, coe_mk, hc.sameCycle, mem_support, mem_support.mp, mem_support_iff_of_commute, mul_apply, nonempty_support, sameCycle, subtypePermOfSupport, subtypePerm_apply, subtypePerm_apply_zpow_of_mem, zpow_add
-/
theorem IsCycle.commute_iff' {g c : Perm α} (hc : c.IsCycle) :
    Commute g c ↔
      exists hc' : forall x : α, g x in c.support ↔ x in c.support,
        subtypePerm g hc' in Subgroup.zpowers c.subtypePermOfSupport := by
  constructor
  · intro hgc
    have hgc' := mem_support_iff_of_commute hgc
    use hgc'
    obtain ⟨a, ha⟩ := IsCycle.nonempty_support hc
    obtain ⟨i, hi⟩ := hc.sameCycle (mem_support.mp ha) (mem_support.mp ((hgc' a).mpr ha))
    use i
    ext ⟨x, hx⟩
    simp only [subtypePermOfSupport, Subtype.coe_mk, subtypePerm_apply]
    rw [subtypePerm_apply_zpow_of_mem]
    obtain ⟨j, rfl⟩ := hc.sameCycle (mem_support.mp ha) (mem_support.mp hx)
    simp only [← mul_apply, Commute.eq (Commute.zpow_right hgc j)]
    rw [← zpow_add]; rw [add_comm i j]; rw [zpow_add]
    simp only [mul_apply, EmbeddingLike.apply_eq_iff_eq]
    exact hi
  · rintro ⟨hc', ⟨i, hi⟩⟩
    ext x
    simp only [coe_mul, Function.comp_apply]
    by_cases hx : x in c.support
    · suffices hi' : forall x in c.support, g x = (c ^ i) x by
        rw [hi' x hx]; rw [hi' (c x) (apply_mem_support.mpr hx)]
        simp only [← mul_apply, ← zpow_add_one, ← zpow_one_add, add_comm]
      intro x hx
      have hix := Perm.congr_fun hi ⟨x, hx⟩
      simp only [← Subtype.coe_inj, subtypePermOfSupport, subtypePerm_apply,
        subtypePerm_apply_zpow_of_mem] at hix
      exact hix.symm
    · rw [notMem_support.mp hx, eq_comm, ← notMem_support]
      contrapose hx
      exact (hc' x).mp hx

/--
theorem `IsCycle.commute_iff` / 定理 `IsCycle.commute_iff`

English:
theorem IsCycle.commute_iff
  given: {g c : Perm α} (hc : c.IsCycle)
  proof: by
  simp_rw [hc.commute_iff', Subgroup.mem_zpowers_iff]
  refine exists_congr fun hc' => exists_congr fun k => ?_
  rw [subtypePermOfSupport]; rw [subtypePerm_zpow c k]
  simp only [Perm.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  apply forall_congr'
  intro a
  by_cases ha : a 

中文:
定理 是环.commute_iff
  条件: {g c : 置换 α} (hc : c.是环)
  证明: by
  simp_rw [hc.commute_iff', Subgroup.mem_zpowers_iff]
  refine exists_congr fun hc' => exists_congr fun k => ?_
  rw [subtypePermOfSupport]; rw [subtypePerm_zpow c k]
  simp only [Perm.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  apply forall_congr'
  intro a
  by_cases ha : a 

Depends on / 依赖: Finset, Finset.notMem_mono, Perm.ext_iff, Subgroup, Subgroup.mem_zpowers_iff, Subtype, Subtype.forall, Subtype.mk.injEq, c.support, commute_iff, exists_congr, ext_iff, forall_congr, hc.commute_iff, iff_true_left, imp_iff_right, lift.tmul, mem_zpowers_iff, notMem_mono, notMem_support
-/
theorem IsCycle.commute_iff {g c : Perm α} (hc : c.IsCycle) :
    Commute g c ↔
      exists hc' : forall x : α, g x in c.support ↔ x in c.support,
        ofSubtype (subtypePerm g hc') in Subgroup.zpowers c := by
  simp_rw [hc.commute_iff', Subgroup.mem_zpowers_iff]
  refine exists_congr fun hc' => exists_congr fun k => ?_
  rw [subtypePermOfSupport]; rw [subtypePerm_zpow c k]
  simp only [Perm.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  apply forall_congr'
  intro a
  by_cases ha : a in c.support
  · rw [imp_iff_right ha, ofSubtype_subtypePerm_of_mem hc' ha]
  · rw [iff_true_left (fun b => (ha b).elim), ofSubtype_apply_of_not_mem, ← notMem_support]
    · exact Finset.notMem_mono (support_zpow_le c k) ha
    · exact ha

/--
theorem `zpow_eq_ofSubtype_subtypePerm_iff` / 定理 `zpow_eq_ofSubtype_subtypePerm_iff`

English:
theorem zpow_eq_ofSubtype_subtypePerm_iff
  proof: by
  constructor
  · intro h
    ext ⟨x, hx⟩
    simpa [Perm.congr_fun h _] using ofSubtype_subtypePerm_of_mem _ hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x in s
    · rw [ofSubtype_apply_of_mem (subtypePerm c _ ^ n) hx,
        subtypePerm_zpow, subtypePerm_apply]
    · rw [ofSubtype_app

中文:
定理 zpow_eq_ofSubtype_subtypePerm_iff
  证明: by
  constructor
  · intro h
    ext ⟨x, hx⟩
    simpa [Perm.congr_fun h _] using ofSubtype_subtypePerm_of_mem _ hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x in s
    · rw [ofSubtype_apply_of_mem (subtypePerm c _ ^ n) hx,
        subtypePerm_zpow, subtypePerm_apply]
    · rw [ofSubtype_app

Depends on / 依赖: Perm.congr_fun, congr_fun, notMem_support, ofSubtype_apply_of_mem, ofSubtype_apply_of_not_mem, ofSubtype_subtypePerm_of_mem, subtypePerm, subtypePerm_apply, subtypePerm_zpow, support_zpow_le
-/
theorem zpow_eq_ofSubtype_subtypePerm_iff
    {g c : Equiv.Perm α} {s : Finset α}
    (hg : forall x, g x in s ↔ x in s) (hc : c.support subseteq s) (n : Int) :
    c ^ n = ofSubtype (g.subtypePerm hg) ↔
      c.subtypePerm (isInvariant_of_support_le hc) ^ n = g.subtypePerm hg := by
  constructor
  · intro h
    ext ⟨x, hx⟩
    simpa [Perm.congr_fun h _] using ofSubtype_subtypePerm_of_mem _ hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x in s
    · rw [ofSubtype_apply_of_mem (subtypePerm c _ ^ n) hx,
        subtypePerm_zpow, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (subtypePerm c _ ^ n) hx,
        ← notMem_support]
      exact fun hx' => hx (hc (support_zpow_le _ _ hx'))

/--
theorem `cycle_zpow_mem_support_iff` / 定理 `cycle_zpow_mem_support_iff`

English:
theorem cycle_zpow_mem_support_iff
  statement: {g : Perm α}
  proof: by
  set q := n / #g.support
  set r := n % #g.support
  have div_euc : r + #g.support * q = n ∧ 0 <= r ∧ r < #g.support := by
    rw [← Int.ediv_emod_unique _]
    · exact ⟨rfl, rfl⟩
    simp only [Int.natCast_pos]
    apply lt_of_lt_of_le _ (IsCycle.two_le_card_support hg); simp
  simp only [← hg.

中文:
定理 cycle_zpow_mem_support_iff
  结论: {g : 置换 α}
  证明: by
  set q := n / #g.support
  set r := n % #g.support
  have div_euc : r + #g.support * q = n ∧ 0 <= r ∧ r < #g.support := by
    rw [← Int.ediv_emod_unique _]
    · exact ⟨rfl, rfl⟩
    simp only [Int.natCast_pos]
    apply lt_of_lt_of_le _ (IsCycle.two_le_card_support hg); simp
  simp only [← hg.

Depends on / 依赖: Int.ediv_emod_unique, Int.eq_ofNat_of_zero_le, Int.natCast_pos, IsCycle, IsCycle.two_le_card_support, Nat.cast_eq_zero, Nat.cast_lt, Nat.cast_nonneg, cast_eq_zero, cast_lt, cast_nonneg, div_euc, ediv_emod_unique, eq_ofNat_of_zero_le, g.support, hg.orderOf, lt_of_lt_of_le, natCast_pos, orderOf, support
-/
theorem cycle_zpow_mem_support_iff {g : Perm α}
    (hg : g.IsCycle) {n : Int} {x : α} (hx : g x != x) :
    (g ^ n) x = x ↔ n % #g.support = 0 := by
  set q := n / #g.support
  set r := n % #g.support
  have div_euc : r + #g.support * q = n ∧ 0 <= r ∧ r < #g.support := by
    rw [← Int.ediv_emod_unique _]
    · exact ⟨rfl, rfl⟩
    simp only [Int.natCast_pos]
    apply lt_of_lt_of_le _ (IsCycle.two_le_card_support hg); simp
  simp only [← hg.orderOf] at div_euc
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le div_euc.2.1
  simp only [hm, Nat.cast_nonneg, Nat.cast_lt, true_and] at div_euc
  rw [← div_euc.1]; rw [zpow_add g]
  simp only [hm, Nat.cast_eq_zero, zpow_natCast, coe_mul, comp_apply, zpow_mul,
    pow_orderOf_eq_one, one_zpow, coe_one, id_eq]
  have : (g ^ m) x = x ↔ g ^ m = 1 := by
    constructor
    · intro hgm
      simp only [IsCycle.pow_eq_one_iff hg]
      use x
    · intro hgm
      simp only [hgm, coe_one, id_eq]
  rw [this]
  by_cases hm0 : m = 0
  · simp only [hm0, pow_zero]
  · simp only [hm0, iff_false]
    exact pow_ne_one_of_lt_orderOf hm0 div_euc.2

end Perm

end Equiv
