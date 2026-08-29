/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yaël Dillies
-/
module

public import Mathlib.Data.List.Iterate
public import Mathlib.Data.Set.Pairwise.List
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Tactic.Group

/-!
# Cycle factors of a permutation

Let `β` be a `Fintype` and `f : Equiv.Perm β`.

* `Equiv.Perm.cycleOf`: `f.cycleOf x` is the cycle of `f` that `x` belongs to.
* `Equiv.Perm.cycleFactors`: `f.cycleFactors` is a list of disjoint cyclic permutations
  that multiply to `f`.
-/

@[expose] public section

open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

/-!
### `cycleOf`
-/

section CycleOf

variable {f g : Perm α} {x y : α}

/--
Definition of `cycleOf` / `cycleOf` 的定义

English:
definition cycleOf
  signature: (f : Perm α) [DecidableRel f.SameCycle] (x : α)
  body: ofSubtype (subtypePerm f fun _ => sameCycle_apply_right : Perm { y // SameCycle f x y })

中文:
定义 cycleOf
  签名: (f : 置换 α) [DecidableRel f.SameCycle] (x : α)
  定义体: ofSubtype (subtypePerm f fun _ => sameCycle_apply_right : Perm { y // SameCycle f x y })

Depends on / 依赖: SameCycle, ofSubtype, sameCycle_apply_right, subtypePerm
-/
def cycleOf (f : Perm α) [DecidableRel f.SameCycle] (x : α) : Perm α :=
  ofSubtype (subtypePerm f fun _ => sameCycle_apply_right : Perm { y // SameCycle f x y })

/--
theorem `cycleOf_apply` / 定理 `cycleOf_apply`

English:
theorem cycleOf_apply
  given: (f : Perm α) [DecidableRel f.SameCycle] (x y : α)
  proof: by
  dsimp only [cycleOf]
  split_ifs with h
  · apply ofSubtype_apply_of_mem
    exact h
  · apply ofSubtype_apply_of_not_mem
    exact h

中文:
定理 cycleOf_apply
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (x y : α)
  证明: by
  dsimp only [cycleOf]
  split_ifs with h
  · apply ofSubtype_apply_of_mem
    exact h
  · apply ofSubtype_apply_of_not_mem
    exact h

Depends on / 依赖: cycleOf, ofSubtype_apply_of_mem, ofSubtype_apply_of_not_mem, split_ifs
-/
theorem cycleOf_apply (f : Perm α) [DecidableRel f.SameCycle] (x y : α) :
    cycleOf f x y = if SameCycle f x y then f y else y := by
  dsimp only [cycleOf]
  split_ifs with h
  · apply ofSubtype_apply_of_mem
    exact h
  · apply ofSubtype_apply_of_not_mem
    exact h

/--
theorem `cycleOf_inv` / 定理 `cycleOf_inv`

English:
theorem cycleOf_inv
  given: (f : Perm α) [DecidableRel f.SameCycle] (x : α)
  proof: Equiv.ext fun y => by
    rw [inv_eq_iff_eq]; rw [cycleOf_apply]; rw [cycleOf_apply]
    split_ifs <;> simp_all [sameCycle_inv, sameCycle_symm_apply_right]

@[simp]

中文:
定理 cycleOf_inv
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (x : α)
  证明: Equiv.ext fun y => by
    rw [inv_eq_iff_eq]; rw [cycleOf_apply]; rw [cycleOf_apply]
    split_ifs <;> simp_all [sameCycle_inv, sameCycle_symm_apply_right]

@[simp]

Depends on / 依赖: Equiv.ext, cycleOf_apply, inv_eq_iff_eq, sameCycle_inv, sameCycle_symm_apply_right, split_ifs
-/
theorem cycleOf_inv (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    (cycleOf f x)⁻¹ = cycleOf f⁻¹ x :=
  Equiv.ext fun y => by
    rw [inv_eq_iff_eq]; rw [cycleOf_apply]; rw [cycleOf_apply]
    split_ifs <;> simp_all [sameCycle_inv, sameCycle_symm_apply_right]

@[simp]
/--
theorem `cycleOf_pow_apply_self` / 定理 `cycleOf_pow_apply_self`

English:
theorem cycleOf_pow_apply_self
  given: (f : Perm α) [DecidableRel f.SameCycle] (x : α)
  proof: by
  intro n
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ']; rw [mul_apply]; rw [cycleOf_apply]; rw [hn]; rw [if_pos]; rw [pow_succ']; rw [mul_apply]
    exact ⟨n, rfl⟩

@[simp]

中文:
定理 cycleOf_pow_apply_self
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (x : α)
  证明: by
  intro n
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ']; rw [mul_apply]; rw [cycleOf_apply]; rw [hn]; rw [if_pos]; rw [pow_succ']; rw [mul_apply]
    exact ⟨n, rfl⟩

@[simp]

Depends on / 依赖: cycleOf_apply, if_pos, mul_apply, pow_succ
-/
theorem cycleOf_pow_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    forall n : Nat, (cycleOf f x ^ n) x = (f ^ n) x := by
  intro n
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ']; rw [mul_apply]; rw [cycleOf_apply]; rw [hn]; rw [if_pos]; rw [pow_succ']; rw [mul_apply]
    exact ⟨n, rfl⟩

@[simp]
/--
theorem `cycleOf_zpow_apply_self` / 定理 `cycleOf_zpow_apply_self`

English:
theorem cycleOf_zpow_apply_self
  given: (f : Perm α) [DecidableRel f.SameCycle] (x : α)
  proof: by
  intro z
  cases z with
  | ofNat z => exact cycleOf_pow_apply_self f x z
  | negSucc z =>
    rw [zpow_negSucc]; rw [← inv_pow]; rw [cycleOf_inv]; rw [zpow_negSucc]; rw [← inv_pow]; rw [cycleOf_pow_apply_self]

中文:
定理 cycleOf_zpow_apply_self
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (x : α)
  证明: by
  intro z
  cases z with
  | ofNat z => exact cycleOf_pow_apply_self f x z
  | negSucc z =>
    rw [zpow_negSucc]; rw [← inv_pow]; rw [cycleOf_inv]; rw [zpow_negSucc]; rw [← inv_pow]; rw [cycleOf_pow_apply_self]

Depends on / 依赖: cycleOf_inv, cycleOf_pow_apply_self, inv_pow, negSucc, zpow_negSucc
-/
theorem cycleOf_zpow_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    forall n : Int, (cycleOf f x ^ n) x = (f ^ n) x := by
  intro z
  cases z with
  | ofNat z => exact cycleOf_pow_apply_self f x z
  | negSucc z =>
    rw [zpow_negSucc]; rw [← inv_pow]; rw [cycleOf_inv]; rw [zpow_negSucc]; rw [← inv_pow]; rw [cycleOf_pow_apply_self]

/--
theorem `SameCycle.cycleOf_apply` / 定理 `SameCycle.cycleOf_apply`

English:
theorem SameCycle.cycleOf_apply
  given: [DecidableRel f.SameCycle]
  proof: ofSubtype_apply_of_mem _

中文:
定理 SameCycle.cycleOf_apply
  条件: [DecidableRel f.SameCycle]
  证明: ofSubtype_apply_of_mem _

Depends on / 依赖: ofSubtype_apply_of_mem
-/
theorem SameCycle.cycleOf_apply [DecidableRel f.SameCycle] :
    SameCycle f x y -> cycleOf f x y = f y :=
  ofSubtype_apply_of_mem _

/--
theorem `cycleOf_apply_of_not_sameCycle` / 定理 `cycleOf_apply_of_not_sameCycle`

English:
theorem cycleOf_apply_of_not_sameCycle
  given: [DecidableRel f.SameCycle]
  proof: ofSubtype_apply_of_not_mem _

中文:
定理 cycleOf_apply_of_not_sameCycle
  条件: [DecidableRel f.SameCycle]
  证明: ofSubtype_apply_of_not_mem _

Depends on / 依赖: ofSubtype_apply_of_not_mem
-/
theorem cycleOf_apply_of_not_sameCycle [DecidableRel f.SameCycle] :
    ¬SameCycle f x y -> cycleOf f x y = y :=
  ofSubtype_apply_of_not_mem _

/--
theorem `SameCycle.cycleOf_eq` / 定理 `SameCycle.cycleOf_eq`

English:
theorem SameCycle.cycleOf_eq
  given: [DecidableRel f.SameCycle] (h : SameCycle f x y)
  proof: by
  ext z
  rw [Equiv.Perm.cycleOf_apply]
  split_ifs with hz
  · exact (h.symm.trans hz).cycleOf_apply.symm
  · exact (cycleOf_apply_of_not_sameCycle (mt h.trans hz)).symm

@[simp]

中文:
定理 SameCycle.cycleOf_eq
  条件: [DecidableRel f.SameCycle] (h : SameCycle f x y)
  证明: by
  ext z
  rw [Equiv.Perm.cycleOf_apply]
  split_ifs with hz
  · exact (h.symm.trans hz).cycleOf_apply.symm
  · exact (cycleOf_apply_of_not_sameCycle (mt h.trans hz)).symm

@[simp]

Depends on / 依赖: Equiv.Perm.cycleOf_apply, cycleOf_apply, cycleOf_apply.symm, cycleOf_apply_of_not_sameCycle, h.symm.trans, h.trans, split_ifs
-/
theorem SameCycle.cycleOf_eq [DecidableRel f.SameCycle] (h : SameCycle f x y) :
    cycleOf f x = cycleOf f y := by
  ext z
  rw [Equiv.Perm.cycleOf_apply]
  split_ifs with hz
  · exact (h.symm.trans hz).cycleOf_apply.symm
  · exact (cycleOf_apply_of_not_sameCycle (mt h.trans hz)).symm

@[simp]
/--
theorem `cycleOf_apply_apply_zpow_self` / 定理 `cycleOf_apply_apply_zpow_self`

English:
theorem cycleOf_apply_apply_zpow_self
  given: (f : Perm α) [DecidableRel f.SameCycle] (x : α) (k : Int)
  proof: by
  rw [SameCycle.cycleOf_apply]
  · rw [add_comm, zpow_add, zpow_one, mul_apply]
  · exact ⟨k, rfl⟩

@[simp]

中文:
定理 cycleOf_apply_apply_zpow_self
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (x : α) (k : 整数)
  证明: by
  rw [SameCycle.cycleOf_apply]
  · rw [add_comm, zpow_add, zpow_one, mul_apply]
  · exact ⟨k, rfl⟩

@[simp]

Depends on / 依赖: SameCycle, SameCycle.cycleOf_apply, add_comm, cycleOf_apply, mul_apply, zpow_add, zpow_one
-/
theorem cycleOf_apply_apply_zpow_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) (k : Int) :
    cycleOf f x ((f ^ k) x) = (f ^ (k + 1) : Perm α) x := by
  rw [SameCycle.cycleOf_apply]
  · rw [add_comm, zpow_add, zpow_one, mul_apply]
  · exact ⟨k, rfl⟩

@[simp]
/--
theorem `cycleOf_apply_apply_pow_self` / 定理 `cycleOf_apply_apply_pow_self`

English:
theorem cycleOf_apply_apply_pow_self
  given: (f : Perm α) [DecidableRel f.SameCycle] (x : α) (k : Nat)
  proof: by
  convert! cycleOf_apply_apply_zpow_self f x k using 1

@[simp]

中文:
定理 cycleOf_apply_apply_pow_self
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (x : α) (k : 自然数)
  证明: by
  convert! cycleOf_apply_apply_zpow_self f x k using 1

@[simp]

Depends on / 依赖: convert, cycleOf_apply_apply_zpow_self
-/
theorem cycleOf_apply_apply_pow_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) (k : Nat) :
    cycleOf f x ((f ^ k) x) = (f ^ (k + 1) : Perm α) x := by
  convert! cycleOf_apply_apply_zpow_self f x k using 1

@[simp]
/--
theorem `cycleOf_apply_apply_self` / 定理 `cycleOf_apply_apply_self`

English:
theorem cycleOf_apply_apply_self
  given: (f : Perm α) [DecidableRel f.SameCycle] (x : α)
  proof: by
  convert! cycleOf_apply_apply_pow_self f x 1 using 1

@[simp]

中文:
定理 cycleOf_apply_apply_self
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (x : α)
  证明: by
  convert! cycleOf_apply_apply_pow_self f x 1 using 1

@[simp]

Depends on / 依赖: convert, cycleOf_apply_apply_pow_self
-/
theorem cycleOf_apply_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    cycleOf f x (f x) = f (f x) := by
  convert! cycleOf_apply_apply_pow_self f x 1 using 1

@[simp]
/--
theorem `cycleOf_apply_self` / 定理 `cycleOf_apply_self`

English:
theorem cycleOf_apply_self
  given: (f : Perm α) [DecidableRel f.SameCycle] (x : α)
  statement: cycleOf f x x = f x
  proof: SameCycle.rfl.cycleOf_apply

中文:
定理 cycleOf_apply_self
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (x : α)
  结论: cycleOf f x x = f x
  证明: SameCycle.rfl.cycleOf_apply

Depends on / 依赖: SameCycle, SameCycle.rfl.cycleOf_apply, cycleOf_apply
-/
theorem cycleOf_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) : cycleOf f x x = f x :=
  SameCycle.rfl.cycleOf_apply

/--
theorem `IsCycle.cycleOf_eq` / 定理 `IsCycle.cycleOf_eq`

English:
theorem IsCycle.cycleOf_eq
  statement: [DecidableRel f.SameCycle]
  proof: Equiv.ext fun y =>
    if h : SameCycle f x y then by rw [h.cycleOf_apply]
    else by
      rw [cycleOf_apply_of_not_sameCycle h]; rw [Classical.not_not.1 (mt ((isCycle_iff_sameCycle hx).1 hf).2 h)]

@[simp]

中文:
定理 是环.cycleOf_eq
  结论: [DecidableRel f.SameCycle]
  证明: Equiv.ext fun y =>
    if h : SameCycle f x y then by rw [h.cycleOf_apply]
    else by
      rw [cycleOf_apply_of_not_sameCycle h]; rw [Classical.not_not.1 (mt ((isCycle_iff_sameCycle hx).1 hf).2 h)]

@[simp]

Depends on / 依赖: Classical, Classical.not_not, Equiv.ext, SameCycle, cycleOf_apply, cycleOf_apply_of_not_sameCycle, h.cycleOf_apply, isCycle_iff_sameCycle, not_not
-/
theorem IsCycle.cycleOf_eq [DecidableRel f.SameCycle]
    (hf : IsCycle f) (hx : f x != x) : cycleOf f x = f :=
  Equiv.ext fun y =>
    if h : SameCycle f x y then by rw [h.cycleOf_apply]
    else by
      rw [cycleOf_apply_of_not_sameCycle h]; rw [Classical.not_not.1 (mt ((isCycle_iff_sameCycle hx).1 hf).2 h)]

@[simp]
/--
theorem `cycleOf_eq_one_iff` / 定理 `cycleOf_eq_one_iff`

English:
theorem cycleOf_eq_one_iff
  given: (f : Perm α) [DecidableRel f.SameCycle]
  statement: cycleOf f x = 1 ↔ f x = x
  proof: by
  simp_rw [Perm.ext_iff, cycleOf_apply, one_apply]
  refine ⟨fun h => (if_pos (SameCycle.refl f x)).symm.trans (h x), fun h y => ?_⟩
  by_cases hy : f y = y
  · rw [hy, ite_self]
  · exact if_neg (mt SameCycle.apply_eq_self_iff (by tauto))

@[simp]

中文:
定理 cycleOf_eq_one_iff
  条件: (f : 置换 α) [DecidableRel f.SameCycle]
  结论: cycleOf f x = 1 ↔ f x = x
  证明: by
  simp_rw [Perm.ext_iff, cycleOf_apply, one_apply]
  refine ⟨fun h => (if_pos (SameCycle.refl f x)).symm.trans (h x), fun h y => ?_⟩
  by_cases hy : f y = y
  · rw [hy, ite_self]
  · exact if_neg (mt SameCycle.apply_eq_self_iff (by tauto))

@[simp]

Depends on / 依赖: Perm.ext_iff, SameCycle, SameCycle.apply_eq_self_iff, SameCycle.refl, apply_eq_self_iff, cycleOf_apply, ext_iff, if_neg, if_pos, ite_self, one_apply, simp_rw, symm.trans
-/
theorem cycleOf_eq_one_iff (f : Perm α) [DecidableRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x := by
  simp_rw [Perm.ext_iff, cycleOf_apply, one_apply]
  refine ⟨fun h => (if_pos (SameCycle.refl f x)).symm.trans (h x), fun h y => ?_⟩
  by_cases hy : f y = y
  · rw [hy, ite_self]
  · exact if_neg (mt SameCycle.apply_eq_self_iff (by tauto))

@[simp]
/--
theorem `cycleOf_self_apply` / 定理 `cycleOf_self_apply`

English:
theorem cycleOf_self_apply
  given: (f : Perm α) [DecidableRel f.SameCycle] (x : α)
  proof: (sameCycle_apply_right.2 SameCycle.rfl).symm.cycleOf_eq

@[simp]

中文:
定理 cycleOf_self_apply
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (x : α)
  证明: (sameCycle_apply_right.2 SameCycle.rfl).symm.cycleOf_eq

@[simp]

Depends on / 依赖: SameCycle, SameCycle.rfl, cycleOf_eq, sameCycle_apply_right, symm.cycleOf_eq
-/
theorem cycleOf_self_apply (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    cycleOf f (f x) = cycleOf f x :=
  (sameCycle_apply_right.2 SameCycle.rfl).symm.cycleOf_eq

@[simp]
/--
theorem `cycleOf_self_apply_pow` / 定理 `cycleOf_self_apply_pow`

English:
theorem cycleOf_self_apply_pow
  given: (f : Perm α) [DecidableRel f.SameCycle] (n : Nat) (x : α)
  proof: SameCycle.rfl.pow_left.cycleOf_eq

@[simp]

中文:
定理 cycleOf_self_apply_pow
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (n : 自然数) (x : α)
  证明: SameCycle.rfl.pow_left.cycleOf_eq

@[simp]

Depends on / 依赖: SameCycle, SameCycle.rfl.pow_left.cycleOf_eq, cycleOf_eq, pow_left
-/
theorem cycleOf_self_apply_pow (f : Perm α) [DecidableRel f.SameCycle] (n : Nat) (x : α) :
    cycleOf f ((f ^ n) x) = cycleOf f x :=
  SameCycle.rfl.pow_left.cycleOf_eq

@[simp]
/--
theorem `cycleOf_self_apply_zpow` / 定理 `cycleOf_self_apply_zpow`

English:
theorem cycleOf_self_apply_zpow
  given: (f : Perm α) [DecidableRel f.SameCycle] (n : Int) (x : α)
  proof: SameCycle.rfl.zpow_left.cycleOf_eq

中文:
定理 cycleOf_self_apply_zpow
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (n : 整数) (x : α)
  证明: SameCycle.rfl.zpow_left.cycleOf_eq

Depends on / 依赖: SameCycle, SameCycle.rfl.zpow_left.cycleOf_eq, cycleOf_eq, zpow_left
-/
theorem cycleOf_self_apply_zpow (f : Perm α) [DecidableRel f.SameCycle] (n : Int) (x : α) :
    cycleOf f ((f ^ n) x) = cycleOf f x :=
  SameCycle.rfl.zpow_left.cycleOf_eq

/--
theorem `IsCycle.cycleOf` / 定理 `IsCycle.cycleOf`

English:
theorem IsCycle.cycleOf
  statement: [DecidableRel f.SameCycle] [DecidableEq α]
  proof: by
  by_cases hx : f x = x
  · rwa [if_pos hx, cycleOf_eq_one_iff]
  · rwa [if_neg hx, hf.cycleOf_eq]

中文:
定理 是环.cycleOf
  结论: [DecidableRel f.SameCycle] [DecidableEq α]
  证明: by
  by_cases hx : f x = x
  · rwa [if_pos hx, cycleOf_eq_one_iff]
  · rwa [if_neg hx, hf.cycleOf_eq]
-/
protected theorem IsCycle.cycleOf [DecidableRel f.SameCycle] [DecidableEq α]
    (hf : IsCycle f) : cycleOf f x = if f x = x then 1 else f := by
  by_cases hx : f x = x
  · rwa [if_pos hx, cycleOf_eq_one_iff]
  · rwa [if_neg hx, hf.cycleOf_eq]

/--
theorem `cycleOf_one` / 定理 `cycleOf_one`

English:
theorem cycleOf_one
  given: [DecidableRel (1 : Perm α).SameCycle] (x : α)
  proof: (cycleOf_eq_one_iff 1).mpr rfl

中文:
定理 cycleOf_one
  条件: [DecidableRel (1 : 置换 α).SameCycle] (x : α)
  证明: (cycleOf_eq_one_iff 1).mpr rfl

Depends on / 依赖: cycleOf_eq_one_iff
-/
theorem cycleOf_one [DecidableRel (1 : Perm α).SameCycle] (x : α) :
    cycleOf 1 x = 1 := (cycleOf_eq_one_iff 1).mpr rfl

/--
theorem `isCycle_cycleOf` / 定理 `isCycle_cycleOf`

English:
theorem isCycle_cycleOf
  given: (f : Perm α) [DecidableRel f.SameCycle] (hx : f x != x)
  proof: have : cycleOf f x x != x := by rwa [SameCycle.rfl.cycleOf_apply]
  (isCycle_iff_sameCycle this).2 @fun y =>
    ⟨fun h => mt h.apply_eq_self_iff.2 this, fun h =>
      if hxy : SameCycle f x y then
        let ⟨i, hi⟩ := hxy
        ⟨i, by rw [cycleOf_zpow_apply_self, hi]⟩
      else by
        rw [cycleOf_apply_of_not_sameCycle hxy] at h
        exact (h rfl).elim⟩

中文:
定理 isCycle_cycleOf
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (hx : f x != x)
  证明: have : cycleOf f x x != x := by rwa [SameCycle.rfl.cycleOf_apply]
  (isCycle_iff_sameCycle this).2 @fun y =>
    ⟨fun h => mt h.apply_eq_self_iff.2 this, fun h =>
      if hxy : SameCycle f x y then
        let ⟨i, hi⟩ := hxy
        ⟨i, by rw [cycleOf_zpow_apply_self, hi]⟩
      else by
        rw [cycleOf_apply_of_not_sameCycle hxy] at h
        exact (h rfl).elim⟩

Depends on / 依赖: SameCycle, SameCycle.rfl.cycleOf_apply, apply_eq_self_iff, cycleOf, cycleOf_apply, cycleOf_apply_of_not_sameCycle, cycleOf_zpow_apply_self, h.apply_eq_self_iff, isCycle_iff_sameCycle
-/
theorem isCycle_cycleOf (f : Perm α) [DecidableRel f.SameCycle] (hx : f x != x) :
    IsCycle (cycleOf f x) :=
  have : cycleOf f x x != x := by rwa [SameCycle.rfl.cycleOf_apply]
  (isCycle_iff_sameCycle this).2 @fun y =>
    ⟨fun h => mt h.apply_eq_self_iff.2 this, fun h =>
      if hxy : SameCycle f x y then
        let ⟨i, hi⟩ := hxy
        ⟨i, by rw [cycleOf_zpow_apply_self, hi]⟩
      else by
        rw [cycleOf_apply_of_not_sameCycle hxy] at h
        exact (h rfl).elim⟩

/--
theorem `pow_mod_orderOf_cycleOf_apply` / 定理 `pow_mod_orderOf_cycleOf_apply`

English:
theorem pow_mod_orderOf_cycleOf_apply
  given: (f : Perm α) [DecidableRel f.SameCycle] (n : Nat) (x : α)
  proof: by
  rw [← cycleOf_pow_apply_self f]; rw [← cycleOf_pow_apply_self f]; rw [pow_mod_orderOf]

中文:
定理 pow_mod_orderOf_cycleOf_apply
  条件: (f : 置换 α) [DecidableRel f.SameCycle] (n : 自然数) (x : α)
  证明: by
  rw [← cycleOf_pow_apply_self f]; rw [← cycleOf_pow_apply_self f]; rw [pow_mod_orderOf]

Depends on / 依赖: cycleOf_pow_apply_self, pow_mod_orderOf
-/
theorem pow_mod_orderOf_cycleOf_apply (f : Perm α) [DecidableRel f.SameCycle] (n : Nat) (x : α) :
    (f ^ (n % orderOf (cycleOf f x))) x = (f ^ n) x := by
  rw [← cycleOf_pow_apply_self f]; rw [← cycleOf_pow_apply_self f]; rw [pow_mod_orderOf]

/--
theorem `cycleOf_mul_of_apply_right_eq_self` / 定理 `cycleOf_mul_of_apply_right_eq_self`

English:
theorem cycleOf_mul_of_apply_right_eq_self
  statement: [DecidableRel f.SameCycle]
  proof: by
  ext y
  by_cases hxy : (f * g).SameCycle x y
  · obtain ⟨z, rfl⟩ := hxy
    rw [cycleOf_apply_apply_zpow_self]
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]
  · rw [cycleOf_apply_of_not_sameCycle hxy, cycleOf_apply_of_not_sameCycle]
    contrapose hxy
    obtain ⟨z, rfl⟩ := hxy
    refine ⟨z, ?_⟩
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]

中文:
定理 cycleOf_mul_of_apply_right_eq_self
  结论: [DecidableRel f.SameCycle]
  证明: by
  ext y
  by_cases hxy : (f * g).SameCycle x y
  · obtain ⟨z, rfl⟩ := hxy
    rw [cycleOf_apply_apply_zpow_self]
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]
  · rw [cycleOf_apply_of_not_sameCycle hxy, cycleOf_apply_of_not_sameCycle]
    contrapose hxy
    obtain ⟨z, rfl⟩ := hxy
    refine ⟨z, ?_⟩
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]

Depends on / 依赖: SameCycle, contrapose, cycleOf_apply_apply_zpow_self, cycleOf_apply_of_not_sameCycle, h.mul_zpow, mul_zpow, zpow_apply_eq_self_of_apply_eq_self
-/
theorem cycleOf_mul_of_apply_right_eq_self [DecidableRel f.SameCycle]
    [DecidableRel (f * g).SameCycle]
    (h : Commute f g) (x : α) (hx : g x = x) : (f * g).cycleOf x = f.cycleOf x := by
  ext y
  by_cases hxy : (f * g).SameCycle x y
  · obtain ⟨z, rfl⟩ := hxy
    rw [cycleOf_apply_apply_zpow_self]
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]
  · rw [cycleOf_apply_of_not_sameCycle hxy, cycleOf_apply_of_not_sameCycle]
    contrapose hxy
    obtain ⟨z, rfl⟩ := hxy
    refine ⟨z, ?_⟩
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]

/--
theorem `Disjoint.cycleOf_mul_distrib` / 定理 `Disjoint.cycleOf_mul_distrib`

English:
theorem Disjoint.cycleOf_mul_distrib
  statement: [DecidableRel f.SameCycle] [DecidableRel g.SameCycle]
  proof: by
  classical
  rcases (disjoint_iff_eq_or_eq.mp h) x with hfx | hgx
  · simp [h.commute.eq, cycleOf_mul_of_apply_right_eq_self h.symm.commute, hfx]
  · simp [cycleOf_mul_of_apply_right_eq_self h.commute, hgx]

中文:
定理 Disjoint.cycleOf_mul_distrib
  结论: [DecidableRel f.SameCycle] [DecidableRel g.SameCycle]
  证明: by
  classical
  rcases (disjoint_iff_eq_or_eq.mp h) x with hfx | hgx
  · simp [h.commute.eq, cycleOf_mul_of_apply_right_eq_self h.symm.commute, hfx]
  · simp [cycleOf_mul_of_apply_right_eq_self h.commute, hgx]

Depends on / 依赖: classical, commute, cycleOf_mul_of_apply_right_eq_self, disjoint_iff_eq_or_eq, disjoint_iff_eq_or_eq.mp, h.commute, h.commute.eq, h.symm.commute
-/
theorem Disjoint.cycleOf_mul_distrib [DecidableRel f.SameCycle] [DecidableRel g.SameCycle]
    [DecidableRel (f * g).SameCycle] (h : f.Disjoint g) (x : α) :
    (f * g).cycleOf x = f.cycleOf x * g.cycleOf x := by
  classical
  rcases (disjoint_iff_eq_or_eq.mp h) x with hfx | hgx
  · simp [h.commute.eq, cycleOf_mul_of_apply_right_eq_self h.symm.commute, hfx]
  · simp [cycleOf_mul_of_apply_right_eq_self h.commute, hgx]

/--
theorem `mem_support_cycleOf_iff_aux` / 定理 `mem_support_cycleOf_iff_aux`

English:
theorem mem_support_cycleOf_iff_aux
  given: [DecidableRel f.SameCycle] [DecidableEq α] [Fintype α]
  proof: by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff _).mpr hx]
    simp [hx]
  · rw [mem_support, cycleOf_apply]
    split_ifs with hy
    · simp only [hx, hy, Ne, not_false_iff, and_self_iff, mem_support]
      rcases hy with ⟨k, rfl⟩
      rw [← notMem_support]
      simpa using hx
    · simpa [hx] using hy

中文:
定理 mem_support_cycleOf_iff_aux
  条件: [DecidableRel f.SameCycle] [DecidableEq α] [有限类型 α]
  证明: by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff _).mpr hx]
    simp [hx]
  · rw [mem_support, cycleOf_apply]
    split_ifs with hy
    · simp only [hx, hy, Ne, not_false_iff, and_self_iff, mem_support]
      rcases hy with ⟨k, rfl⟩
      rw [← notMem_support]
      simpa using hx
    · simpa [hx] using hy
-/
private theorem mem_support_cycleOf_iff_aux [DecidableRel f.SameCycle] [DecidableEq α] [Fintype α] :
    y in support (f.cycleOf x) ↔ SameCycle f x y ∧ x in support f := by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff _).mpr hx]
    simp [hx]
  · rw [mem_support, cycleOf_apply]
    split_ifs with hy
    · simp only [hx, hy, Ne, not_false_iff, and_self_iff, mem_support]
      rcases hy with ⟨k, rfl⟩
      rw [← notMem_support]
      simpa using hx
    · simpa [hx] using hy

/--
theorem `mem_support_cycleOf_iff'_aux` / 定理 `mem_support_cycleOf_iff'_aux`

English:
theorem mem_support_cycleOf_iff'_aux
  statement: (hx : f x != x)
  proof: by
  rw [mem_support_cycleOf_iff_aux]; rw [and_iff_left (mem_support.2 hx)]

中文:
定理 mem_support_cycleOf_iff'_aux
  结论: (hx : f x != x)
  证明: by
  rw [mem_support_cycleOf_iff_aux]; rw [and_iff_left (mem_support.2 hx)]
-/
private theorem mem_support_cycleOf_iff'_aux (hx : f x != x)
    [DecidableRel f.SameCycle] [DecidableEq α] [Fintype α] :
    y in support (f.cycleOf x) ↔ SameCycle f x y := by
  rw [mem_support_cycleOf_iff_aux]; rw [and_iff_left (mem_support.2 hx)]

/--
theorem `isCycle_cycleOf_iff` / 定理 `isCycle_cycleOf_iff`

English:
theorem isCycle_cycleOf_iff
  given: (f : Perm α) [DecidableRel f.SameCycle]
  proof: by
  refine ⟨fun hx => ?_, f.isCycle_cycleOf⟩
  rw [Ne]; rw [← cycleOf_eq_one_iff f]
  exact hx.ne_one

中文:
定理 isCycle_cycleOf_iff
  条件: (f : 置换 α) [DecidableRel f.SameCycle]
  证明: by
  refine ⟨fun hx => ?_, f.isCycle_cycleOf⟩
  rw [Ne]; rw [← cycleOf_eq_one_iff f]
  exact hx.ne_one

Depends on / 依赖: cycleOf_eq_one_iff, f.isCycle_cycleOf, hx.ne_one, isCycle_cycleOf, ne_one
-/
theorem isCycle_cycleOf_iff (f : Perm α) [DecidableRel f.SameCycle] :
    IsCycle (cycleOf f x) ↔ f x != x := by
  refine ⟨fun hx => ?_, f.isCycle_cycleOf⟩
  rw [Ne]; rw [← cycleOf_eq_one_iff f]
  exact hx.ne_one

/--
theorem `isCycleOn_support_cycleOf_aux` / 定理 `isCycleOn_support_cycleOf_aux`

English:
theorem isCycleOn_support_cycleOf_aux
  statement: [DecidableEq α] [Fintype α] (f : Perm α)
  proof: ⟨f.bijOn by
    refine fun _ =>
        ⟨fun h => mem_support_cycleOf_iff_aux.2 ?_, fun h => mem_support_cycleOf_iff_aux.2 ?_⟩
    · exact ⟨sameCycle_apply_right.1 (mem_support_cycleOf_iff_aux.1 h).1,
      (mem_support_cycleOf_iff_aux.1 h).2⟩
    · exact ⟨sameCycle_apply_right.2 (mem_support_cycleOf_iff_aux.1 h).1,
      (mem_support_cycleOf_iff_aux.1 h).2⟩,
    fun a ha b hb => by
      rw [mem_coe]; rw [mem_support_cycleOf_iff_aux] at ha hb
      exact ha.1.symm.trans hb.1⟩

中文:
定理 isCycleOn_support_cycleOf_aux
  结论: [DecidableEq α] [有限类型 α] (f : 置换 α)
  证明: ⟨f.bijOn by
    refine fun _ =>
        ⟨fun h => mem_support_cycleOf_iff_aux.2 ?_, fun h => mem_support_cycleOf_iff_aux.2 ?_⟩
    · exact ⟨sameCycle_apply_right.1 (mem_support_cycleOf_iff_aux.1 h).1,
      (mem_support_cycleOf_iff_aux.1 h).2⟩
    · exact ⟨sameCycle_apply_right.2 (mem_support_cycleOf_iff_aux.1 h).1,
      (mem_support_cycleOf_iff_aux.1 h).2⟩,
    fun a ha b hb => by
      rw [mem_coe]; rw [mem_support_cycleOf_iff_aux] at ha hb
      exact ha.1.symm.trans hb.1⟩
-/
private theorem isCycleOn_support_cycleOf_aux [DecidableEq α] [Fintype α] (f : Perm α)
    [DecidableRel f.SameCycle] (x : α) : f.IsCycleOn (f.cycleOf x).support :=
⟨f.bijOn by
    refine fun _ =>
        ⟨fun h => mem_support_cycleOf_iff_aux.2 ?_, fun h => mem_support_cycleOf_iff_aux.2 ?_⟩
    · exact ⟨sameCycle_apply_right.1 (mem_support_cycleOf_iff_aux.1 h).1,
      (mem_support_cycleOf_iff_aux.1 h).2⟩
    · exact ⟨sameCycle_apply_right.2 (mem_support_cycleOf_iff_aux.1 h).1,
      (mem_support_cycleOf_iff_aux.1 h).2⟩,
    fun a ha b hb => by
      rw [mem_coe]; rw [mem_support_cycleOf_iff_aux] at ha hb
      exact ha.1.symm.trans hb.1⟩

/--
theorem `SameCycle.exists_pow_eq_of_mem_support_aux` / 定理 `SameCycle.exists_pow_eq_of_mem_support_aux`

English:
theorem SameCycle.exists_pow_eq_of_mem_support_aux
  statement: {f} [DecidableEq α] [Fintype α]
  proof: by
  rw [mem_support] at hx
  exact Equiv.Perm.IsCycleOn.exists_pow_eq (b := y) (f.isCycleOn_support_cycleOf_aux x)
    (by rw [mem_support_cycleOf_iff'_aux hx]) (by rwa [mem_support_cycleOf_iff'_aux hx])

中文:
定理 SameCycle.存在_pow_eq_of_mem_support_aux
  结论: {f} [DecidableEq α] [有限类型 α]
  证明: by
  rw [mem_support] at hx
  exact Equiv.Perm.IsCycleOn.exists_pow_eq (b := y) (f.isCycleOn_support_cycleOf_aux x)
    (by rw [mem_support_cycleOf_iff'_aux hx]) (by rwa [mem_support_cycleOf_iff'_aux hx])
-/
private theorem SameCycle.exists_pow_eq_of_mem_support_aux {f} [DecidableEq α] [Fintype α]
    [DecidableRel f.SameCycle] (h : SameCycle f x y) (hx : x in f.support) :
    exists i < #(f.cycleOf x).support, (f ^ i) x = y := by
  rw [mem_support] at hx
  exact Equiv.Perm.IsCycleOn.exists_pow_eq (b := y) (f.isCycleOn_support_cycleOf_aux x)
    (by rw [mem_support_cycleOf_iff'_aux hx]) (by rwa [mem_support_cycleOf_iff'_aux hx])

/--
Instance `instDecidableRelSameCycle` / 实例 `instDecidableRelSameCycle`

English:
instance instDecidableRelSameCycle
  signature: [DecidableEq α] [Fintype α] (f : Perm α)
  body: fun x y =>
decidable_of_iff (y in List.iterate f x (Fintype.card α)) by
    simp only [List.mem_iterate, iterate_eq_pow, eq_comm (a := y)]
    constructor
    · rintro ⟨n, _, hn⟩
      exact ⟨n, hn⟩
    · intro hxy
      by_cases hx : x in f.support
      case pos =>
        -- we can't invoke the aux lemmas above without obtaining the decidable instance we are
        -- already building; but now we've left the data, so we can do this non-constructively
        -- without sacrificing computability.
        let _inst (f : Perm α) : DecidableRel (SameCycle f) := Classical.decRel _
        rcases hxy.exists_pow_eq_of_mem_support_aux hx with ⟨i, hixy, hi⟩
        refine ⟨i, lt_of_lt_of_le hixy (card_le_univ _), hi⟩
      case neg =>
        have : Nonempty α := ⟨x⟩
        rw [notMem_support] at hx
        exact ⟨0, Fintype.card_pos, hxy.eq_of_left hx⟩

@[simp]

中文:
实例 instDecidableRelSameCycle
  签名: [DecidableEq α] [有限类型 α] (f : 置换 α)
  定义体: fun x y =>
decidable_of_iff (y in List.iterate f x (Fintype.card α)) by
    simp only [List.mem_iterate, iterate_eq_pow, eq_comm (a := y)]
    constructor
    · rintro ⟨n, _, hn⟩
      exact ⟨n, hn⟩
    · intro hxy
      by_cases hx : x in f.support
      case pos =>
        -- we can't invoke the aux lemmas above without obtaining the decidable instance we are
        -- already building; but now we've left the data, so we can do this non-constructively
        -- without sacrificing computability.
        let _inst (f : Perm α) : DecidableRel (SameCycle f) := Classical.decRel _
        rcases hxy.exists_pow_eq_of_mem_support_aux hx with ⟨i, hixy, hi⟩
        refine ⟨i, lt_of_lt_of_le hixy (card_le_univ _), hi⟩
      case neg =>
        have : Nonempty α := ⟨x⟩
        rw [notMem_support] at hx
        exact ⟨0, Fintype.card_pos, hxy.eq_of_left hx⟩

@[simp]
-/
instance instDecidableRelSameCycle [DecidableEq α] [Fintype α] (f : Perm α) :
    DecidableRel (SameCycle f) := fun x y =>
decidable_of_iff (y in List.iterate f x (Fintype.card α)) by
    simp only [List.mem_iterate, iterate_eq_pow, eq_comm (a := y)]
    constructor
    · rintro ⟨n, _, hn⟩
      exact ⟨n, hn⟩
    · intro hxy
      by_cases hx : x in f.support
      case pos =>
        -- we can't invoke the aux lemmas above without obtaining the decidable instance we are
        -- already building; but now we've left the data, so we can do this non-constructively
        -- without sacrificing computability.
        let _inst (f : Perm α) : DecidableRel (SameCycle f) := Classical.decRel _
        rcases hxy.exists_pow_eq_of_mem_support_aux hx with ⟨i, hixy, hi⟩
        refine ⟨i, lt_of_lt_of_le hixy (card_le_univ _), hi⟩
      case neg =>
        have : Nonempty α := ⟨x⟩
        rw [notMem_support] at hx
        exact ⟨0, Fintype.card_pos, hxy.eq_of_left hx⟩

@[simp]
/--
theorem `two_le_card_support_cycleOf_iff` / 定理 `two_le_card_support_cycleOf_iff`

English:
theorem two_le_card_support_cycleOf_iff
  given: [DecidableEq α] [Fintype α]
  proof: by
  refine ⟨fun h => ?_, fun h => by simpa using (isCycle_cycleOf _ h).two_le_card_support⟩
  contrapose! h
  rw [← cycleOf_eq_one_iff] at h
  simp [h]

中文:
定理 two_le_card_support_cycleOf_iff
  条件: [DecidableEq α] [有限类型 α]
  证明: by
  refine ⟨fun h => ?_, fun h => by simpa using (isCycle_cycleOf _ h).two_le_card_support⟩
  contrapose! h
  rw [← cycleOf_eq_one_iff] at h
  simp [h]

Depends on / 依赖: contrapose, cycleOf_eq_one_iff, isCycle_cycleOf, two_le_card_support
-/
theorem two_le_card_support_cycleOf_iff [DecidableEq α] [Fintype α] :
    2 <= #(cycleOf f x).support ↔ f x != x := by
  refine ⟨fun h => ?_, fun h => by simpa using (isCycle_cycleOf _ h).two_le_card_support⟩
  contrapose! h
  rw [← cycleOf_eq_one_iff] at h
  simp [h]

/--
lemma `support_cycleOf_nonempty` / 引理 `support_cycleOf_nonempty`

English:
lemma support_cycleOf_nonempty
  given: [DecidableEq α] [Fintype α]
  proof: by
  rw [← two_le_card_support_cycleOf_iff]; rw [← card_pos]; rw [← Nat.succ_le_iff]
  exact ⟨fun h => Or.resolve_left h.eq_or_lt (card_support_ne_one _).symm, zero_lt_two.trans_le⟩

中文:
引理 support_cycleOf_nonempty
  条件: [DecidableEq α] [有限类型 α]
  证明: by
  rw [← two_le_card_support_cycleOf_iff]; rw [← card_pos]; rw [← Nat.succ_le_iff]
  exact ⟨fun h => Or.resolve_left h.eq_or_lt (card_support_ne_one _).symm, zero_lt_two.trans_le⟩
-/
@[simp] lemma support_cycleOf_nonempty [DecidableEq α] [Fintype α] :
    (cycleOf f x).support.Nonempty ↔ f x != x := by
  rw [← two_le_card_support_cycleOf_iff]; rw [← card_pos]; rw [← Nat.succ_le_iff]
  exact ⟨fun h => Or.resolve_left h.eq_or_lt (card_support_ne_one _).symm, zero_lt_two.trans_le⟩

/--
theorem `mem_support_cycleOf_iff` / 定理 `mem_support_cycleOf_iff`

English:
theorem mem_support_cycleOf_iff
  given: [DecidableEq α] [Fintype α]
  proof: mem_support_cycleOf_iff_aux

中文:
定理 mem_support_cycleOf_iff
  条件: [DecidableEq α] [有限类型 α]
  证明: mem_support_cycleOf_iff_aux

Depends on / 依赖: mem_support_cycleOf_iff_aux
-/
theorem mem_support_cycleOf_iff [DecidableEq α] [Fintype α] :
    y in support (f.cycleOf x) ↔ SameCycle f x y ∧ x in support f :=
  mem_support_cycleOf_iff_aux

/--
theorem `mem_support_cycleOf_iff'` / 定理 `mem_support_cycleOf_iff'`

English:
theorem mem_support_cycleOf_iff'
  given: (hx : f x != x) [DecidableEq α] [Fintype α]
  proof: mem_support_cycleOf_iff'_aux hx

中文:
定理 mem_support_cycleOf_iff'
  条件: (hx : f x != x) [DecidableEq α] [有限类型 α]
  证明: mem_support_cycleOf_iff'_aux hx

Depends on / 依赖: _aux, mem_support_cycleOf_iff
-/
theorem mem_support_cycleOf_iff' (hx : f x != x) [DecidableEq α] [Fintype α] :
    y in support (f.cycleOf x) ↔ SameCycle f x y :=
  mem_support_cycleOf_iff'_aux hx

/--
theorem `sameCycle_iff_cycleOf_eq_of_mem_support` / 定理 `sameCycle_iff_cycleOf_eq_of_mem_support`

English:
theorem sameCycle_iff_cycleOf_eq_of_mem_support
  statement: [DecidableEq α] [Fintype α]
  proof: by
  refine ⟨SameCycle.cycleOf_eq, fun h => ?_⟩
  rw [← mem_support_cycleOf_iff' (mem_support.mp hx)]; rw [h]; rw [mem_support_cycleOf_iff' (mem_support.mp hy)]

中文:
定理 sameCycle_iff_cycleOf_eq_of_mem_support
  结论: [DecidableEq α] [有限类型 α]
  证明: by
  refine ⟨SameCycle.cycleOf_eq, fun h => ?_⟩
  rw [← mem_support_cycleOf_iff' (mem_support.mp hx)]; rw [h]; rw [mem_support_cycleOf_iff' (mem_support.mp hy)]

Depends on / 依赖: SameCycle, SameCycle.cycleOf_eq, cycleOf_eq, mem_support, mem_support.mp, mem_support_cycleOf_iff
-/
theorem sameCycle_iff_cycleOf_eq_of_mem_support [DecidableEq α] [Fintype α]
    {g : Perm α} {x y : α} (hx : x in g.support) (hy : y in g.support) :
    g.SameCycle x y ↔ g.cycleOf x = g.cycleOf y := by
  refine ⟨SameCycle.cycleOf_eq, fun h => ?_⟩
  rw [← mem_support_cycleOf_iff' (mem_support.mp hx)]; rw [h]; rw [mem_support_cycleOf_iff' (mem_support.mp hy)]

/--
theorem `support_cycleOf_eq_nil_iff` / 定理 `support_cycleOf_eq_nil_iff`

English:
theorem support_cycleOf_eq_nil_iff
  given: [DecidableEq α] [Fintype α]
  proof: by simp

中文:
定理 support_cycleOf_eq_nil_iff
  条件: [DecidableEq α] [有限类型 α]
  证明: by simp
-/
theorem support_cycleOf_eq_nil_iff [DecidableEq α] [Fintype α] :
    (f.cycleOf x).support = ∅ ↔ x ∉ f.support := by simp

/--
theorem `isCycleOn_support_cycleOf` / 定理 `isCycleOn_support_cycleOf`

English:
theorem isCycleOn_support_cycleOf
  given: [DecidableEq α] [Fintype α] (f : Perm α) (x : α)
  proof: isCycleOn_support_cycleOf_aux f x

中文:
定理 isCycleOn_support_cycleOf
  条件: [DecidableEq α] [有限类型 α] (f : 置换 α) (x : α)
  证明: isCycleOn_support_cycleOf_aux f x

Depends on / 依赖: isCycleOn_support_cycleOf_aux
-/
theorem isCycleOn_support_cycleOf [DecidableEq α] [Fintype α] (f : Perm α) (x : α) :
    f.IsCycleOn (f.cycleOf x).support :=
  isCycleOn_support_cycleOf_aux f x

/--
theorem `SameCycle.exists_pow_eq_of_mem_support` / 定理 `SameCycle.exists_pow_eq_of_mem_support`

English:
theorem SameCycle.exists_pow_eq_of_mem_support
  statement: {f} [DecidableEq α] [Fintype α] (h : SameCycle f x y)
  proof: h.exists_pow_eq_of_mem_support_aux hx

中文:
定理 SameCycle.存在_pow_eq_of_mem_support
  结论: {f} [DecidableEq α] [有限类型 α] (h : SameCycle f x y)
  证明: h.exists_pow_eq_of_mem_support_aux hx

Depends on / 依赖: exists_pow_eq_of_mem_support_aux, h.exists_pow_eq_of_mem_support_aux
-/
theorem SameCycle.exists_pow_eq_of_mem_support {f} [DecidableEq α] [Fintype α] (h : SameCycle f x y)
    (hx : x in f.support) : exists i < #(f.cycleOf x).support, (f ^ i) x = y :=
  h.exists_pow_eq_of_mem_support_aux hx

/--
theorem `support_cycleOf_le` / 定理 `support_cycleOf_le`

English:
theorem support_cycleOf_le
  given: [DecidableEq α] [Fintype α] (f : Perm α) (x : α)
  proof: by
  intro y hy
  rw [mem_support]; rw [cycleOf_apply] at hy
  split_ifs at hy
  · exact mem_support.mpr hy
  · exact absurd rfl hy

中文:
定理 support_cycleOf_le
  条件: [DecidableEq α] [有限类型 α] (f : 置换 α) (x : α)
  证明: by
  intro y hy
  rw [mem_support]; rw [cycleOf_apply] at hy
  split_ifs at hy
  · exact mem_support.mpr hy
  · exact absurd rfl hy

Depends on / 依赖: absurd, cycleOf_apply, mem_support, mem_support.mpr, split_ifs
-/
theorem support_cycleOf_le [DecidableEq α] [Fintype α] (f : Perm α) (x : α) :
    support (f.cycleOf x) <= support f := by
  intro y hy
  rw [mem_support]; rw [cycleOf_apply] at hy
  split_ifs at hy
  · exact mem_support.mpr hy
  · exact absurd rfl hy

/--
theorem `SameCycle.mem_support_iff` / 定理 `SameCycle.mem_support_iff`

English:
theorem SameCycle.mem_support_iff
  given: {f} [DecidableEq α] [Fintype α] (h : SameCycle f x y)
  proof: ⟨fun hx => support_cycleOf_le f x (mem_support_cycleOf_iff.mpr ⟨h, hx⟩), fun hy =>
    support_cycleOf_le f y (mem_support_cycleOf_iff.mpr ⟨h.symm, hy⟩)⟩

中文:
定理 SameCycle.mem_support_iff
  条件: {f} [DecidableEq α] [有限类型 α] (h : SameCycle f x y)
  证明: ⟨fun hx => support_cycleOf_le f x (mem_support_cycleOf_iff.mpr ⟨h, hx⟩), fun hy =>
    support_cycleOf_le f y (mem_support_cycleOf_iff.mpr ⟨h.symm, hy⟩)⟩

Depends on / 依赖: h.symm, mem_support_cycleOf_iff, mem_support_cycleOf_iff.mpr, support_cycleOf_le
-/
theorem SameCycle.mem_support_iff {f} [DecidableEq α] [Fintype α] (h : SameCycle f x y) :
    x in support f ↔ y in support f :=
  ⟨fun hx => support_cycleOf_le f x (mem_support_cycleOf_iff.mpr ⟨h, hx⟩), fun hy =>
    support_cycleOf_le f y (mem_support_cycleOf_iff.mpr ⟨h.symm, hy⟩)⟩

/--
theorem `pow_mod_card_support_cycleOf_self_apply` / 定理 `pow_mod_card_support_cycleOf_self_apply`

English:
theorem pow_mod_card_support_cycleOf_self_apply
  statement: [DecidableEq α] [Fintype α]
  proof: by
  by_cases hx : f x = x
  · rw [pow_apply_eq_self_of_apply_eq_self hx, pow_apply_eq_self_of_apply_eq_self hx]
  · rw [← cycleOf_pow_apply_self, ← cycleOf_pow_apply_self f, ← (isCycle_cycleOf f hx).orderOf,
      pow_mod_orderOf]

中文:
定理 pow_mod_card_support_cycleOf_self_apply
  结论: [DecidableEq α] [有限类型 α]
  证明: by
  by_cases hx : f x = x
  · rw [pow_apply_eq_self_of_apply_eq_self hx, pow_apply_eq_self_of_apply_eq_self hx]
  · rw [← cycleOf_pow_apply_self, ← cycleOf_pow_apply_self f, ← (isCycle_cycleOf f hx).orderOf,
      pow_mod_orderOf]

Depends on / 依赖: cycleOf_pow_apply_self, isCycle_cycleOf, orderOf, pow_apply_eq_self_of_apply_eq_self, pow_mod_orderOf
-/
theorem pow_mod_card_support_cycleOf_self_apply [DecidableEq α] [Fintype α]
    (f : Perm α) (n : Nat) (x : α) : (f ^ (n % #(f.cycleOf x).support)) x = (f ^ n) x := by
  by_cases hx : f x = x
  · rw [pow_apply_eq_self_of_apply_eq_self hx, pow_apply_eq_self_of_apply_eq_self hx]
  · rw [← cycleOf_pow_apply_self, ← cycleOf_pow_apply_self f, ← (isCycle_cycleOf f hx).orderOf,
      pow_mod_orderOf]

/--
theorem `SameCycle.exists_pow_eq` / 定理 `SameCycle.exists_pow_eq`

English:
theorem SameCycle.exists_pow_eq
  given: [DecidableEq α] [Fintype α] (f : Perm α) (h : SameCycle f x y)
  proof: by
  by_cases hx : x in f.support
  · obtain ⟨k, hk, hk'⟩ := h.exists_pow_eq_of_mem_support hx
    rcases k with - | k
    · refine ⟨#(f.cycleOf x).support, hk, self_le_add_right _ _, ?_⟩
      simp only [pow_zero, coe_one, id_eq] at hk'
      subst hk'
      rw [← (isCycle_cycleOf _ <| mem_support.1 hx).orderOf]; rw [← cycleOf_pow_apply_self]; rw [pow_orderOf_eq_one]; rw [one_apply]
    · exact ⟨k + 1, by simp, Nat.le_succ_of_le hk.le, hk'⟩
  · refine ⟨1, zero_lt_one, by simp, ?_⟩
    obtain ⟨k, rfl⟩ := h
    rw [notMem_support] at hx
    rw [pow_apply_eq_self_of_apply_eq_self hx]; rw [zpow_apply_eq_self_of_apply_eq_self hx]

中文:
定理 SameCycle.存在_pow_eq
  条件: [DecidableEq α] [有限类型 α] (f : 置换 α) (h : SameCycle f x y)
  证明: by
  by_cases hx : x in f.support
  · obtain ⟨k, hk, hk'⟩ := h.exists_pow_eq_of_mem_support hx
    rcases k with - | k
    · refine ⟨#(f.cycleOf x).support, hk, self_le_add_right _ _, ?_⟩
      simp only [pow_zero, coe_one, id_eq] at hk'
      subst hk'
      rw [← (isCycle_cycleOf _ <| mem_support.1 hx).orderOf]; rw [← cycleOf_pow_apply_self]; rw [pow_orderOf_eq_one]; rw [one_apply]
    · exact ⟨k + 1, by simp, Nat.le_succ_of_le hk.le, hk'⟩
  · refine ⟨1, zero_lt_one, by simp, ?_⟩
    obtain ⟨k, rfl⟩ := h
    rw [notMem_support] at hx
    rw [pow_apply_eq_self_of_apply_eq_self hx]; rw [zpow_apply_eq_self_of_apply_eq_self hx]

Depends on / 依赖: Nat.le_succ_of_le, coe_one, cycleOf, cycleOf_pow_apply_self, exists_pow_eq_of_mem_support, f.cycleOf, f.support, h.exists_pow_eq_of_mem_support, hk.le, id_eq, isCycle_cycleOf, le_succ_of_le, mem_support, notMem_support, one_apply, orderOf, pow_orderOf_eq_one, pow_zero, self_le_add_right, support
-/
theorem SameCycle.exists_pow_eq [DecidableEq α] [Fintype α] (f : Perm α) (h : SameCycle f x y) :
    exists i : Nat, 0 < i ∧ i <= #(f.cycleOf x).support + 1 ∧ (f ^ i) x = y := by
  by_cases hx : x in f.support
  · obtain ⟨k, hk, hk'⟩ := h.exists_pow_eq_of_mem_support hx
    rcases k with - | k
    · refine ⟨#(f.cycleOf x).support, hk, self_le_add_right _ _, ?_⟩
      simp only [pow_zero, coe_one, id_eq] at hk'
      subst hk'
      rw [← (isCycle_cycleOf _ <| mem_support.1 hx).orderOf]; rw [← cycleOf_pow_apply_self]; rw [pow_orderOf_eq_one]; rw [one_apply]
    · exact ⟨k + 1, by simp, Nat.le_succ_of_le hk.le, hk'⟩
  · refine ⟨1, zero_lt_one, by simp, ?_⟩
    obtain ⟨k, rfl⟩ := h
    rw [notMem_support] at hx
    rw [pow_apply_eq_self_of_apply_eq_self hx]; rw [zpow_apply_eq_self_of_apply_eq_self hx]

/--
theorem `zpow_eq_zpow_on_iff` / 定理 `zpow_eq_zpow_on_iff`

English:
theorem zpow_eq_zpow_on_iff
  statement: [DecidableEq α] [Fintype α]
  proof: by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  conv_lhs => rw [← Int.sub_add_cancel m n, Int.add_comm, zpow_add]
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [← Int.dvd_iff_emod_eq_zero]
  rw [← cycleOf_zpow_apply_self g x]; rw [cycle_zpow_mem_support_iff]
  · rw [← Int.dvd_iff_emod_eq_zero]
  · exact isCycle_cycleOf g hx
  · simp only [cycleOf_apply_self]; exact hx

中文:
定理 zpow_eq_zpow_on_iff
  结论: [DecidableEq α] [有限类型 α]
  证明: by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  conv_lhs => rw [← Int.sub_add_cancel m n, Int.add_comm, zpow_add]
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [← Int.dvd_iff_emod_eq_zero]
  rw [← cycleOf_zpow_apply_self g x]; rw [cycle_zpow_mem_support_iff]
  · rw [← Int.dvd_iff_emod_eq_zero]
  · exact isCycle_cycleOf g hx
  · simp only [cycleOf_apply_self]; exact hx

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Function, Function.comp_apply, Int.add_comm, Int.dvd_iff_emod_eq_zero, Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.sub_add_cancel, add_comm, apply_eq_iff_eq, coe_mul, comp_apply, conv_lhs, cycleOf_apply_self, cycleOf_zpow_apply_self, cycle_zpow_mem_support_iff, dvd_iff_emod_eq_zero, emod_eq_emod_iff_emod_sub_eq_zero, isCycle_cycleOf, sub_add_cancel
-/
theorem zpow_eq_zpow_on_iff [DecidableEq α] [Fintype α]
    (g : Perm α) {m n : Int} {x : α} (hx : g x != x) :
    (g ^ m) x = (g ^ n) x ↔ m % #(g.cycleOf x).support = n % #(g.cycleOf x).support := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  conv_lhs => rw [← Int.sub_add_cancel m n, Int.add_comm, zpow_add]
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [← Int.dvd_iff_emod_eq_zero]
  rw [← cycleOf_zpow_apply_self g x]; rw [cycle_zpow_mem_support_iff]
  · rw [← Int.dvd_iff_emod_eq_zero]
  · exact isCycle_cycleOf g hx
  · simp only [cycleOf_apply_self]; exact hx

end CycleOf


/-!
### `cycleFactors`
-/

section cycleFactors

open scoped List in
/--
Definition of `cycleFactorsAux` / `cycleFactorsAux` 的定义

English:
definition cycleFactorsAux
  signature: [DecidableEq α] [Fintype α]
  body: go l f h (fun _ => rfl)

中文:
定义 cycleFactorsAux
  签名: [DecidableEq α] [有限类型 α]
  定义体: go l f h (fun _ => rfl)
-/
def cycleFactorsAux [DecidableEq α] [Fintype α]
    (l : List α) (f : Perm α) (h : forall {x}, f x != x -> x in l) :
    { pl : List (Perm α) // pl.prod = f ∧ (forall g in pl, IsCycle g) ∧ pl.Pairwise Disjoint } :=
  go l f h (fun _ => rfl)
where
  /-- The auxiliary of `cycleFactorsAux`. This functions separates cycles from `f` instead of `g`
  to prevent the process of a cycle gets complex. -/
  go (l : List α) (g : Perm α) (hg : forall {x}, g x != x -> x in l)
    (hfg : forall {x}, g x != x -> cycleOf f x = cycleOf g x) :
    { pl : List (Perm α) // pl.prod = g ∧ (forall g' in pl, IsCycle g') ∧ pl.Pairwise Disjoint } :=
  match l with
  | [] => ⟨[], by
      { simp only [imp_false, List.Pairwise.nil, List.not_mem_nil, forall_const, and_true,
          forall_prop_of_false, Classical.not_not, not_false_iff, List.prod_nil] at *
        ext
        simp [*]}⟩
  | x :: l =>
    if hx : g x = x then go l g (by
        intro y hy; exact List.mem_of_ne_of_mem (fun h => hy (by rwa [h])) (hg hy)) hfg
    else
      let ⟨m, hm⟩ :=
        go l ((cycleOf f x)⁻¹ * g) (by
            rw [hfg hx]
            intro y hy
            exact List.mem_of_ne_of_mem
              (fun h : y = x => by
                rw [h]; rw [mul_apply]; rw [Ne]; rw [inv_eq_iff_eq]; rw [cycleOf_apply_self] at hy
                exact hy rfl)
              (hg fun h : g y = y => by
                rw [mul_apply]; rw [h]; rw [Ne]; rw [inv_eq_iff_eq]; rw [cycleOf_apply] at hy
                split_ifs at hy <;> tauto))
          (by
            rw [hfg hx]
            intro y hy
            simp [symm_apply_eq, cycleOf_apply, eq_comm (a := g y)] at hy
            rw [hfg (Ne.symm hy.right)]; rw [← mul_inv_eq_one (a := g.cycleOf y)]; rw [cycleOf_inv]
            simp_rw [mul_inv_rev]
            rw [inv_inv]; rw [cycleOf_mul_of_apply_right_eq_self]; rw [← cycleOf_inv]; rw [mul_inv_eq_one]
            · rw [Commute.inv_left_iff, commute_iff_eq]
              ext z; by_cases hz : SameCycle g x z
              · simp [cycleOf_apply, hz]
              · simp [cycleOf_apply_of_not_sameCycle, hz]
            · exact cycleOf_apply_of_not_sameCycle hy.left)
      ⟨cycleOf f x :: m, by
        obtain ⟨hm₁, hm₂, hm₃⟩ := hm
        rw [hfg hx] at hm₁ ⊢
        rw [List.pairwise_cons]
        refine ⟨?_, fun g' hg' => ?_, fun g' hg' y => ?_, hm₃⟩
        · simp [List.prod_cons, hm₁]
        · exact ((List.mem_cons).1 hg').elim (fun hg' => hg'.symm ▸ isCycle_cycleOf _ hx) (hm₂ g')
        by_contra! ⟨hgy, hg'y⟩
        have hxy : SameCycle g x y := not_imp_comm.1 cycleOf_apply_of_not_sameCycle hgy
        have hg'm : g' :: m.erase g' ~ m := List.cons_perm_iff_perm_erase.2 ⟨hg', .refl _⟩
        have : forall h in m.erase g', Disjoint g' h :=
          (List.pairwise_cons.1 ((hg'm.pairwise_iff Disjoint.symm).2 hm₃)).1
refine hg'y (disjoint_prod_right _ this y).resolve_right ?_
        have hsc : SameCycle g⁻¹ x (g y) := by rwa [sameCycle_inv, sameCycle_apply_right]
        rw [disjoint_prod_perm hm₃ hg'm.symm]; rw [List.prod_cons]; rw [← eq_inv_mul_iff_mul_eq] at hm₁
        simpa [hm₁, cycleOf_inv, hsc.cycleOf_apply, eq_symm_apply, eq_comm] using hg'y⟩

/--
theorem `mem_list_cycles_iff` / 定理 `mem_list_cycles_iff`

English:
theorem mem_list_cycles_iff
  statement: {α : Type*} [Finite α] {l : List (Perm α)}
  proof: by
  suffices σ.IsCycle -> (σ in l ↔ forall a, σ a != a -> σ a = l.prod a) by
    exact ⟨fun hσ => ⟨h1 σ hσ, (this (h1 σ hσ)).mp hσ⟩, fun hσ => (this hσ.1).mpr hσ.2⟩
  intro h3
  classical
    cases nonempty_fintype α
    constructor
    · intro h a ha
      exact eq_on_support_mem_disjoint h h2 _ (mem_support.mpr ha)
    · intro h
      have hσl : σ.support subseteq l.prod.support := by
        intro x hx
        rw [mem_support] at hx
        rwa [mem_support, ← h _ hx]
      obtain ⟨a, ha, -⟩ := id h3
      rw [← mem_support] at ha
      obtain ⟨τ, hτ, hτa⟩ := exists_mem_support_of_mem_support_prod (hσl ha)
      have hτl : forall x in τ.support, τ x = l.prod x := eq_on_support_mem_disjoint hτ h2
      have key : forall x in σ.support inter τ.support, σ x = τ x := by
        intro x hx
        rw [h x (mem_support.mp (mem_of_mem_inter_left hx))]; rw [hτl x (mem_of_mem_inter_right hx)]
      convert! hτ
      refine h3.eq_on_support_inter_nonempty_congr (h1 _ hτ) key ?_ ha
      exact key a (mem_inter_of_mem ha hτa)

中文:
定理 mem_list_cycles_iff
  结论: {α : 类型} [有限 α] {l : 列表 (置换 α)}
  证明: by
  suffices σ.IsCycle -> (σ in l ↔ forall a, σ a != a -> σ a = l.prod a) by
    exact ⟨fun hσ => ⟨h1 σ hσ, (this (h1 σ hσ)).mp hσ⟩, fun hσ => (this hσ.1).mpr hσ.2⟩
  intro h3
  classical
    cases nonempty_fintype α
    constructor
    · intro h a ha
      exact eq_on_support_mem_disjoint h h2 _ (mem_support.mpr ha)
    · intro h
      have hσl : σ.support subseteq l.prod.support := by
        intro x hx
        rw [mem_support] at hx
        rwa [mem_support, ← h _ hx]
      obtain ⟨a, ha, -⟩ := id h3
      rw [← mem_support] at ha
      obtain ⟨τ, hτ, hτa⟩ := exists_mem_support_of_mem_support_prod (hσl ha)
      have hτl : forall x in τ.support, τ x = l.prod x := eq_on_support_mem_disjoint hτ h2
      have key : forall x in σ.support inter τ.support, σ x = τ x := by
        intro x hx
        rw [h x (mem_support.mp (mem_of_mem_inter_left hx))]; rw [hτl x (mem_of_mem_inter_right hx)]
      convert! hτ
      refine h3.eq_on_support_inter_nonempty_congr (h1 _ hτ) key ?_ ha
      exact key a (mem_inter_of_mem ha hτa)

Depends on / 依赖: IsCycle, classical, eq_on_support_mem_disjoint, exists_mem, l.prod, l.prod.support, mem_support, mem_support.mpr, nonempty_fintype, subseteq, support
-/
theorem mem_list_cycles_iff {α : Type*} [Finite α] {l : List (Perm α)}
    (h1 : forall σ : Perm α, σ in l -> σ.IsCycle) (h2 : l.Pairwise Disjoint) {σ : Perm α} :
    σ in l ↔ σ.IsCycle ∧ forall a, σ a != a -> σ a = l.prod a := by
  suffices σ.IsCycle -> (σ in l ↔ forall a, σ a != a -> σ a = l.prod a) by
    exact ⟨fun hσ => ⟨h1 σ hσ, (this (h1 σ hσ)).mp hσ⟩, fun hσ => (this hσ.1).mpr hσ.2⟩
  intro h3
  classical
    cases nonempty_fintype α
    constructor
    · intro h a ha
      exact eq_on_support_mem_disjoint h h2 _ (mem_support.mpr ha)
    · intro h
      have hσl : σ.support subseteq l.prod.support := by
        intro x hx
        rw [mem_support] at hx
        rwa [mem_support, ← h _ hx]
      obtain ⟨a, ha, -⟩ := id h3
      rw [← mem_support] at ha
      obtain ⟨τ, hτ, hτa⟩ := exists_mem_support_of_mem_support_prod (hσl ha)
      have hτl : forall x in τ.support, τ x = l.prod x := eq_on_support_mem_disjoint hτ h2
      have key : forall x in σ.support inter τ.support, σ x = τ x := by
        intro x hx
        rw [h x (mem_support.mp (mem_of_mem_inter_left hx))]; rw [hτl x (mem_of_mem_inter_right hx)]
      convert! hτ
      refine h3.eq_on_support_inter_nonempty_congr (h1 _ hτ) key ?_ ha
      exact key a (mem_inter_of_mem ha hτa)

open scoped List in
/--
theorem `list_cycles_perm_list_cycles` / 定理 `list_cycles_perm_list_cycles`

English:
theorem list_cycles_perm_list_cycles
  statement: {α : Type*} [Finite α] {l₁ l₂ : List (Perm α)}
  proof: by
  refine
    (List.perm_ext_iff_of_nodup (nodup_of_pairwise_disjoint_cycles h₁l₁ h₂l₁)
          (nodup_of_pairwise_disjoint_cycles h₁l₂ h₂l₂)).mpr
      fun σ => ?_
  by_cases hσ : σ.IsCycle
  · obtain _ := not_forall.mp (mt ext hσ.ne_one)
    rw [mem_list_cycles_iff h₁l₁ h₂l₁]; rw [mem_list_cycles_iff h₁l₂ h₂l₂]; rw [h₀]
  · exact iff_of_false (mt (h₁l₁ σ) hσ) (mt (h₁l₂ σ) hσ)

中文:
定理 list_cycles_perm_list_cycles
  结论: {α : 类型} [有限 α] {l₁ l₂ : 列表 (置换 α)}
  证明: by
  refine
    (List.perm_ext_iff_of_nodup (nodup_of_pairwise_disjoint_cycles h₁l₁ h₂l₁)
          (nodup_of_pairwise_disjoint_cycles h₁l₂ h₂l₂)).mpr
      fun σ => ?_
  by_cases hσ : σ.IsCycle
  · obtain _ := not_forall.mp (mt ext hσ.ne_one)
    rw [mem_list_cycles_iff h₁l₁ h₂l₁]; rw [mem_list_cycles_iff h₁l₂ h₂l₂]; rw [h₀]
  · exact iff_of_false (mt (h₁l₁ σ) hσ) (mt (h₁l₂ σ) hσ)

Depends on / 依赖: CompatibleSMul, CompatibleSMul.isScalarTower, IsCycle, IsScalarTower, List.perm_ext_iff_of_nodup, iff_of_false, isScalarTower, mem_list_cycles_iff, ne_one, nodup_of_pairwise_disjoint_cycles, not_forall, not_forall.mp, perm_ext_iff_of_nodup
-/
theorem list_cycles_perm_list_cycles {α : Type*} [Finite α] {l₁ l₂ : List (Perm α)}
    (h₀ : l₁.prod = l₂.prod) (h₁l₁ : forall σ : Perm α, σ in l₁ -> σ.IsCycle)
    (h₁l₂ : forall σ : Perm α, σ in l₂ -> σ.IsCycle) (h₂l₁ : l₁.Pairwise Disjoint)
    (h₂l₂ : l₂.Pairwise Disjoint) : l₁ ~ l₂ := by
  refine
    (List.perm_ext_iff_of_nodup (nodup_of_pairwise_disjoint_cycles h₁l₁ h₂l₁)
          (nodup_of_pairwise_disjoint_cycles h₁l₂ h₂l₂)).mpr
      fun σ => ?_
  by_cases hσ : σ.IsCycle
  · obtain _ := not_forall.mp (mt ext hσ.ne_one)
    rw [mem_list_cycles_iff h₁l₁ h₂l₁]; rw [mem_list_cycles_iff h₁l₂ h₂l₂]; rw [h₀]
  · exact iff_of_false (mt (h₁l₁ σ) hσ) (mt (h₁l₂ σ) hσ)

/--
Definition of `cycleFactors` / `cycleFactors` 的定义

English:
definition cycleFactors
  signature: [Fintype α] [LinearOrder α] (f : Perm α)
  body: cycleFactorsAux (sort (α := α) univ) f (fun {_ _} => (mem_sort _).2 (mem_univ _))

中文:
定义 cycleFactors
  签名: [有限类型 α] [线性序 α] (f : 置换 α)
  定义体: cycleFactorsAux (sort (α := α) univ) f (fun {_ _} => (mem_sort _).2 (mem_univ _))

Depends on / 依赖: cycleFactorsAux, mem_sort, mem_univ
-/
def cycleFactors [Fintype α] [LinearOrder α] (f : Perm α) :
    { l : List (Perm α) // l.prod = f ∧ (forall g in l, IsCycle g) ∧ l.Pairwise Disjoint } :=
  cycleFactorsAux (sort (α := α) univ) f (fun {_ _} => (mem_sort _).2 (mem_univ _))

/--
Definition of `truncCycleFactors` / `truncCycleFactors` 的定义

English:
definition truncCycleFactors
  signature: [DecidableEq α] [Fintype α] (f : Perm α)
  body: Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (cycleFactorsAux l f (h _)))
    (show forall x, f x != x -> x in (@univ α _).1 from fun _ _ => mem_univ _)

中文:
定义 truncCycleFactors
  签名: [DecidableEq α] [有限类型 α] (f : 置换 α)
  定义体: Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (cycleFactorsAux l f (h _)))
    (show forall x, f x != x -> x in (@univ α _).1 from fun _ _ => mem_univ _)

Depends on / 依赖: Quotient, Quotient.recOnSubsingleton, Trunc.mk, cycleFactorsAux, mem_univ, recOnSubsingleton
-/
def truncCycleFactors [DecidableEq α] [Fintype α] (f : Perm α) :
    Trunc { l : List (Perm α) // l.prod = f ∧ (forall g in l, IsCycle g) ∧ l.Pairwise Disjoint } :=
  Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (cycleFactorsAux l f (h _)))
    (show forall x, f x != x -> x in (@univ α _).1 from fun _ _ => mem_univ _)

section CycleFactorsFinset

variable [DecidableEq α] [Fintype α] (f : Perm α)

/--
Definition of `cycleFactorsFinset` / `cycleFactorsFinset` 的定义

English:
definition cycleFactorsFinset
  signature: : Finset (Perm α)
  body: (truncCycleFactors f).lift
    (fun l : { l : List (Perm α) // l.prod = f ∧ (forall g in l, IsCycle g) ∧ l.Pairwise Disjoint } =>
      ⟨↑l.val, nodup_of_pairwise_disjoint (fun h1 => not_isCycle_one <| l.2.2.1 _ h1) l.2.2.2⟩)
    fun ⟨_, hl⟩ ⟨_, hl'⟩ =>
Finset.eq_of_veq Multiset.coe_eq_coe.mpr
      list_cycles_perm_list_cycles (hl'.left.symm ▸ hl.left) hl.right.left hl'.right.left
        hl.right.right hl'.right.right

中文:
定义 cycleFactorsFinset
  签名: : 有限集 (置换 α)
  定义体: (truncCycleFactors f).lift
    (fun l : { l : List (Perm α) // l.prod = f ∧ (forall g in l, IsCycle g) ∧ l.Pairwise Disjoint } =>
      ⟨↑l.val, nodup_of_pairwise_disjoint (fun h1 => not_isCycle_one <| l.2.2.1 _ h1) l.2.2.2⟩)
    fun ⟨_, hl⟩ ⟨_, hl'⟩ =>
Finset.eq_of_veq Multiset.coe_eq_coe.mpr
      list_cycles_perm_list_cycles (hl'.left.symm ▸ hl.left) hl.right.left hl'.right.left
        hl.right.right hl'.right.right

Depends on / 依赖: Disjoint, Finset, Finset.eq_of_veq, IsCycle, Multiset, Multiset.coe_eq_coe.mpr, Pairwise, coe_eq_coe, eq_of_veq, hl.left, hl.right.left, hl.right.right, l.Pairwise, l.prod, l.val, left.symm, list_cycles_perm_list_cycles, nodup_of_pairwise_disjoint, not_isCycle_one, right.left
-/
def cycleFactorsFinset : Finset (Perm α) :=
  (truncCycleFactors f).lift
    (fun l : { l : List (Perm α) // l.prod = f ∧ (forall g in l, IsCycle g) ∧ l.Pairwise Disjoint } =>
      ⟨↑l.val, nodup_of_pairwise_disjoint (fun h1 => not_isCycle_one <| l.2.2.1 _ h1) l.2.2.2⟩)
    fun ⟨_, hl⟩ ⟨_, hl'⟩ =>
Finset.eq_of_veq Multiset.coe_eq_coe.mpr
      list_cycles_perm_list_cycles (hl'.left.symm ▸ hl.left) hl.right.left hl'.right.left
        hl.right.right hl'.right.right

set_option backward.isDefEq.respectTransparency false in
open scoped List in
/--
theorem `cycleFactorsFinset_eq_list_toFinset` / 定理 `cycleFactorsFinset_eq_list_toFinset`

English:
theorem cycleFactorsFinset_eq_list_toFinset
  given: {σ : Perm α} {l : List (Perm α)} (hn : l.Nodup)
  proof: by
  obtain ⟨⟨l', hp', hc', hd'⟩, hl⟩ := Trunc.exists_rep σ.truncCycleFactors
  have ht : cycleFactorsFinset σ = l'.toFinset := by
    rw [cycleFactorsFinset]; rw [← hl]; rw [Trunc.lift_mk]; rw [Multiset.toFinset_eq]; rw [List.toFinset_coe]
  rw [ht]
  constructor
  · intro h
    have hn' : l'.Nodup := nodup_of_pairwise_disjoint_cycles hc' hd'
    have hperm : l ~ l' := List.perm_of_nodup_nodup_toFinset_eq hn hn' h.symm
    refine ⟨?_, ?_, ?_⟩
    · exact fun _ h => hc' _ (hperm.subset h)
    · rwa [hperm.pairwise_iff symm]
    · rw [← hp', hperm.symm.prod_eq']
      exact hd'.imp Disjoint.commute
  · rintro ⟨hc, hd, hp⟩
    refine List.toFinset_eq_of_perm _ _ ?_
    refine list_cycles_perm_list_cycles ?_ hc' hc hd' hd
    rw [hp]; rw [hp']

中文:
定理 cycleFactorsFinset_eq_list_toFinset
  条件: {σ : 置换 α} {l : 列表 (置换 α)} (hn : l.Nodup)
  证明: by
  obtain ⟨⟨l', hp', hc', hd'⟩, hl⟩ := Trunc.exists_rep σ.truncCycleFactors
  have ht : cycleFactorsFinset σ = l'.toFinset := by
    rw [cycleFactorsFinset]; rw [← hl]; rw [Trunc.lift_mk]; rw [Multiset.toFinset_eq]; rw [List.toFinset_coe]
  rw [ht]
  constructor
  · intro h
    have hn' : l'.Nodup := nodup_of_pairwise_disjoint_cycles hc' hd'
    have hperm : l ~ l' := List.perm_of_nodup_nodup_toFinset_eq hn hn' h.symm
    refine ⟨?_, ?_, ?_⟩
    · exact fun _ h => hc' _ (hperm.subset h)
    · rwa [hperm.pairwise_iff symm]
    · rw [← hp', hperm.symm.prod_eq']
      exact hd'.imp Disjoint.commute
  · rintro ⟨hc, hd, hp⟩
    refine List.toFinset_eq_of_perm _ _ ?_
    refine list_cycles_perm_list_cycles ?_ hc' hc hd' hd
    rw [hp]; rw [hp']

Depends on / 依赖: List.perm_of_nodup_nodup_toFinset_eq, List.toFinset_coe, Multiset, Multiset.toFinset_eq, Trunc.exists_rep, Trunc.lift_mk, cycleFactorsFinset, exists_rep, h.symm, hperm.pairwise_iff, hperm.subset, lift_mk, nodup_of_pairwise_disjoint_cycles, pairwise_iff, perm_of_nodup_nodup_toFinset_eq, subset, toFinset, toFinset_coe, toFinset_eq, truncCycleFactors
-/
theorem cycleFactorsFinset_eq_list_toFinset {σ : Perm α} {l : List (Perm α)} (hn : l.Nodup) :
    σ.cycleFactorsFinset = l.toFinset ↔
      (forall f : Perm α, f in l -> f.IsCycle) ∧ l.Pairwise Disjoint ∧ l.prod = σ := by
  obtain ⟨⟨l', hp', hc', hd'⟩, hl⟩ := Trunc.exists_rep σ.truncCycleFactors
  have ht : cycleFactorsFinset σ = l'.toFinset := by
    rw [cycleFactorsFinset]; rw [← hl]; rw [Trunc.lift_mk]; rw [Multiset.toFinset_eq]; rw [List.toFinset_coe]
  rw [ht]
  constructor
  · intro h
    have hn' : l'.Nodup := nodup_of_pairwise_disjoint_cycles hc' hd'
    have hperm : l ~ l' := List.perm_of_nodup_nodup_toFinset_eq hn hn' h.symm
    refine ⟨?_, ?_, ?_⟩
    · exact fun _ h => hc' _ (hperm.subset h)
    · rwa [hperm.pairwise_iff symm]
    · rw [← hp', hperm.symm.prod_eq']
      exact hd'.imp Disjoint.commute
  · rintro ⟨hc, hd, hp⟩
    refine List.toFinset_eq_of_perm _ _ ?_
    refine list_cycles_perm_list_cycles ?_ hc' hc hd' hd
    rw [hp]; rw [hp']

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cycleFactorsFinset_eq_finset` / 定理 `cycleFactorsFinset_eq_finset`

English:
theorem cycleFactorsFinset_eq_finset
  given: {σ : Perm α} {s : Finset (Perm α)}
  proof: by
  obtain ⟨l, hl, rfl⟩ := s.exists_list_nodup_eq
  simp [cycleFactorsFinset_eq_list_toFinset, hl]

中文:
定理 cycleFactorsFinset_eq_finset
  条件: {σ : 置换 α} {s : 有限集 (置换 α)}
  证明: by
  obtain ⟨l, hl, rfl⟩ := s.exists_list_nodup_eq
  simp [cycleFactorsFinset_eq_list_toFinset, hl]

Depends on / 依赖: cycleFactorsFinset_eq_list_toFinset, exists_list_nodup_eq, s.exists_list_nodup_eq
-/
theorem cycleFactorsFinset_eq_finset {σ : Perm α} {s : Finset (Perm α)} :
    σ.cycleFactorsFinset = s ↔
      (forall f : Perm α, f in s -> f.IsCycle) ∧
        exists h : (s : Set (Perm α)).Pairwise Disjoint,
          s.noncommProd id (h.mono' fun _ _ => Disjoint.commute) = σ := by
  obtain ⟨l, hl, rfl⟩ := s.exists_list_nodup_eq
  simp [cycleFactorsFinset_eq_list_toFinset, hl]

/--
theorem `cycleFactorsFinset_pairwise_disjoint` / 定理 `cycleFactorsFinset_pairwise_disjoint`

English:
theorem cycleFactorsFinset_pairwise_disjoint
  proof: (cycleFactorsFinset_eq_finset.mp rfl).2.choose

中文:
定理 cycleFactorsFinset_pairwise_disjoint
  证明: (cycleFactorsFinset_eq_finset.mp rfl).2.choose

Depends on / 依赖: cycleFactorsFinset_eq_finset, cycleFactorsFinset_eq_finset.mp
-/
theorem cycleFactorsFinset_pairwise_disjoint :
    (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint :=
  (cycleFactorsFinset_eq_finset.mp rfl).2.choose

/--
theorem `cycleFactorsFinset_mem_commute` / 定理 `cycleFactorsFinset_mem_commute`

English:
theorem cycleFactorsFinset_mem_commute
  statement: (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute
  proof: (cycleFactorsFinset_pairwise_disjoint _).mono' fun _ _ => Disjoint.commute

中文:
定理 cycleFactorsFinset_mem_commute
  结论: (cycleFactorsFinset f : 集合 (置换 α)).两两 Commute
  证明: (cycleFactorsFinset_pairwise_disjoint _).mono' fun _ _ => Disjoint.commute

Depends on / 依赖: Disjoint, Disjoint.commute, commute, cycleFactorsFinset_pairwise_disjoint
-/
theorem cycleFactorsFinset_mem_commute : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute :=
  (cycleFactorsFinset_pairwise_disjoint _).mono' fun _ _ => Disjoint.commute

/--
theorem `cycleFactorsFinset_mem_commute'` / 定理 `cycleFactorsFinset_mem_commute'`

English:
theorem cycleFactorsFinset_mem_commute'
  statement: {g1 g2 : Perm α}
  proof: by
  rcases eq_or_ne g1 g2 with rfl | h
  · apply Commute.refl
  · exact Equiv.Perm.cycleFactorsFinset_mem_commute f h1 h2 h

中文:
定理 cycleFactorsFinset_mem_commute'
  结论: {g1 g2 : 置换 α}
  证明: by
  rcases eq_or_ne g1 g2 with rfl | h
  · apply Commute.refl
  · exact Equiv.Perm.cycleFactorsFinset_mem_commute f h1 h2 h

Depends on / 依赖: Commute, Commute.refl, Equiv.Perm.cycleFactorsFinset_mem_commute, cycleFactorsFinset_mem_commute, eq_or_ne
-/
theorem cycleFactorsFinset_mem_commute' {g1 g2 : Perm α}
    (h1 : g1 in f.cycleFactorsFinset) (h2 : g2 in f.cycleFactorsFinset) :
    Commute g1 g2 := by
  rcases eq_or_ne g1 g2 with rfl | h
  · apply Commute.refl
  · exact Equiv.Perm.cycleFactorsFinset_mem_commute f h1 h2 h

/--
theorem `cycleFactorsFinset_noncommProd` / 定理 `cycleFactorsFinset_noncommProd`

English:
theorem cycleFactorsFinset_noncommProd
  proof: (cycleFactorsFinset_eq_finset.mp rfl).2.choose_spec

中文:
定理 cycleFactorsFinset_noncommProd
  证明: (cycleFactorsFinset_eq_finset.mp rfl).2.choose_spec

Depends on / 依赖: choose_spec, cycleFactorsFinset, cycleFactorsFinset_eq_finset, cycleFactorsFinset_eq_finset.mp, cycleFactorsFinset_mem_commute, f.cycleFactorsFinset.noncommProd, noncommProd
-/
theorem cycleFactorsFinset_noncommProd
    (comm : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute :=
      cycleFactorsFinset_mem_commute f) :
    f.cycleFactorsFinset.noncommProd id comm = f :=
  (cycleFactorsFinset_eq_finset.mp rfl).2.choose_spec

/--
theorem `mem_cycleFactorsFinset_iff` / 定理 `mem_cycleFactorsFinset_iff`

English:
theorem mem_cycleFactorsFinset_iff
  given: {f p : Perm α}
  proof: by
  obtain ⟨l, hl, hl'⟩ := f.cycleFactorsFinset.exists_list_nodup_eq
  rw [← hl']
  rw [eq_comm]; rw [cycleFactorsFinset_eq_list_toFinset hl] at hl'
  simpa [List.mem_toFinset, Ne, ← hl'.right.right] using
    mem_list_cycles_iff hl'.left hl'.right.left

中文:
定理 mem_cycleFactorsFinset_iff
  条件: {f p : 置换 α}
  证明: by
  obtain ⟨l, hl, hl'⟩ := f.cycleFactorsFinset.exists_list_nodup_eq
  rw [← hl']
  rw [eq_comm]; rw [cycleFactorsFinset_eq_list_toFinset hl] at hl'
  simpa [List.mem_toFinset, Ne, ← hl'.right.right] using
    mem_list_cycles_iff hl'.left hl'.right.left

Depends on / 依赖: List.mem_toFinset, cycleFactorsFinset, cycleFactorsFinset_eq_list_toFinset, eq_comm, exists_list_nodup_eq, f.cycleFactorsFinset.exists_list_nodup_eq, mem_list_cycles_iff, mem_toFinset, right.left, right.right
-/
theorem mem_cycleFactorsFinset_iff {f p : Perm α} :
    p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = f a := by
  obtain ⟨l, hl, hl'⟩ := f.cycleFactorsFinset.exists_list_nodup_eq
  rw [← hl']
  rw [eq_comm]; rw [cycleFactorsFinset_eq_list_toFinset hl] at hl'
  simpa [List.mem_toFinset, Ne, ← hl'.right.right] using
    mem_list_cycles_iff hl'.left hl'.right.left

/--
theorem `cycleOf_mem_cycleFactorsFinset_iff` / 定理 `cycleOf_mem_cycleFactorsFinset_iff`

English:
theorem cycleOf_mem_cycleFactorsFinset_iff
  given: {f : Perm α} {x : α}
  proof: by
  rw [mem_cycleFactorsFinset_iff]
  constructor
  · rintro ⟨hc, _⟩
    contrapose hc
    rw [notMem_support]; rw [← cycleOf_eq_one_iff] at hc
    simp [hc]
  · intro hx
    refine ⟨isCycle_cycleOf _ (mem_support.mp hx), ?_⟩
    intro y hy
    rw [mem_support] at hy
    rw [cycleOf_apply]
    split_ifs with H
    · rfl
    · rw [cycleOf_apply_of_not_sameCycle H] at hy
      contradiction

中文:
定理 cycleOf_mem_cycleFactorsFinset_iff
  条件: {f : 置换 α} {x : α}
  证明: by
  rw [mem_cycleFactorsFinset_iff]
  constructor
  · rintro ⟨hc, _⟩
    contrapose hc
    rw [notMem_support]; rw [← cycleOf_eq_one_iff] at hc
    simp [hc]
  · intro hx
    refine ⟨isCycle_cycleOf _ (mem_support.mp hx), ?_⟩
    intro y hy
    rw [mem_support] at hy
    rw [cycleOf_apply]
    split_ifs with H
    · rfl
    · rw [cycleOf_apply_of_not_sameCycle H] at hy
      contradiction

Depends on / 依赖: contrapose, cycleOf_apply, cycleOf_apply_of_not_sameCycle, cycleOf_eq_one_iff, isCycle_cycleOf, mem_cycleFactorsFinset_iff, mem_support, mem_support.mp, notMem_support, split_ifs
-/
theorem cycleOf_mem_cycleFactorsFinset_iff {f : Perm α} {x : α} :
    cycleOf f x in cycleFactorsFinset f ↔ x in f.support := by
  rw [mem_cycleFactorsFinset_iff]
  constructor
  · rintro ⟨hc, _⟩
    contrapose hc
    rw [notMem_support]; rw [← cycleOf_eq_one_iff] at hc
    simp [hc]
  · intro hx
    refine ⟨isCycle_cycleOf _ (mem_support.mp hx), ?_⟩
    intro y hy
    rw [mem_support] at hy
    rw [cycleOf_apply]
    split_ifs with H
    · rfl
    · rw [cycleOf_apply_of_not_sameCycle H] at hy
      contradiction

/--
lemma `cycleOf_ne_one_iff_mem_cycleFactorsFinset` / 引理 `cycleOf_ne_one_iff_mem_cycleFactorsFinset`

English:
lemma cycleOf_ne_one_iff_mem_cycleFactorsFinset
  given: {g : Equiv.Perm α} {x : α}
  proof: by
  rw [cycleOf_mem_cycleFactorsFinset_iff]; rw [mem_support]; rw [ne_eq]; rw [cycleOf_eq_one_iff]

中文:
引理 cycleOf_ne_one_iff_mem_cycleFactorsFinset
  条件: {g : 等价.置换 α} {x : α}
  证明: by
  rw [cycleOf_mem_cycleFactorsFinset_iff]; rw [mem_support]; rw [ne_eq]; rw [cycleOf_eq_one_iff]

Depends on / 依赖: cycleOf_eq_one_iff, cycleOf_mem_cycleFactorsFinset_iff, mem_support, ne_eq
-/
lemma cycleOf_ne_one_iff_mem_cycleFactorsFinset {g : Equiv.Perm α} {x : α} :
    g.cycleOf x != 1 ↔ g.cycleOf x in g.cycleFactorsFinset := by
  rw [cycleOf_mem_cycleFactorsFinset_iff]; rw [mem_support]; rw [ne_eq]; rw [cycleOf_eq_one_iff]

/--
theorem `mem_cycleFactorsFinset_support_le` / 定理 `mem_cycleFactorsFinset_support_le`

English:
theorem mem_cycleFactorsFinset_support_le
  given: {p f : Perm α} (h : p in cycleFactorsFinset f)
  proof: by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x hx
  rwa [mem_support, ← h.right x hx, ← mem_support]

中文:
定理 mem_cycleFactorsFinset_support_le
  条件: {p f : 置换 α} (h : p in cycleFactorsFinset f)
  证明: by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x hx
  rwa [mem_support, ← h.right x hx, ← mem_support]

Depends on / 依赖: h.right, mem_cycleFactorsFinset_iff, mem_support
-/
theorem mem_cycleFactorsFinset_support_le {p f : Perm α} (h : p in cycleFactorsFinset f) :
    p.support <= f.support := by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x hx
  rwa [mem_support, ← h.right x hx, ← mem_support]

/--
lemma `support_zpowers_of_mem_cycleFactorsFinset_le` / 引理 `support_zpowers_of_mem_cycleFactorsFinset_le`

English:
lemma support_zpowers_of_mem_cycleFactorsFinset_le
  statement: {g : Perm α}
  proof: by
  obtain ⟨m, hm⟩ := v.prop
  simp only [← hm]
  exact le_trans (support_zpow_le _ _) (mem_cycleFactorsFinset_support_le c.prop)

中文:
引理 support_zpowers_of_mem_cycleFactorsFinset_le
  结论: {g : 置换 α}
  证明: by
  obtain ⟨m, hm⟩ := v.prop
  simp only [← hm]
  exact le_trans (support_zpow_le _ _) (mem_cycleFactorsFinset_support_le c.prop)

Depends on / 依赖: c.prop, le_trans, mem_cycleFactorsFinset_support_le, support_zpow_le, v.prop
-/
lemma support_zpowers_of_mem_cycleFactorsFinset_le {g : Perm α}
    {c : g.cycleFactorsFinset} (v : Subgroup.zpowers (c : Perm α)) :
    (v : Perm α).support <= g.support := by
  obtain ⟨m, hm⟩ := v.prop
  simp only [← hm]
  exact le_trans (support_zpow_le _ _) (mem_cycleFactorsFinset_support_le c.prop)

/--
theorem `pairwise_disjoint_of_mem_zpowers` / 定理 `pairwise_disjoint_of_mem_zpowers`

English:
theorem pairwise_disjoint_of_mem_zpowers
  proof: fun c d hcd => fun x y hx hy => by
  obtain ⟨m, hm⟩ := hx; obtain ⟨n, hn⟩ := hy
  simp only [← hm, ← hn]
  apply Disjoint.zpow_disjoint_zpow
  exact f.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr hcd)

中文:
定理 pairwise_disjoint_of_mem_zpowers
  证明: fun c d hcd => fun x y hx hy => by
  obtain ⟨m, hm⟩ := hx; obtain ⟨n, hn⟩ := hy
  simp only [← hm, ← hn]
  apply Disjoint.zpow_disjoint_zpow
  exact f.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr hcd)

Depends on / 依赖: Disjoint, Disjoint.zpow_disjoint_zpow, Subtype, Subtype.coe_ne_coe.mpr, c.prop, coe_ne_coe, cycleFactorsFinset_pairwise_disjoint, d.prop, f.cycleFactorsFinset_pairwise_disjoint, zpow_disjoint_zpow
-/
theorem pairwise_disjoint_of_mem_zpowers :
    Pairwise fun (i j : f.cycleFactorsFinset) =>
      forall (x y : Perm α), x in Subgroup.zpowers ↑i -> y in Subgroup.zpowers ↑j -> Disjoint x y :=
  fun c d hcd => fun x y hx hy => by
  obtain ⟨m, hm⟩ := hx; obtain ⟨n, hn⟩ := hy
  simp only [← hm, ← hn]
  apply Disjoint.zpow_disjoint_zpow
  exact f.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr hcd)

/--
lemma `pairwise_commute_of_mem_zpowers` / 引理 `pairwise_commute_of_mem_zpowers`

English:
lemma pairwise_commute_of_mem_zpowers
  proof: f.pairwise_disjoint_of_mem_zpowers.mono
    (fun _ _ => forall₂_imp (fun _ _ h hx hy => (h hx hy).commute))

中文:
引理 pairwise_commute_of_mem_zpowers
  证明: f.pairwise_disjoint_of_mem_zpowers.mono
    (fun _ _ => forall₂_imp (fun _ _ h hx hy => (h hx hy).commute))

Depends on / 依赖: commute, f.pairwise_disjoint_of_mem_zpowers.mono, pairwise_disjoint_of_mem_zpowers
-/
lemma pairwise_commute_of_mem_zpowers :
    Pairwise fun (i j : f.cycleFactorsFinset) =>
      forall (x y : Perm α), x in Subgroup.zpowers ↑i -> y in Subgroup.zpowers ↑j -> Commute x y :=
  f.pairwise_disjoint_of_mem_zpowers.mono
    (fun _ _ => forall₂_imp (fun _ _ h hx hy => (h hx hy).commute))

/--
lemma `disjoint_ofSubtype_noncommPiCoprod` / 引理 `disjoint_ofSubtype_noncommPiCoprod`

English:
lemma disjoint_ofSubtype_noncommPiCoprod
  statement: (u : Perm (Function.fixedPoints f))
  proof: by
  apply Finset.noncommProd_induction
  · intro a _ b _ h
    apply f.pairwise_commute_of_mem_zpowers h <;> simp only [Subgroup.coe_subtype, SetLike.coe_mem]
  · intro x y
    exact Disjoint.mul_right
  · exact disjoint_one_right _
  · intro c _
    simp only [Subgroup.coe_subtype]
    exact Disjoint.mono (disjoint_ofSubtype_of_memFixedPoints_self u)
      le_rfl (support_zpowers_of_mem_cycleFactorsFinset_le (v c))

中文:
引理 disjoint_ofSubtype_noncommPiCoprod
  结论: (u : 置换 (函数.fixedPoints f))
  证明: by
  apply Finset.noncommProd_induction
  · intro a _ b _ h
    apply f.pairwise_commute_of_mem_zpowers h <;> simp only [Subgroup.coe_subtype, SetLike.coe_mem]
  · intro x y
    exact Disjoint.mul_right
  · exact disjoint_one_right _
  · intro c _
    simp only [Subgroup.coe_subtype]
    exact Disjoint.mono (disjoint_ofSubtype_of_memFixedPoints_self u)
      le_rfl (support_zpowers_of_mem_cycleFactorsFinset_le (v c))

Depends on / 依赖: Disjoint, Disjoint.mono, Disjoint.mul_right, Finset, Finset.noncommProd_induction, SetLike, SetLike.coe_mem, Subgroup, Subgroup.coe_subtype, coe_mem, coe_subtype, disjoint_ofSubtype_of_memFixedPoints_self, disjoint_one_right, f.pairwise_commute_of_mem_zpowers, le_rfl, mul_right, noncommProd_induction, pairwise_commute_of_mem_zpowers, support_zpowers_of_mem_cycleFactorsFinset_le
-/
lemma disjoint_ofSubtype_noncommPiCoprod (u : Perm (Function.fixedPoints f))
    (v : (c : { x // x in f.cycleFactorsFinset }) -> (Subgroup.zpowers (c : Perm α))) :
    Disjoint (ofSubtype u) ((Subgroup.noncommPiCoprod f.pairwise_commute_of_mem_zpowers) v) := by
  apply Finset.noncommProd_induction
  · intro a _ b _ h
    apply f.pairwise_commute_of_mem_zpowers h <;> simp only [Subgroup.coe_subtype, SetLike.coe_mem]
  · intro x y
    exact Disjoint.mul_right
  · exact disjoint_one_right _
  · intro c _
    simp only [Subgroup.coe_subtype]
    exact Disjoint.mono (disjoint_ofSubtype_of_memFixedPoints_self u)
      le_rfl (support_zpowers_of_mem_cycleFactorsFinset_le (v c))

/--
lemma `commute_ofSubtype_noncommPiCoprod` / 引理 `commute_ofSubtype_noncommPiCoprod`

English:
lemma commute_ofSubtype_noncommPiCoprod
  statement: (u : Perm (Function.fixedPoints f))
  proof: Disjoint.commute (f.disjoint_ofSubtype_noncommPiCoprod u v)

中文:
引理 commute_ofSubtype_noncommPiCoprod
  结论: (u : 置换 (函数.fixedPoints f))
  证明: Disjoint.commute (f.disjoint_ofSubtype_noncommPiCoprod u v)

Depends on / 依赖: Disjoint, Disjoint.commute, commute, disjoint_ofSubtype_noncommPiCoprod, f.disjoint_ofSubtype_noncommPiCoprod
-/
lemma commute_ofSubtype_noncommPiCoprod (u : Perm (Function.fixedPoints f))
    (v : (c : { x // x in f.cycleFactorsFinset }) -> (Subgroup.zpowers (c : Perm α))) :
    Commute (ofSubtype u) ((Subgroup.noncommPiCoprod f.pairwise_commute_of_mem_zpowers) v) :=
  Disjoint.commute (f.disjoint_ofSubtype_noncommPiCoprod u v)

/--
theorem `mem_support_iff_mem_support_of_mem_cycleFactorsFinset` / 定理 `mem_support_iff_mem_support_of_mem_cycleFactorsFinset`

English:
theorem mem_support_iff_mem_support_of_mem_cycleFactorsFinset
  given: {g : Equiv.Perm α} {x : α}
  proof: by
  constructor
  · intro h
    use g.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr h
    rw [mem_support_cycleOf_iff]
    exact ⟨SameCycle.refl g x, h⟩
  · rintro ⟨c, hc, hx⟩
    exact mem_cycleFactorsFinset_support_le hc hx

中文:
定理 mem_support_iff_mem_support_of_mem_cycleFactorsFinset
  条件: {g : 等价.置换 α} {x : α}
  证明: by
  constructor
  · intro h
    use g.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr h
    rw [mem_support_cycleOf_iff]
    exact ⟨SameCycle.refl g x, h⟩
  · rintro ⟨c, hc, hx⟩
    exact mem_cycleFactorsFinset_support_le hc hx

Depends on / 依赖: SameCycle, SameCycle.refl, cycleOf, cycleOf_mem_cycleFactorsFinset_iff, cycleOf_mem_cycleFactorsFinset_iff.mpr, g.cycleOf, mem_cycleFactorsFinset_support_le, mem_support_cycleOf_iff
-/
theorem mem_support_iff_mem_support_of_mem_cycleFactorsFinset {g : Equiv.Perm α} {x : α} :
    x in g.support ↔ exists c in g.cycleFactorsFinset, x in c.support := by
  constructor
  · intro h
    use g.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr h
    rw [mem_support_cycleOf_iff]
    exact ⟨SameCycle.refl g x, h⟩
  · rintro ⟨c, hc, hx⟩
    exact mem_cycleFactorsFinset_support_le hc hx

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `cycleFactorsFinset_eq_empty_iff` / 定理 `cycleFactorsFinset_eq_empty_iff`

English:
theorem cycleFactorsFinset_eq_empty_iff
  given: {f : Perm α}
  statement: cycleFactorsFinset f = ∅ ↔ f = 1
  proof: by
  simpa [cycleFactorsFinset_eq_finset] using eq_comm

@[simp]

中文:
定理 cycleFactorsFinset_eq_empty_iff
  条件: {f : 置换 α}
  结论: cycleFactorsFinset f = ∅ ↔ f = 1
  证明: by
  simpa [cycleFactorsFinset_eq_finset] using eq_comm

@[simp]

Depends on / 依赖: cycleFactorsFinset_eq_finset, eq_comm
-/
theorem cycleFactorsFinset_eq_empty_iff {f : Perm α} : cycleFactorsFinset f = ∅ ↔ f = 1 := by
  simpa [cycleFactorsFinset_eq_finset] using eq_comm

@[simp]
/--
theorem `cycleFactorsFinset_one` / 定理 `cycleFactorsFinset_one`

English:
theorem cycleFactorsFinset_one
  statement: cycleFactorsFinset (1 : Perm α) = ∅
  proof: by
  simp [cycleFactorsFinset_eq_empty_iff]

@[simp]

中文:
定理 cycleFactorsFinset_one
  结论: cycleFactorsFinset (1 : 置换 α) = ∅
  证明: by
  simp [cycleFactorsFinset_eq_empty_iff]

@[simp]

Depends on / 依赖: cycleFactorsFinset_eq_empty_iff
-/
theorem cycleFactorsFinset_one : cycleFactorsFinset (1 : Perm α) = ∅ := by
  simp [cycleFactorsFinset_eq_empty_iff]

@[simp]
/--
theorem `cycleFactorsFinset_eq_singleton_self_iff` / 定理 `cycleFactorsFinset_eq_singleton_self_iff`

English:
theorem cycleFactorsFinset_eq_singleton_self_iff
  given: {f : Perm α}
  proof: by simp [cycleFactorsFinset_eq_finset]

中文:
定理 cycleFactorsFinset_eq_singleton_self_iff
  条件: {f : 置换 α}
  证明: by simp [cycleFactorsFinset_eq_finset]

Depends on / 依赖: cycleFactorsFinset_eq_finset
-/
theorem cycleFactorsFinset_eq_singleton_self_iff {f : Perm α} :
    f.cycleFactorsFinset = {f} ↔ f.IsCycle := by simp [cycleFactorsFinset_eq_finset]

/--
theorem `IsCycle.cycleFactorsFinset_eq_singleton` / 定理 `IsCycle.cycleFactorsFinset_eq_singleton`

English:
theorem IsCycle.cycleFactorsFinset_eq_singleton
  given: {f : Perm α} (hf : IsCycle f)
  proof: cycleFactorsFinset_eq_singleton_self_iff.mpr hf

中文:
定理 是环.cycleFactorsFinset_eq_singleton
  条件: {f : 置换 α} (hf : 是环 f)
  证明: cycleFactorsFinset_eq_singleton_self_iff.mpr hf

Depends on / 依赖: cycleFactorsFinset_eq_singleton_self_iff, cycleFactorsFinset_eq_singleton_self_iff.mpr
-/
theorem IsCycle.cycleFactorsFinset_eq_singleton {f : Perm α} (hf : IsCycle f) :
    f.cycleFactorsFinset = {f} :=
  cycleFactorsFinset_eq_singleton_self_iff.mpr hf

/--
theorem `cycleFactorsFinset_eq_singleton_iff` / 定理 `cycleFactorsFinset_eq_singleton_iff`

English:
theorem cycleFactorsFinset_eq_singleton_iff
  given: {f g : Perm α}
  proof: by
  suffices f = g -> (g.IsCycle ↔ f.IsCycle) by
    rw [cycleFactorsFinset_eq_finset]
    simpa [eq_comm]
  rintro rfl
  exact Iff.rfl

中文:
定理 cycleFactorsFinset_eq_singleton_iff
  条件: {f g : 置换 α}
  证明: by
  suffices f = g -> (g.IsCycle ↔ f.IsCycle) by
    rw [cycleFactorsFinset_eq_finset]
    simpa [eq_comm]
  rintro rfl
  exact Iff.rfl

Depends on / 依赖: Iff.rfl, IsCycle, cycleFactorsFinset_eq_finset, eq_comm, f.IsCycle, g.IsCycle
-/
theorem cycleFactorsFinset_eq_singleton_iff {f g : Perm α} :
    f.cycleFactorsFinset = {g} ↔ f.IsCycle ∧ f = g := by
  suffices f = g -> (g.IsCycle ↔ f.IsCycle) by
    rw [cycleFactorsFinset_eq_finset]
    simpa [eq_comm]
  rintro rfl
  exact Iff.rfl

/--
theorem `cycleFactorsFinset_injective` / 定理 `cycleFactorsFinset_injective`

English:
theorem cycleFactorsFinset_injective
  statement: Function.Injective (@cycleFactorsFinset α _ _)
  proof: by
  intro f g h
  rw [← cycleFactorsFinset_noncommProd f]
  simpa [h] using cycleFactorsFinset_noncommProd g

中文:
定理 cycleFactorsFinset_injective
  结论: 函数.单射 (@cycleFactorsFinset α _ _)
  证明: by
  intro f g h
  rw [← cycleFactorsFinset_noncommProd f]
  simpa [h] using cycleFactorsFinset_noncommProd g

Depends on / 依赖: cycleFactorsFinset_noncommProd
-/
theorem cycleFactorsFinset_injective : Function.Injective (@cycleFactorsFinset α _ _) := by
  intro f g h
  rw [← cycleFactorsFinset_noncommProd f]
  simpa [h] using cycleFactorsFinset_noncommProd g

/--
theorem `Disjoint.disjoint_cycleFactorsFinset` / 定理 `Disjoint.disjoint_cycleFactorsFinset`

English:
theorem Disjoint.disjoint_cycleFactorsFinset
  given: {f g : Perm α} (h : Disjoint f g)
  proof: by
  rw [disjoint_iff_disjoint_support] at h
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [mem_cycleFactorsFinset_iff, mem_support] at hx hy
  obtain ⟨⟨⟨a, ha, -⟩, hf⟩, -, hg⟩ := hx, hy
  have := h.le_bot (by simp [ha, ← hf a ha, ← hg a ha] : a in f.support inter g.support)
  tauto

中文:
定理 Disjoint.disjoint_cycleFactorsFinset
  条件: {f g : 置换 α} (h : Disjoint f g)
  证明: by
  rw [disjoint_iff_disjoint_support] at h
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [mem_cycleFactorsFinset_iff, mem_support] at hx hy
  obtain ⟨⟨⟨a, ha, -⟩, hf⟩, -, hg⟩ := hx, hy
  have := h.le_bot (by simp [ha, ← hf a ha, ← hg a ha] : a in f.support inter g.support)
  tauto

Depends on / 依赖: Finset, Finset.disjoint_left, disjoint_iff_disjoint_support, disjoint_left, f.support, g.support, h.le_bot, le_bot, mem_cycleFactorsFinset_iff, mem_support, support
-/
theorem Disjoint.disjoint_cycleFactorsFinset {f g : Perm α} (h : Disjoint f g) :
    _root_.Disjoint (cycleFactorsFinset f) (cycleFactorsFinset g) := by
  rw [disjoint_iff_disjoint_support] at h
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [mem_cycleFactorsFinset_iff, mem_support] at hx hy
  obtain ⟨⟨⟨a, ha, -⟩, hf⟩, -, hg⟩ := hx, hy
  have := h.le_bot (by simp [ha, ← hf a ha, ← hg a ha] : a in f.support inter g.support)
  tauto

/--
theorem `Disjoint.cycleFactorsFinset_mul_eq_union` / 定理 `Disjoint.cycleFactorsFinset_mul_eq_union`

English:
theorem Disjoint.cycleFactorsFinset_mul_eq_union
  given: {f g : Perm α} (h : Disjoint f g)
  proof: by
  rw [cycleFactorsFinset_eq_finset]
  refine ⟨?_, ?_, ?_⟩
  · simp [or_imp, mem_cycleFactorsFinset_iff, forall_comm]
  · rw [coe_union, Set.pairwise_union_of_symm]
    exact
      ⟨cycleFactorsFinset_pairwise_disjoint _, cycleFactorsFinset_pairwise_disjoint _,
        fun x hx y hy _ =>
        h.mono (mem_cycleFactorsFinset_support_le hx) (mem_cycleFactorsFinset_support_le hy)⟩
  · rw [noncommProd_union_of_disjoint h.disjoint_cycleFactorsFinset]
    rw [cycleFactorsFinset_noncommProd]; rw [cycleFactorsFinset_noncommProd]

中文:
定理 Disjoint.cycleFactorsFinset_mul_eq_union
  条件: {f g : 置换 α} (h : Disjoint f g)
  证明: by
  rw [cycleFactorsFinset_eq_finset]
  refine ⟨?_, ?_, ?_⟩
  · simp [or_imp, mem_cycleFactorsFinset_iff, forall_comm]
  · rw [coe_union, Set.pairwise_union_of_symm]
    exact
      ⟨cycleFactorsFinset_pairwise_disjoint _, cycleFactorsFinset_pairwise_disjoint _,
        fun x hx y hy _ =>
        h.mono (mem_cycleFactorsFinset_support_le hx) (mem_cycleFactorsFinset_support_le hy)⟩
  · rw [noncommProd_union_of_disjoint h.disjoint_cycleFactorsFinset]
    rw [cycleFactorsFinset_noncommProd]; rw [cycleFactorsFinset_noncommProd]

Depends on / 依赖: Set.pairwise_union_of_symm, coe_union, cycleFactorsFinset_eq_finset, cycleFactorsFinset_noncommProd, cycleFactorsFinset_pairwise_disjoint, disjoint_cycleFactorsFinset, forall_comm, h.disjoint_cycleFactorsFinset, h.mono, mem_cycleFactorsFinset_iff, mem_cycleFactorsFinset_support_le, noncommProd_union_of_disjoint, or_imp, pairwise_union_of_symm
-/
theorem Disjoint.cycleFactorsFinset_mul_eq_union {f g : Perm α} (h : Disjoint f g) :
    cycleFactorsFinset (f * g) = cycleFactorsFinset f union cycleFactorsFinset g := by
  rw [cycleFactorsFinset_eq_finset]
  refine ⟨?_, ?_, ?_⟩
  · simp [or_imp, mem_cycleFactorsFinset_iff, forall_comm]
  · rw [coe_union, Set.pairwise_union_of_symm]
    exact
      ⟨cycleFactorsFinset_pairwise_disjoint _, cycleFactorsFinset_pairwise_disjoint _,
        fun x hx y hy _ =>
        h.mono (mem_cycleFactorsFinset_support_le hx) (mem_cycleFactorsFinset_support_le hy)⟩
  · rw [noncommProd_union_of_disjoint h.disjoint_cycleFactorsFinset]
    rw [cycleFactorsFinset_noncommProd]; rw [cycleFactorsFinset_noncommProd]

/--
theorem `disjoint_mul_inv_of_mem_cycleFactorsFinset` / 定理 `disjoint_mul_inv_of_mem_cycleFactorsFinset`

English:
theorem disjoint_mul_inv_of_mem_cycleFactorsFinset
  given: {f g : Perm α} (h : f in cycleFactorsFinset g)
  proof: by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x
  by_cases hx : f x = x
  · exact Or.inr hx
  left
  rw [mul_apply]; rw [← h.right _ (by simpa [eq_symm_apply])]
  simp

中文:
定理 disjoint_mul_inv_of_mem_cycleFactorsFinset
  条件: {f g : 置换 α} (h : f in cycleFactorsFinset g)
  证明: by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x
  by_cases hx : f x = x
  · exact Or.inr hx
  left
  rw [mul_apply]; rw [← h.right _ (by simpa [eq_symm_apply])]
  simp

Depends on / 依赖: Or.inr, eq_symm_apply, h.right, mem_cycleFactorsFinset_iff, mul_apply
-/
theorem disjoint_mul_inv_of_mem_cycleFactorsFinset {f g : Perm α} (h : f in cycleFactorsFinset g) :
    Disjoint (g * f⁻¹) f := by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x
  by_cases hx : f x = x
  · exact Or.inr hx
  left
  rw [mul_apply]; rw [← h.right _ (by simpa [eq_symm_apply])]
  simp

/--
theorem `cycle_is_cycleOf` / 定理 `cycle_is_cycleOf`

English:
theorem cycle_is_cycleOf
  statement: {f c : Equiv.Perm α} {a : α} (ha : a in c.support)
  proof: by
  suffices f.cycleOf a = c.cycleOf a by
    rw [this]
    apply symm
    exact
      Equiv.Perm.IsCycle.cycleOf_eq (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).left
        (Equiv.Perm.mem_support.mp ha)
  let hfc := (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc).symm
  let hfc2 := Perm.Disjoint.commute hfc
  rw [← Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hfc2]
  · simp only [hfc2.eq, inv_mul_cancel_right]
  -- `a` is in the support of `c`, hence it is not in the support of `g c⁻¹`
  exact
    Equiv.Perm.notMem_support.mp
      (Finset.disjoint_left.mp (Equiv.Perm.Disjoint.disjoint_support hfc) ha)

中文:
定理 cycle_is_cycleOf
  结论: {f c : 等价.置换 α} {a : α} (ha : a in c.support)
  证明: by
  suffices f.cycleOf a = c.cycleOf a by
    rw [this]
    apply symm
    exact
      Equiv.Perm.IsCycle.cycleOf_eq (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).left
        (Equiv.Perm.mem_support.mp ha)
  let hfc := (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc).symm
  let hfc2 := Perm.Disjoint.commute hfc
  rw [← Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hfc2]
  · simp only [hfc2.eq, inv_mul_cancel_right]
  -- `a` is in the support of `c`, hence it is not in the support of `g c⁻¹`
  exact
    Equiv.Perm.notMem_support.mp
      (Finset.disjoint_left.mp (Equiv.Perm.Disjoint.disjoint_support hfc) ha)

Depends on / 依赖: Disjoint, Equiv.Perm.IsCycle.cycleOf_eq, Equiv.Perm.cycleOf_mul_of_apply_right_eq_self, Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset, Equiv.Perm.mem_cycleFactorsFinset_iff.mp, Equiv.Perm.mem_support.mp, IsCycle, Perm.Disjoint.commute, c.cycleOf, commute, cycleOf, cycleOf_eq, cycleOf_mul_of_apply_right_eq_self, disjoint_mul_inv_of_mem_cycleFactorsFinset, f.cycleOf, hfc2.eq, inv_mul_cancel_right, mem_cycleFactorsFinset_iff, mem_support
-/
theorem cycle_is_cycleOf {f c : Equiv.Perm α} {a : α} (ha : a in c.support)
    (hc : c in f.cycleFactorsFinset) : c = f.cycleOf a := by
  suffices f.cycleOf a = c.cycleOf a by
    rw [this]
    apply symm
    exact
      Equiv.Perm.IsCycle.cycleOf_eq (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).left
        (Equiv.Perm.mem_support.mp ha)
  let hfc := (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc).symm
  let hfc2 := Perm.Disjoint.commute hfc
  rw [← Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hfc2]
  · simp only [hfc2.eq, inv_mul_cancel_right]
  -- `a` is in the support of `c`, hence it is not in the support of `g c⁻¹`
  exact
    Equiv.Perm.notMem_support.mp
      (Finset.disjoint_left.mp (Equiv.Perm.Disjoint.disjoint_support hfc) ha)

/--
theorem `isCycleOn_support_of_mem_cycleFactorsFinset` / 定理 `isCycleOn_support_of_mem_cycleFactorsFinset`

English:
theorem isCycleOn_support_of_mem_cycleFactorsFinset
  statement: {g c : Equiv.Perm α}
  proof: by
  obtain ⟨x, hx⟩ := IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp hc).1
  rw [cycle_is_cycleOf hx hc]
  exact isCycleOn_support_cycleOf g x

中文:
定理 isCycleOn_support_of_mem_cycleFactorsFinset
  结论: {g c : 等价.置换 α}
  证明: by
  obtain ⟨x, hx⟩ := IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp hc).1
  rw [cycle_is_cycleOf hx hc]
  exact isCycleOn_support_cycleOf g x

Depends on / 依赖: IsCycle, IsCycle.nonempty_support, cycle_is_cycleOf, isCycleOn_support_cycleOf, mem_cycleFactorsFinset_iff, mem_cycleFactorsFinset_iff.mp, nonempty_support
-/
theorem isCycleOn_support_of_mem_cycleFactorsFinset {g c : Equiv.Perm α}
    (hc : c in g.cycleFactorsFinset) :
    IsCycleOn g c.support := by
  obtain ⟨x, hx⟩ := IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp hc).1
  rw [cycle_is_cycleOf hx hc]
  exact isCycleOn_support_cycleOf g x

/--
theorem `eq_cycleOf_of_mem_cycleFactorsFinset_iff` / 定理 `eq_cycleOf_of_mem_cycleFactorsFinset_iff`

English:
theorem eq_cycleOf_of_mem_cycleFactorsFinset_iff
  proof: by
  refine ⟨?_, (cycle_is_cycleOf · hc)⟩
  rintro rfl
  rw [mem_support]; rw [cycleOf_apply_self]; rw [ne_eq]; rw [← cycleOf_eq_one_iff]
  exact (mem_cycleFactorsFinset_iff.mp hc).left.ne_one

中文:
定理 eq_cycleOf_of_mem_cycleFactorsFinset_iff
  证明: by
  refine ⟨?_, (cycle_is_cycleOf · hc)⟩
  rintro rfl
  rw [mem_support]; rw [cycleOf_apply_self]; rw [ne_eq]; rw [← cycleOf_eq_one_iff]
  exact (mem_cycleFactorsFinset_iff.mp hc).left.ne_one

Depends on / 依赖: cycleOf_apply_self, cycleOf_eq_one_iff, cycle_is_cycleOf, left.ne_one, mem_cycleFactorsFinset_iff, mem_cycleFactorsFinset_iff.mp, mem_support, ne_eq, ne_one
-/
theorem eq_cycleOf_of_mem_cycleFactorsFinset_iff
    (g c : Perm α) (hc : c in g.cycleFactorsFinset) (x : α) :
    c = g.cycleOf x ↔ x in c.support := by
  refine ⟨?_, (cycle_is_cycleOf · hc)⟩
  rintro rfl
  rw [mem_support]; rw [cycleOf_apply_self]; rw [ne_eq]; rw [← cycleOf_eq_one_iff]
  exact (mem_cycleFactorsFinset_iff.mp hc).left.ne_one

/--
theorem `zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff` / 定理 `zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff`

English:
theorem zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff
  statement: {g : Perm α}
  proof: by
  rw [← g.eq_cycleOf_of_mem_cycleFactorsFinset_iff _ c.prop]; rw [cycleOf_self_apply_zpow]; rw [eq_cycleOf_of_mem_cycleFactorsFinset_iff _ _ c.prop]

中文:
定理 zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff
  结论: {g : 置换 α}
  证明: by
  rw [← g.eq_cycleOf_of_mem_cycleFactorsFinset_iff _ c.prop]; rw [cycleOf_self_apply_zpow]; rw [eq_cycleOf_of_mem_cycleFactorsFinset_iff _ _ c.prop]

Depends on / 依赖: c.prop, cycleOf_self_apply_zpow, eq_cycleOf_of_mem_cycleFactorsFinset_iff, g.eq_cycleOf_of_mem_cycleFactorsFinset_iff
-/
theorem zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff {g : Perm α}
    {x : α} {m : Int} {c : g.cycleFactorsFinset} :
    (g ^ m) x in (c : Perm α).support ↔ x in (c : Perm α).support := by
  rw [← g.eq_cycleOf_of_mem_cycleFactorsFinset_iff _ c.prop]; rw [cycleOf_self_apply_zpow]; rw [eq_cycleOf_of_mem_cycleFactorsFinset_iff _ _ c.prop]

/--
theorem `mem_cycleFactorsFinset_conj` / 定理 `mem_cycleFactorsFinset_conj`

English:
theorem mem_cycleFactorsFinset_conj
  given: (g k c : Perm α)
  proof: by
  suffices imp_lemma : forall {g k c : Perm α},
      c in g.cycleFactorsFinset -> k * c * k⁻¹ in (k * g * k⁻¹).cycleFactorsFinset by
    refine ⟨fun h => ?_, imp_lemma⟩
    have aux : forall h : Perm α, h = k⁻¹ * (k * h * k⁻¹) * k := fun _ => by group
    rw [aux g]; rw [aux c]
    exact imp_lemma h
  intro g k c
  simp only [mem_cycleFactorsFinset_iff]
  apply And.imp IsCycle.conj
  intro hc a ha
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  apply hc
  simp_all

中文:
定理 mem_cycleFactorsFinset_conj
  条件: (g k c : 置换 α)
  证明: by
  suffices imp_lemma : forall {g k c : Perm α},
      c in g.cycleFactorsFinset -> k * c * k⁻¹ in (k * g * k⁻¹).cycleFactorsFinset by
    refine ⟨fun h => ?_, imp_lemma⟩
    have aux : forall h : Perm α, h = k⁻¹ * (k * h * k⁻¹) * k := fun _ => by group
    rw [aux g]; rw [aux c]
    exact imp_lemma h
  intro g k c
  simp only [mem_cycleFactorsFinset_iff]
  apply And.imp IsCycle.conj
  intro hc a ha
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  apply hc
  simp_all

Depends on / 依赖: And.imp, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Function, Function.comp_apply, IsCycle, IsCycle.conj, apply_eq_iff_eq, coe_mul, comp_apply, cycleFactorsFinset, g.cycleFactorsFinset, imp_lemma, mem_cycleFactorsFinset_iff
-/
theorem mem_cycleFactorsFinset_conj (g k c : Perm α) :
    k * c * k⁻¹ in (k * g * k⁻¹).cycleFactorsFinset ↔ c in g.cycleFactorsFinset := by
  suffices imp_lemma : forall {g k c : Perm α},
      c in g.cycleFactorsFinset -> k * c * k⁻¹ in (k * g * k⁻¹).cycleFactorsFinset by
    refine ⟨fun h => ?_, imp_lemma⟩
    have aux : forall h : Perm α, h = k⁻¹ * (k * h * k⁻¹) * k := fun _ => by group
    rw [aux g]; rw [aux c]
    exact imp_lemma h
  intro g k c
  simp only [mem_cycleFactorsFinset_iff]
  apply And.imp IsCycle.conj
  intro hc a ha
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  apply hc
  simp_all

/--
theorem `commute_of_mem_cycleFactorsFinset_commute` / 定理 `commute_of_mem_cycleFactorsFinset_commute`

English:
theorem commute_of_mem_cycleFactorsFinset_commute
  statement: (k g : Perm α)
  proof: by
  rw [← cycleFactorsFinset_noncommProd g (cycleFactorsFinset_mem_commute g)]
  apply Finset.noncommProd_commute
  simpa only [id_eq] using hk

中文:
定理 commute_of_mem_cycleFactorsFinset_commute
  结论: (k g : 置换 α)
  证明: by
  rw [← cycleFactorsFinset_noncommProd g (cycleFactorsFinset_mem_commute g)]
  apply Finset.noncommProd_commute
  simpa only [id_eq] using hk

Depends on / 依赖: Finset, Finset.noncommProd_commute, cycleFactorsFinset_mem_commute, cycleFactorsFinset_noncommProd, id_eq, noncommProd_commute
-/
theorem commute_of_mem_cycleFactorsFinset_commute (k g : Perm α)
    (hk : forall c in g.cycleFactorsFinset, Commute k c) :
    Commute k g := by
  rw [← cycleFactorsFinset_noncommProd g (cycleFactorsFinset_mem_commute g)]
  apply Finset.noncommProd_commute
  simpa only [id_eq] using hk

/--
theorem `self_mem_cycle_factors_commute` / 定理 `self_mem_cycle_factors_commute`

English:
theorem self_mem_cycle_factors_commute
  statement: {g c : Perm α}
  proof: by
  apply commute_of_mem_cycleFactorsFinset_commute
  intro c' hc'
  by_cases hcc' : c = c'
  · rw [hcc']
  · apply g.cycleFactorsFinset_mem_commute hc hc'; exact hcc'

中文:
定理 self_mem_cycle_factors_commute
  结论: {g c : 置换 α}
  证明: by
  apply commute_of_mem_cycleFactorsFinset_commute
  intro c' hc'
  by_cases hcc' : c = c'
  · rw [hcc']
  · apply g.cycleFactorsFinset_mem_commute hc hc'; exact hcc'

Depends on / 依赖: commute_of_mem_cycleFactorsFinset_commute, cycleFactorsFinset_mem_commute, g.cycleFactorsFinset_mem_commute
-/
theorem self_mem_cycle_factors_commute {g c : Perm α}
    (hc : c in g.cycleFactorsFinset) : Commute c g := by
  apply commute_of_mem_cycleFactorsFinset_commute
  intro c' hc'
  by_cases hcc' : c = c'
  · rw [hcc']
  · apply g.cycleFactorsFinset_mem_commute hc hc'; exact hcc'

/--
theorem `mem_support_cycle_of_cycle` / 定理 `mem_support_cycle_of_cycle`

English:
theorem mem_support_cycle_of_cycle
  statement: {g d c : Perm α}
  proof: by
  intro x
  simp only [mem_support, not_iff_not]
  by_cases h : c = d
  · rw [← h, EmbeddingLike.apply_eq_iff_eq]
  · rw [← Perm.mul_apply,
      Commute.eq (cycleFactorsFinset_mem_commute g hc hd h),
      mul_apply, EmbeddingLike.apply_eq_iff_eq]

中文:
定理 mem_support_cycle_of_cycle
  结论: {g d c : 置换 α}
  证明: by
  intro x
  simp only [mem_support, not_iff_not]
  by_cases h : c = d
  · rw [← h, EmbeddingLike.apply_eq_iff_eq]
  · rw [← Perm.mul_apply,
      Commute.eq (cycleFactorsFinset_mem_commute g hc hd h),
      mul_apply, EmbeddingLike.apply_eq_iff_eq]

Depends on / 依赖: Commute, Commute.eq, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Perm.mul_apply, apply_eq_iff_eq, cycleFactorsFinset_mem_commute, mem_support, mul_apply, not_iff_not
-/
theorem mem_support_cycle_of_cycle {g d c : Perm α}
    (hc : c in g.cycleFactorsFinset) (hd : d in g.cycleFactorsFinset) :
    forall x : α, d x in c.support ↔ x in c.support := by
  intro x
  simp only [mem_support, not_iff_not]
  by_cases h : c = d
  · rw [← h, EmbeddingLike.apply_eq_iff_eq]
  · rw [← Perm.mul_apply,
      Commute.eq (cycleFactorsFinset_mem_commute g hc hd h),
      mul_apply, EmbeddingLike.apply_eq_iff_eq]

/--
theorem `mem_cycleFactorsFinset_support` / 定理 `mem_cycleFactorsFinset_support`

English:
theorem mem_cycleFactorsFinset_support
  given: {g c : Perm α} (hc : c in g.cycleFactorsFinset) (a : α)
  proof: mem_support_iff_of_commute (self_mem_cycle_factors_commute hc).symm a

中文:
定理 mem_cycleFactorsFinset_support
  条件: {g c : 置换 α} (hc : c in g.cycleFactorsFinset) (a : α)
  证明: mem_support_iff_of_commute (self_mem_cycle_factors_commute hc).symm a

Depends on / 依赖: mem_support_iff_of_commute, self_mem_cycle_factors_commute
-/
theorem mem_cycleFactorsFinset_support {g c : Perm α} (hc : c in g.cycleFactorsFinset) (a : α) :
    g a in c.support ↔ a in c.support :=
  mem_support_iff_of_commute (self_mem_cycle_factors_commute hc).symm a

end CycleFactorsFinset

@[elab_as_elim]
/--
theorem `cycle_induction_on` / 定理 `cycle_induction_on`

English:
theorem cycle_induction_on
  statement: [Finite β] (P : Perm β -> Prop) (σ : Perm β) (base_one : P 1)
  proof: by
  cases nonempty_fintype β
  suffices forall l : List (Perm β),
      (forall τ : Perm β, τ in l -> τ.IsCycle) -> l.Pairwise Disjoint -> P l.prod by
    classical
      let x := σ.truncCycleFactors.out
      exact (congr_arg P x.2.1).mp (this x.1 x.2.2.1 x.2.2.2)
  intro l
  induction l with
  | nil => exact fun _ _ => base_one
  | cons σ l ih =>
    intro h1 h2
    rw [List.prod_cons]
    exact
      induction_disjoint σ l.prod (disjoint_prod_right _ (List.pairwise_cons.mp h2).1)
        (h1 _ List.mem_cons_self) (base_cycles σ (h1 σ List.mem_cons_self))
        (ih (fun τ hτ => h1 τ (List.mem_cons_of_mem σ hτ)) h2.of_cons)

中文:
定理 cycle_induction_on
  结论: [有限 β] (P : 置换 β -> 命题) (σ : 置换 β) (base_one : P 1)
  证明: by
  cases nonempty_fintype β
  suffices forall l : List (Perm β),
      (forall τ : Perm β, τ in l -> τ.IsCycle) -> l.Pairwise Disjoint -> P l.prod by
    classical
      let x := σ.truncCycleFactors.out
      exact (congr_arg P x.2.1).mp (this x.1 x.2.2.1 x.2.2.2)
  intro l
  induction l with
  | nil => exact fun _ _ => base_one
  | cons σ l ih =>
    intro h1 h2
    rw [List.prod_cons]
    exact
      induction_disjoint σ l.prod (disjoint_prod_right _ (List.pairwise_cons.mp h2).1)
        (h1 _ List.mem_cons_self) (base_cycles σ (h1 σ List.mem_cons_self))
        (ih (fun τ hτ => h1 τ (List.mem_cons_of_mem σ hτ)) h2.of_cons)

Depends on / 依赖: Disjoint, IsCycle, List.mem_cons_se, List.mem_cons_self, List.pairwise_cons.mp, List.prod_cons, Pairwise, base_cycles, base_one, classical, congr_arg, disjoint_prod_right, induction_disjoint, l.Pairwise, l.prod, mem_cons_se, mem_cons_self, nonempty_fintype, pairwise_cons, prod_cons
-/
theorem cycle_induction_on [Finite β] (P : Perm β -> Prop) (σ : Perm β) (base_one : P 1)
    (base_cycles : forall σ : Perm β, σ.IsCycle -> P σ)
    (induction_disjoint : forall σ τ : Perm β,
      Disjoint σ τ -> IsCycle σ -> P σ -> P τ -> P (σ * τ)) : P σ := by
  cases nonempty_fintype β
  suffices forall l : List (Perm β),
      (forall τ : Perm β, τ in l -> τ.IsCycle) -> l.Pairwise Disjoint -> P l.prod by
    classical
      let x := σ.truncCycleFactors.out
      exact (congr_arg P x.2.1).mp (this x.1 x.2.2.1 x.2.2.2)
  intro l
  induction l with
  | nil => exact fun _ _ => base_one
  | cons σ l ih =>
    intro h1 h2
    rw [List.prod_cons]
    exact
      induction_disjoint σ l.prod (disjoint_prod_right _ (List.pairwise_cons.mp h2).1)
        (h1 _ List.mem_cons_self) (base_cycles σ (h1 σ List.mem_cons_self))
        (ih (fun τ hτ => h1 τ (List.mem_cons_of_mem σ hτ)) h2.of_cons)

/--
theorem `cycleFactorsFinset_mul_inv_mem_eq_sdiff` / 定理 `cycleFactorsFinset_mul_inv_mem_eq_sdiff`

English:
theorem cycleFactorsFinset_mul_inv_mem_eq_sdiff
  statement: [DecidableEq α] [Fintype α] {f g : Perm α}
  proof: by
  revert f
  refine
    cycle_induction_on (P := fun {g : Perm α} =>
      forall {f}, (f in cycleFactorsFinset g)
        -> cycleFactorsFinset (g * f⁻¹) = cycleFactorsFinset g \ {f}) _ ?_ ?_ ?_
  · simp
  · intro σ hσ f hf
    simp only [cycleFactorsFinset_eq_singleton_self_iff.mpr hσ, mem_singleton] at hf ⊢
    simp [hf]
  · intro σ τ hd _ hσ hτ f
    simp_rw [hd.cycleFactorsFinset_mul_eq_union, mem_union]
    -- if only `wlog` could work here...
    rintro (hf | hf)
    · rw [hd.commute.eq, union_comm, union_sdiff_distrib, sdiff_singleton_eq_erase,
        erase_eq_of_notMem, mul_assoc, Disjoint.cycleFactorsFinset_mul_eq_union, hσ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        rcases hd.symm x with hx | hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        notMem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem hf H))
    · rw [union_sdiff_distrib, sdiff_singleton_eq_erase, erase_eq_of_notMem, mul_assoc,
        Disjoint.cycleFactorsFinset_mul_eq_union, hτ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        rcases hd x with hx | hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        notMem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem H hf))

中文:
定理 cycleFactorsFinset_mul_inv_mem_eq_sdiff
  结论: [DecidableEq α] [有限类型 α] {f g : 置换 α}
  证明: by
  revert f
  refine
    cycle_induction_on (P := fun {g : Perm α} =>
      forall {f}, (f in cycleFactorsFinset g)
        -> cycleFactorsFinset (g * f⁻¹) = cycleFactorsFinset g \ {f}) _ ?_ ?_ ?_
  · simp
  · intro σ hσ f hf
    simp only [cycleFactorsFinset_eq_singleton_self_iff.mpr hσ, mem_singleton] at hf ⊢
    simp [hf]
  · intro σ τ hd _ hσ hτ f
    simp_rw [hd.cycleFactorsFinset_mul_eq_union, mem_union]
    -- if only `wlog` could work here...
    rintro (hf | hf)
    · rw [hd.commute.eq, union_comm, union_sdiff_distrib, sdiff_singleton_eq_erase,
        erase_eq_of_notMem, mul_assoc, Disjoint.cycleFactorsFinset_mul_eq_union, hσ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        rcases hd.symm x with hx | hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        notMem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem hf H))
    · rw [union_sdiff_distrib, sdiff_singleton_eq_erase, erase_eq_of_notMem, mul_assoc,
        Disjoint.cycleFactorsFinset_mul_eq_union, hτ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        rcases hd x with hx | hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        notMem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem H hf))

Depends on / 依赖: cycleFactorsFinset, cycleFactorsFinset_eq_singleton_self_iff, cycleFactorsFinset_eq_singleton_self_iff.mpr, cycleFactorsFinset_mul_eq_union, cycle_induction_on, hd.cycleFactorsFinset_mul_eq_union, mem_singleton, mem_union, revert, simp_rw
-/
theorem cycleFactorsFinset_mul_inv_mem_eq_sdiff [DecidableEq α] [Fintype α] {f g : Perm α}
    (h : f in cycleFactorsFinset g) : cycleFactorsFinset (g * f⁻¹) = cycleFactorsFinset g \ {f} := by
  revert f
  refine
    cycle_induction_on (P := fun {g : Perm α} =>
      forall {f}, (f in cycleFactorsFinset g)
        -> cycleFactorsFinset (g * f⁻¹) = cycleFactorsFinset g \ {f}) _ ?_ ?_ ?_
  · simp
  · intro σ hσ f hf
    simp only [cycleFactorsFinset_eq_singleton_self_iff.mpr hσ, mem_singleton] at hf ⊢
    simp [hf]
  · intro σ τ hd _ hσ hτ f
    simp_rw [hd.cycleFactorsFinset_mul_eq_union, mem_union]
    -- if only `wlog` could work here...
    rintro (hf | hf)
    · rw [hd.commute.eq, union_comm, union_sdiff_distrib, sdiff_singleton_eq_erase,
        erase_eq_of_notMem, mul_assoc, Disjoint.cycleFactorsFinset_mul_eq_union, hσ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        rcases hd.symm x with hx | hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        notMem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem hf H))
    · rw [union_sdiff_distrib, sdiff_singleton_eq_erase, erase_eq_of_notMem, mul_assoc,
        Disjoint.cycleFactorsFinset_mul_eq_union, hτ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        rcases hd x with hx | hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        notMem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem H hf))

/--
theorem `IsCycle.forall_commute_iff` / 定理 `IsCycle.forall_commute_iff`

English:
theorem IsCycle.forall_commute_iff
  given: [DecidableEq α] [Fintype α] (g z : Perm α)
  proof: by
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  exact IsCycle.commute_iff (mem_cycleFactorsFinset_iff.mp hc).1

中文:
定理 是环.对任意_commute_iff
  条件: [DecidableEq α] [有限类型 α] (g z : 置换 α)
  证明: by
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  exact IsCycle.commute_iff (mem_cycleFactorsFinset_iff.mp hc).1

Depends on / 依赖: IsCycle, IsCycle.commute_iff, commute_iff, forall_congr, imp_congr_right, mem_cycleFactorsFinset_iff, mem_cycleFactorsFinset_iff.mp
-/
theorem IsCycle.forall_commute_iff [DecidableEq α] [Fintype α] (g z : Perm α) :
    (forall c in g.cycleFactorsFinset, Commute z c) ↔
      forall c in g.cycleFactorsFinset,
      exists (hc : forall x : α, z x in c.support ↔ x in c.support),
        ofSubtype (subtypePerm z hc) in Subgroup.zpowers c := by
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  exact IsCycle.commute_iff (mem_cycleFactorsFinset_iff.mp hc).1

/--
theorem `subtypePerm_on_cycleFactorsFinset` / 定理 `subtypePerm_on_cycleFactorsFinset`

English:
theorem subtypePerm_on_cycleFactorsFinset
  statement: [DecidableEq α] [Fintype α]
  proof: by
  ext ⟨x, hx⟩
  simp only [subtypePerm_apply, Subtype.coe_mk, subtypePermOfSupport]
  exact ((mem_cycleFactorsFinset_iff.mp hc).2 x hx).symm

中文:
定理 subtypePerm_on_cycleFactorsFinset
  结论: [DecidableEq α] [有限类型 α]
  证明: by
  ext ⟨x, hx⟩
  simp only [subtypePerm_apply, Subtype.coe_mk, subtypePermOfSupport]
  exact ((mem_cycleFactorsFinset_iff.mp hc).2 x hx).symm

Depends on / 依赖: Subtype, Subtype.coe_mk, coe_mk, mem_cycleFactorsFinset_iff, mem_cycleFactorsFinset_iff.mp, subtypePermOfSupport, subtypePerm_apply
-/
theorem subtypePerm_on_cycleFactorsFinset [DecidableEq α] [Fintype α]
    {g c : Perm α} (hc : c in g.cycleFactorsFinset) :
    g.subtypePerm (mem_cycleFactorsFinset_support hc) = c.subtypePermOfSupport := by
  ext ⟨x, hx⟩
  simp only [subtypePerm_apply, Subtype.coe_mk, subtypePermOfSupport]
  exact ((mem_cycleFactorsFinset_iff.mp hc).2 x hx).symm

/--
theorem `commute_iff_of_mem_cycleFactorsFinset` / 定理 `commute_iff_of_mem_cycleFactorsFinset`

English:
theorem commute_iff_of_mem_cycleFactorsFinset
  statement: [DecidableEq α] [Fintype α] {g k c : Equiv.Perm α}
  proof: by
  rw [IsCycle.commute_iff' (mem_cycleFactorsFinset_iff.mp hc).1]
  apply exists_congr
  intro hc'
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro n
  rw [Equiv.Perm.subtypePerm_on_cycleFactorsFinset hc]

中文:
定理 commute_iff_of_mem_cycleFactorsFinset
  结论: [DecidableEq α] [有限类型 α] {g k c : 等价.置换 α}
  证明: by
  rw [IsCycle.commute_iff' (mem_cycleFactorsFinset_iff.mp hc).1]
  apply exists_congr
  intro hc'
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro n
  rw [Equiv.Perm.subtypePerm_on_cycleFactorsFinset hc]

Depends on / 依赖: Equiv.Perm.subtypePerm_on_cycleFactorsFinset, IsCycle, IsCycle.commute_iff, Subgroup, Subgroup.mem_zpowers_iff, commute_iff, exists_congr, mem_cycleFactorsFinset_iff, mem_cycleFactorsFinset_iff.mp, mem_zpowers_iff, subtypePerm_on_cycleFactorsFinset
-/
theorem commute_iff_of_mem_cycleFactorsFinset [DecidableEq α] [Fintype α] {g k c : Equiv.Perm α}
    (hc : c in g.cycleFactorsFinset) :
    Commute k c ↔
      exists hc' : forall x : α, k x in c.support ↔ x in c.support,
        k.subtypePerm hc' in Subgroup.zpowers
          (g.subtypePerm (mem_cycleFactorsFinset_support hc)) := by
  rw [IsCycle.commute_iff' (mem_cycleFactorsFinset_iff.mp hc).1]
  apply exists_congr
  intro hc'
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro n
  rw [Equiv.Perm.subtypePerm_on_cycleFactorsFinset hc]

end cycleFactors

end Perm

end Equiv
