/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Pointwise.Set.Lattice
public import Mathlib.Algebra.Group.Subgroup.MulOppositeLemmas
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Pointwise
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-! # Pointwise instances on `Subgroup` and `AddSubgroup`s

This file provides the actions

* `Subgroup.pointwiseMulAction`
* `AddSubgroup.pointwiseMulAction`

which matches the action of `Set.mulActionSet`.

These actions are available in the `Pointwise` locale.

## Implementation notes

The pointwise section of this file is almost identical to
the file `Mathlib/Algebra/Group/Submonoid/Pointwise.lean`.
Where possible, try to keep them in sync.
-/

@[expose] public section

assert_not_exists GroupWithZero

open Set
open scoped Pointwise

variable {α G A S : Type*}

@[to_additive (attr := simp, norm_cast)]
/--
theorem `inv_coe_set` / 定理 `inv_coe_set`

English:
theorem inv_coe_set
  given: [InvolutiveInv G] [SetLike S G] [InvMemClass S G] {H : S}
  statement: (H : Set G)⁻¹ = H
  proof: Set.ext fun _ => inv_mem_iff

@[to_additive (attr := simp)]

中文:
定理 inv_coe_set
  条件: [InvolutiveInv G] [集合状 S G] [InvMem类 S G] {H : S}
  结论: (H : 集合 G)⁻¹ = H
  证明: Set.ext fun _ => inv_mem_iff

@[to_additive (attr := simp)]

Depends on / 依赖: Set.ext, inv_mem_iff
-/
theorem inv_coe_set [InvolutiveInv G] [SetLike S G] [InvMemClass S G] {H : S} : (H : Set G)⁻¹ = H :=
  Set.ext fun _ => inv_mem_iff

@[to_additive (attr := simp)]
/--
lemma `smul_coe_set` / 引理 `smul_coe_set`

English:
lemma smul_coe_set
  given: [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G} (ha : a in s)
  proof: by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_left, ha]

@[norm_cast, to_additive]

中文:
引理 smul_coe_set
  条件: [群 G] [集合状 S G] [子群类 S G] {s : S} {a : G} (ha : a in s)
  证明: by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_left, ha]

@[norm_cast, to_additive]

Depends on / 依赖: Set.mem_smul_set_iff_inv_smul_mem, mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_left
-/
lemma smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G} (ha : a in s) :
    a • (s : Set G) = s := by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_left, ha]

@[norm_cast, to_additive]
/--
lemma `coe_set_eq_one` / 引理 `coe_set_eq_one`

English:
lemma coe_set_eq_one
  given: [Group G] {s : Subgroup G}
  statement: (s : Set G) = 1 ↔ s = ⊥
  proof: (SetLike.ext'_iff.trans (by rfl)).symm

@[to_additive (attr := simp)]

中文:
引理 coe_set_eq_one
  条件: [群 G] {s : 子群 G}
  结论: (s : 集合 G) = 1 ↔ s = ⊥
  证明: (SetLike.ext'_iff.trans (by rfl)).symm

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext, _iff, _iff.trans
-/
lemma coe_set_eq_one [Group G] {s : Subgroup G} : (s : Set G) = 1 ↔ s = ⊥ :=
  (SetLike.ext'_iff.trans (by rfl)).symm

@[to_additive (attr := simp)]
/--
lemma `op_smul_coe_set` / 引理 `op_smul_coe_set`

English:
lemma op_smul_coe_set
  given: [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G} (ha : a in s)
  proof: by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_right, ha]

@[to_additive (attr := simp, norm_cast)]

中文:
引理 op_smul_coe_set
  条件: [群 G] [集合状 S G] [子群类 S G] {s : S} {a : G} (ha : a in s)
  证明: by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_right, ha]

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Set.mem_smul_set_iff_inv_smul_mem, mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_right
-/
lemma op_smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G} (ha : a in s) :
    MulOpposite.op a • (s : Set G) = s := by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_right, ha]

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_div_coe` / 引理 `coe_div_coe`

English:
lemma coe_div_coe
  given: [SetLike S G] [DivisionMonoid G] [SubgroupClass S G] (H : S)
  proof: by simp [div_eq_mul_inv]

中文:
引理 coe_div_coe
  条件: [集合状 S G] [Division幺半群 G] [子群类 S G] (H : S)
  证明: by simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
lemma coe_div_coe [SetLike S G] [DivisionMonoid G] [SubgroupClass S G] (H : S) :
    H / H = (H : Set G) := by simp [div_eq_mul_inv]

variable [Group G] [AddGroup A] {s : Set G}

namespace Set

open Subgroup

@[to_additive (attr := simp)]
/--
lemma `mul_subgroupClosure` / 引理 `mul_subgroupClosure`

English:
lemma mul_subgroupClosure
  given: (hs : s.Nonempty)
  statement: s * closure s = closure s
  proof: by
  rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
  have h a (ha : a in s) : a • (closure s : Set G) = closure s :=
smul_coe_set subset_closure ha
  simp +contextual [h, hs]

中文:
引理 mul_subgroupClosure
  条件: (hs : s.非空)
  结论: s * closure s = closure s
  证明: by
  rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
  have h a (ha : a in s) : a • (closure s : Set G) = closure s :=
smul_coe_set subset_closure ha
  simp +contextual [h, hs]

Depends on / 依赖: Set.iUnion_smul_set, closure, contextual, iUnion_smul_set, smul_coe_set, smul_eq_mul, subset_closure
-/
lemma mul_subgroupClosure (hs : s.Nonempty) : s * closure s = closure s := by
  rw [← smul_eq_mul]; rw [← Set.iUnion_smul_set]
  have h a (ha : a in s) : a • (closure s : Set G) = closure s :=
smul_coe_set subset_closure ha
  simp +contextual [h, hs]

open scoped RightActions in
@[to_additive (attr := simp)]
/--
lemma `subgroupClosure_mul` / 引理 `subgroupClosure_mul`

English:
lemma subgroupClosure_mul
  given: (hs : s.Nonempty)
  statement: closure s * s = closure s
  proof: by
  rw [← Set.iUnion_op_smul_set]
  have h a (ha : a in s) : (closure s : Set G) <• a = closure s :=
op_smul_coe_set subset_closure ha
  simp +contextual [h, hs]

@[to_additive (attr := simp)]

中文:
引理 subgroupClosure_mul
  条件: (hs : s.非空)
  结论: closure s * s = closure s
  证明: by
  rw [← Set.iUnion_op_smul_set]
  have h a (ha : a in s) : (closure s : Set G) <• a = closure s :=
op_smul_coe_set subset_closure ha
  simp +contextual [h, hs]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.iUnion_op_smul_set, closure, contextual, iUnion_op_smul_set, op_smul_coe_set, subset_closure
-/
lemma subgroupClosure_mul (hs : s.Nonempty) : closure s * s = closure s := by
  rw [← Set.iUnion_op_smul_set]
  have h a (ha : a in s) : (closure s : Set G) <• a = closure s :=
op_smul_coe_set subset_closure ha
  simp +contextual [h, hs]

@[to_additive (attr := simp)]
/--
lemma `pow_mul_subgroupClosure` / 引理 `pow_mul_subgroupClosure`

English:
lemma pow_mul_subgroupClosure
  given: (hs : s.Nonempty)
  statement: forall n, s ^ n * closure s = closure s

中文:
引理 pow_mul_subgroupClosure
  条件: (hs : s.非空)
  结论: 对任意 n, s ^ n * closure s = closure s
-/
lemma pow_mul_subgroupClosure (hs : s.Nonempty) : forall n, s ^ n * closure s = closure s
  | 0 => by simp
  | n + 1 => by rw [pow_succ, mul_assoc, mul_subgroupClosure hs, pow_mul_subgroupClosure hs]

@[to_additive (attr := simp)]
/--
lemma `subgroupClosure_mul_pow` / 引理 `subgroupClosure_mul_pow`

English:
lemma subgroupClosure_mul_pow
  given: (hs : s.Nonempty)
  statement: forall n, closure s * s ^ n = closure s

中文:
引理 subgroupClosure_mul_pow
  条件: (hs : s.非空)
  结论: 对任意 n, closure s * s ^ n = closure s
-/
lemma subgroupClosure_mul_pow (hs : s.Nonempty) : forall n, closure s * s ^ n = closure s
  | 0 => by simp
  | n + 1 => by rw [pow_succ', ← mul_assoc, subgroupClosure_mul hs, subgroupClosure_mul_pow hs]

end Set

namespace Subgroup

@[to_additive (attr := simp)]
/--
theorem `inv_subset_closure` / 定理 `inv_subset_closure`

English:
theorem inv_subset_closure
  given: (S : Set G)
  statement: S⁻¹ subseteq closure S
  proof: fun s hs => by
  rw [SetLike.mem_coe]; rw [← Subgroup.inv_mem_iff]
  exact subset_closure (mem_inv.mp hs)

@[to_additive]

中文:
定理 inv_subset_closure
  条件: (S : 集合 G)
  结论: S⁻¹ subseteq closure S
  证明: fun s hs => by
  rw [SetLike.mem_coe]; rw [← Subgroup.inv_mem_iff]
  exact subset_closure (mem_inv.mp hs)

@[to_additive]

Depends on / 依赖: SetLike, SetLike.mem_coe, Subgroup, Subgroup.inv_mem_iff, inv_mem_iff, mem_coe, mem_inv, mem_inv.mp, subset_closure
-/
theorem inv_subset_closure (S : Set G) : S⁻¹ subseteq closure S := fun s hs => by
  rw [SetLike.mem_coe]; rw [← Subgroup.inv_mem_iff]
  exact subset_closure (mem_inv.mp hs)

@[to_additive]
/--
theorem `closure_toSubmonoid` / 定理 `closure_toSubmonoid`

English:
theorem closure_toSubmonoid
  given: (S : Set G)
  proof: by
  refine le_antisymm (fun x hx => ?_) (Submonoid.closure_le.2 ?_)
  · refine
      closure_induction
        (fun x hx => Submonoid.closure_mono subset_union_left (Submonoid.subset_closure hx))
        (Submonoid.one_mem _) (fun x y _ _ hx hy => Submonoid.mul_mem _ hx hy) (fun x _ hx => ?_) hx
    rwa [← Submonoid.mem_closure_inv, Set.union_inv, inv_inv, Set.union_comm]
  · simp only [true_and, coe_toSubmonoid, union_subset_iff, subset_closure, inv_subset_closure]

@[to_additive]

中文:
定理 closure_toSubmonoid
  条件: (S : 集合 G)
  证明: by
  refine le_antisymm (fun x hx => ?_) (Submonoid.closure_le.2 ?_)
  · refine
      closure_induction
        (fun x hx => Submonoid.closure_mono subset_union_left (Submonoid.subset_closure hx))
        (Submonoid.one_mem _) (fun x y _ _ hx hy => Submonoid.mul_mem _ hx hy) (fun x _ hx => ?_) hx
    rwa [← Submonoid.mem_closure_inv, Set.union_inv, inv_inv, Set.union_comm]
  · simp only [true_and, coe_toSubmonoid, union_subset_iff, subset_closure, inv_subset_closure]

@[to_additive]

Depends on / 依赖: Set.union_comm, Set.union_inv, Submonoid, Submonoid.closure_le, Submonoid.closure_mono, Submonoid.mem_closure_inv, Submonoid.mul_mem, Submonoid.one_mem, Submonoid.subset_closure, closure_induction, closure_le, closure_mono, coe_toSubmonoid, inv_inv, inv_subset_closure, le_antisymm, mem_closure_inv, mul_mem, one_mem, subset_closure
-/
theorem closure_toSubmonoid (S : Set G) :
    (closure S).toSubmonoid = Submonoid.closure (S union S⁻¹) := by
  refine le_antisymm (fun x hx => ?_) (Submonoid.closure_le.2 ?_)
  · refine
      closure_induction
        (fun x hx => Submonoid.closure_mono subset_union_left (Submonoid.subset_closure hx))
        (Submonoid.one_mem _) (fun x y _ _ hx hy => Submonoid.mul_mem _ hx hy) (fun x _ hx => ?_) hx
    rwa [← Submonoid.mem_closure_inv, Set.union_inv, inv_inv, Set.union_comm]
  · simp only [true_and, coe_toSubmonoid, union_subset_iff, subset_closure, inv_subset_closure]

@[to_additive]
/--
lemma `toSubmonoid_zpowers` / 引理 `toSubmonoid_zpowers`

English:
lemma toSubmonoid_zpowers
  given: (g : G)
  proof: by
  rw [zpowers_eq_closure]; rw [closure_toSubmonoid]; rw [Submonoid.closure_union]; rw [Submonoid.powers_eq_closure]; rw [Submonoid.powers_eq_closure]; rw [Set.inv_singleton]

@[to_additive]

中文:
引理 toSubmonoid_zpowers
  条件: (g : G)
  证明: by
  rw [zpowers_eq_closure]; rw [closure_toSubmonoid]; rw [Submonoid.closure_union]; rw [Submonoid.powers_eq_closure]; rw [Submonoid.powers_eq_closure]; rw [Set.inv_singleton]

@[to_additive]

Depends on / 依赖: Set.inv_singleton, Submonoid, Submonoid.closure_union, Submonoid.powers_eq_closure, closure_toSubmonoid, closure_union, inv_singleton, powers_eq_closure, zpowers_eq_closure
-/
lemma toSubmonoid_zpowers (g : G) :
    (Subgroup.zpowers g).toSubmonoid = Submonoid.powers g ⊔ Submonoid.powers g⁻¹ := by
  rw [zpowers_eq_closure]; rw [closure_toSubmonoid]; rw [Submonoid.closure_union]; rw [Submonoid.powers_eq_closure]; rw [Submonoid.powers_eq_closure]; rw [Set.inv_singleton]

@[to_additive]
/--
lemma `_root_.Submonoid.powers_le_zpowers` / 引理 `_root_.Submonoid.powers_le_zpowers`

English:
lemma _root_.Submonoid.powers_le_zpowers
  given: (g : G)
  proof: by
  rw [toSubmonoid_zpowers]
  exact le_sup_left

中文:
引理 _root_.子幺半群.powers_le_zpowers
  条件: (g : G)
  证明: by
  rw [toSubmonoid_zpowers]
  exact le_sup_left

Depends on / 依赖: le_sup_left, toSubmonoid_zpowers
-/
lemma _root_.Submonoid.powers_le_zpowers (g : G) :
    Submonoid.powers g <= (Subgroup.zpowers g).toSubmonoid := by
  rw [toSubmonoid_zpowers]
  exact le_sup_left

/-- For subgroups generated by a single element, see the simpler `zpow_induction_left`. -/
@[to_additive (attr := elab_as_elim)
  /-- For additive subgroups generated by a single element, see the simpler
  `zsmul_induction_left`. -/]
/--
theorem `closure_induction_left` / 定理 `closure_induction_left`

English:
theorem closure_induction_left
  statement: {p : (x : G) -> x in closure s -> Prop} (one : p 1 (one_mem _))
  proof: by
  revert h
  simp_rw [← mem_toSubmonoid, closure_toSubmonoid] at *
  intro h
  induction h using Submonoid.closure_induction_left with
  | one => exact one
  | mul_left x hx y hy ih =>
    cases hx with
    | inl hx => exact mul_left _ hx _ hy ih
    | inr hx => simpa only [inv_inv] using inv_mul_cancel _ hx _ hy ih

中文:
定理 closure_induction_left
  结论: {p : (x : G) -> x in closure s -> 命题} (one : p 1 (one_mem _))
  证明: by
  revert h
  simp_rw [← mem_toSubmonoid, closure_toSubmonoid] at *
  intro h
  induction h using Submonoid.closure_induction_left with
  | one => exact one
  | mul_left x hx y hy ih =>
    cases hx with
    | inl hx => exact mul_left _ hx _ hy ih
    | inr hx => simpa only [inv_inv] using inv_mul_cancel _ hx _ hy ih

Depends on / 依赖: Submonoid, Submonoid.closure_induction_left, closure_induction_left, closure_toSubmonoid, inv_inv, inv_mul_cancel, mem_toSubmonoid, mul_left, revert, simp_rw
-/
theorem closure_induction_left {p : (x : G) -> x in closure s -> Prop} (one : p 1 (one_mem _))
    (mul_left : forall x (hx : x in s), forall (y) hy, p y hy -> p (x * y) (mul_mem (subset_closure hx) hy))
    (inv_mul_cancel : forall x (hx : x in s), forall (y) hy, p y hy ->
      p (x⁻¹ * y) (mul_mem (inv_mem (subset_closure hx)) hy))
    {x : G} (h : x in closure s) : p x h := by
  revert h
  simp_rw [← mem_toSubmonoid, closure_toSubmonoid] at *
  intro h
  induction h using Submonoid.closure_induction_left with
  | one => exact one
  | mul_left x hx y hy ih =>
    cases hx with
    | inl hx => exact mul_left _ hx _ hy ih
    | inr hx => simpa only [inv_inv] using inv_mul_cancel _ hx _ hy ih

/-- For subgroups generated by a single element, see the simpler `zpow_induction_right`. -/
@[to_additive (attr := elab_as_elim)
  /-- For additive subgroups generated by a single element, see the simpler
  `zsmul_induction_right`. -/]
/--
theorem `closure_induction_right` / 定理 `closure_induction_right`

English:
theorem closure_induction_right
  statement: {p : (x : G) -> x in closure s -> Prop} (one : p 1 (one_mem _))
  proof: closure_induction_left (s := MulOpposite.unop ⁻¹' s)
    (p := fun m hm => p m.unop <| by rwa [← op_closure] at hm)
    one
    (fun _x hx _y _ => mul_right _ _ _ hx)
    (fun _x hx _y _ => mul_inv_cancel _ _ _ hx)
    (by rwa [← op_closure])

@[to_additive (attr := simp)]

中文:
定理 closure_induction_right
  结论: {p : (x : G) -> x in closure s -> 命题} (one : p 1 (one_mem _))
  证明: closure_induction_left (s := MulOpposite.unop ⁻¹' s)
    (p := fun m hm => p m.unop <| by rwa [← op_closure] at hm)
    one
    (fun _x hx _y _ => mul_right _ _ _ hx)
    (fun _x hx _y _ => mul_inv_cancel _ _ _ hx)
    (by rwa [← op_closure])

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.unop, closure_induction_left, m.unop, mul_inv_cancel, mul_right, op_closure
-/
theorem closure_induction_right {p : (x : G) -> x in closure s -> Prop} (one : p 1 (one_mem _))
    (mul_right : forall (x) hx, forall y (hy : y in s), p x hx -> p (x * y) (mul_mem hx (subset_closure hy)))
    (mul_inv_cancel : forall (x) hx, forall y (hy : y in s), p x hx ->
      p (x * y⁻¹) (mul_mem hx (inv_mem (subset_closure hy))))
    {x : G} (h : x in closure s) : p x h :=
  closure_induction_left (s := MulOpposite.unop ⁻¹' s)
    (p := fun m hm => p m.unop <| by rwa [← op_closure] at hm)
    one
    (fun _x hx _y _ => mul_right _ _ _ hx)
    (fun _x hx _y _ => mul_inv_cancel _ _ _ hx)
    (by rwa [← op_closure])

@[to_additive (attr := simp)]
/--
theorem `closure_inv` / 定理 `closure_inv`

English:
theorem closure_inv
  given: (s : Set G)
  statement: closure s⁻¹ = closure s
  proof: by
  simp only [← toSubmonoid_inj, closure_toSubmonoid, inv_inv, union_comm]

@[to_additive (attr := simp)]

中文:
定理 closure_inv
  条件: (s : 集合 G)
  结论: closure s⁻¹ = closure s
  证明: by
  simp only [← toSubmonoid_inj, closure_toSubmonoid, inv_inv, union_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: closure_toSubmonoid, inv_inv, toSubmonoid_inj, union_comm
-/
theorem closure_inv (s : Set G) : closure s⁻¹ = closure s := by
  simp only [← toSubmonoid_inj, closure_toSubmonoid, inv_inv, union_comm]

@[to_additive (attr := simp)]
/--
lemma `closure_singleton_inv` / 引理 `closure_singleton_inv`

English:
lemma closure_singleton_inv
  given: (x : G)
  statement: closure {x⁻¹} = closure {x}
  proof: by
  rw [← Set.inv_singleton]; rw [closure_inv]

中文:
引理 closure_singleton_inv
  条件: (x : G)
  结论: closure {x⁻¹} = closure {x}
  证明: by
  rw [← Set.inv_singleton]; rw [closure_inv]

Depends on / 依赖: Set.inv_singleton, closure_inv, inv_singleton
-/
lemma closure_singleton_inv (x : G) : closure {x⁻¹} = closure {x} := by
  rw [← Set.inv_singleton]; rw [closure_inv]

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of
`k` and their inverse, and is preserved under multiplication, then `p` holds for all elements of
the closure of `k`. -/
@[to_additive (attr := elab_as_elim)
  /-- An induction principle for additive closure membership. If `p` holds for `0` and all
  elements of `k` and their negation, and is preserved under addition, then `p` holds for all
  elements of the additive closure of `k`. -/]
/--
theorem `closure_induction''` / 定理 `closure_induction''`

English:
theorem closure_induction''
  statement: {p : (g : G) -> g in closure s -> Prop}
  proof: closure_induction_left one (fun x hx y _ hy => mul x y _ _ (mem x hx) hy)
    (fun x hx y _ => mul x⁻¹ y _ _ <| inv_mem x hx) h

中文:
定理 closure_induction''
  结论: {p : (g : G) -> g in closure s -> 命题}
  证明: closure_induction_left one (fun x hx y _ hy => mul x y _ _ (mem x hx) hy)
    (fun x hx y _ => mul x⁻¹ y _ _ <| inv_mem x hx) h

Depends on / 依赖: closure_induction_left, inv_mem
-/
theorem closure_induction'' {p : (g : G) -> g in closure s -> Prop}
    (mem : forall x (hx : x in s), p x (subset_closure hx))
    (inv_mem : forall x (hx : x in s), p x⁻¹ (inv_mem (subset_closure hx)))
    (one : p 1 (one_mem _))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    {x} (h : x in closure s) : p x h :=
  closure_induction_left one (fun x hx y _ hy => mul x y _ _ (mem x hx) hy)
    (fun x hx y _ => mul x⁻¹ y _ _ <| inv_mem x hx) h

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `1` and all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[to_additive (attr := elab_as_elim) /-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `0` and all elements of `S i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `S`. -/]
/--
theorem `iSup_induction` / 定理 `iSup_induction`

English:
theorem iSup_induction
  statement: {ι : Sort*} (S : ι -> Subgroup G) {C : G -> Prop} {x : G} (hx : x in ⨆ i, S i)
  proof: by
  rw [iSup_eq_closure] at hx
  induction hx using closure_induction'' with
  | one => exact one
  | mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem _ _ hi
  | inv_mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem _ _ (inv_mem hi)
  | mul x y _ _ ihx ihy => exact mul x y ihx ihy

中文:
定理 iSup_induction
  结论: {ι : 类型层*} (S : ι -> 子群 G) {C : G -> 命题} {x : G} (hx : x in ⨆ i, S i)
  证明: by
  rw [iSup_eq_closure] at hx
  induction hx using closure_induction'' with
  | one => exact one
  | mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem _ _ hi
  | inv_mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem _ _ (inv_mem hi)
  | mul x y _ _ ihx ihy => exact mul x y ihx ihy

Depends on / 依赖: Set.mem_iUnion.mp, closure_induction, iSup_eq_closure, inv_mem, mem_iUnion
-/
theorem iSup_induction {ι : Sort*} (S : ι -> Subgroup G) {C : G -> Prop} {x : G} (hx : x in ⨆ i, S i)
    (mem : forall (i), forall x in S i, C x) (one : C 1) (mul : forall x y, C x -> C y -> C (x * y)) : C x := by
  rw [iSup_eq_closure] at hx
  induction hx using closure_induction'' with
  | one => exact one
  | mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem _ _ hi
  | inv_mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem _ _ (inv_mem hi)
  | mul x y _ _ ihx ihy => exact mul x y ihx ihy

/-- A dependent version of `Subgroup.iSup_induction`. -/
@[to_additive (attr := elab_as_elim) /-- A dependent version of `AddSubgroup.iSup_induction`. -/]
/--
theorem `iSup_induction'` / 定理 `iSup_induction'`

English:
theorem iSup_induction'
  statement: {ι : Sort*} (S : ι -> Subgroup G) {C : forall x, (x in ⨆ i, S i) -> Prop}
  proof: by
  suffices exists h, C x h from this.snd
  refine iSup_induction S (C := fun x => exists h, C x h) hx (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, hp i _ hx⟩
  · exact ⟨_, h1⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, hmul _ _ _ _ Cx Cy⟩

@[to_additive (attr := simp)]

中文:
定理 iSup_induction'
  结论: {ι : 类型层*} (S : ι -> 子群 G) {C : 对任意 x, (x in ⨆ i, S i) -> 命题}
  证明: by
  suffices exists h, C x h from this.snd
  refine iSup_induction S (C := fun x => exists h, C x h) hx (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, hp i _ hx⟩
  · exact ⟨_, h1⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, hmul _ _ _ _ Cx Cy⟩

@[to_additive (attr := simp)]

Depends on / 依赖: iSup_induction, this.snd
-/
theorem iSup_induction' {ι : Sort*} (S : ι -> Subgroup G) {C : forall x, (x in ⨆ i, S i) -> Prop}
    (hp : forall (i), forall x (hx : x in S i), C x (mem_iSup_of_mem i hx)) (h1 : C 1 (one_mem _))
    (hmul : forall x y hx hy, C x hx -> C y hy -> C (x * y) (mul_mem ‹_› ‹_›)) {x : G}
    (hx : x in ⨆ i, S i) : C x hx := by
  suffices exists h, C x h from this.snd
  refine iSup_induction S (C := fun x => exists h, C x h) hx (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, hp i _ hx⟩
  · exact ⟨_, h1⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, hmul _ _ _ _ Cx Cy⟩

@[to_additive (attr := simp)]
/--
theorem `mul_subset` / 定理 `mul_subset`

English:
theorem mul_subset
  given: {t : Set G} {H : Subgroup G} (hs : s subseteq H) (ht : t subseteq H)
  statement: s * t subseteq H
  proof: Submonoid.mul_subset hs ht

@[to_additive (attr := simp)]

中文:
定理 mul_subset
  条件: {t : 集合 G} {H : 子群 G} (hs : s subseteq H) (ht : t subseteq H)
  结论: s * t subseteq H
  证明: Submonoid.mul_subset hs ht

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.mul_subset, mul_subset
-/
theorem mul_subset {t : Set G} {H : Subgroup G} (hs : s subseteq H) (ht : t subseteq H) : s * t subseteq H :=
  Submonoid.mul_subset hs ht

@[to_additive (attr := simp)]
/--
lemma `pow_subset` / 引理 `pow_subset`

English:
lemma pow_subset
  given: {H : Subgroup G} {n : Nat} (hs : s subseteq H)
  statement: s ^ n subseteq H
  proof: by
  induction n <;> simp [pow_succ, *]

@[to_additive]

中文:
引理 pow_subset
  条件: {H : 子群 G} {n : 自然数} (hs : s subseteq H)
  结论: s ^ n subseteq H
  证明: by
  induction n <;> simp [pow_succ, *]

@[to_additive]

Depends on / 依赖: pow_succ
-/
lemma pow_subset {H : Subgroup G} {n : Nat} (hs : s subseteq H) : s ^ n subseteq H := by
  induction n <;> simp [pow_succ, *]

@[to_additive]
/--
theorem `closure_mul_le` / 定理 `closure_mul_le`

English:
theorem closure_mul_le
  given: (S T : Set G)
  statement: closure (S * T) <= closure S ⊔ closure T
  proof: sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)

@[to_additive]

中文:
定理 closure_mul_le
  条件: (S T : 集合 G)
  结论: closure (S * T) <= closure S ⊔ closure T
  证明: sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)

@[to_additive]

Depends on / 依赖: SetLike, SetLike.le_def.mp, closure, le_def, le_sup_left, le_sup_right, mul_mem, sInf_le, subset_closure
-/
theorem closure_mul_le (S T : Set G) : closure (S * T) <= closure S ⊔ closure T :=
  sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)

@[to_additive]
/--
lemma `closure_pow_le` / 引理 `closure_pow_le`

English:
lemma closure_pow_le
  given: {n : Nat}
  statement: closure (s ^ n) <= closure s
  proof: by simp

@[to_additive]

中文:
引理 closure_pow_le
  条件: {n : 自然数}
  结论: closure (s ^ n) <= closure s
  证明: by simp

@[to_additive]
-/
lemma closure_pow_le {n : Nat} : closure (s ^ n) <= closure s := by simp

@[to_additive]
/--
lemma `closure_pow_anti` / 引理 `closure_pow_anti`

English:
lemma closure_pow_anti
  given: {m n : Nat} (hmn : m ∣ n)
  statement: closure (s ^ n) <= closure (s ^ m)
  proof: by
  obtain ⟨k, rfl⟩ := hmn
  simp [pow_mul]

@[to_additive]

中文:
引理 closure_pow_anti
  条件: {m n : 自然数} (hmn : m ∣ n)
  结论: closure (s ^ n) <= closure (s ^ m)
  证明: by
  obtain ⟨k, rfl⟩ := hmn
  simp [pow_mul]

@[to_additive]

Depends on / 依赖: pow_mul
-/
lemma closure_pow_anti {m n : Nat} (hmn : m ∣ n) : closure (s ^ n) <= closure (s ^ m) := by
  obtain ⟨k, rfl⟩ := hmn
  simp [pow_mul]

@[to_additive]
/--
lemma `closure_pow` / 引理 `closure_pow`

English:
lemma closure_pow
  given: {n : Nat} (hs : 1 in s) (hn : n != 0)
  statement: closure (s ^ n) = closure s
  proof: closure_pow_le.antisymm by grw [← subset_pow hs hn]

@[to_additive]

中文:
引理 closure_pow
  条件: {n : 自然数} (hs : 1 in s) (hn : n != 0)
  结论: closure (s ^ n) = closure s
  证明: closure_pow_le.antisymm by grw [← subset_pow hs hn]

@[to_additive]

Depends on / 依赖: antisymm, closure_pow_le, closure_pow_le.antisymm, subset_pow
-/
lemma closure_pow {n : Nat} (hs : 1 in s) (hn : n != 0) : closure (s ^ n) = closure s :=
closure_pow_le.antisymm by grw [← subset_pow hs hn]

@[to_additive]
/--
theorem `sup_eq_closure_mul` / 定理 `sup_eq_closure_mul`

English:
theorem sup_eq_closure_mul
  given: (H K : Subgroup G)
  statement: H ⊔ K = closure ((H : Set G) * (K : Set G))
  proof: le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

@[to_additive]

中文:
定理 sup_eq_closure_mul
  条件: (H K : 子群 G)
  结论: H ⊔ K = closure ((H : 集合 G) * (K : 集合 G))
  证明: le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

@[to_additive]

Depends on / 依赖: H.one_mem, K.one_mem, closure_eq, closure_mul_le, le_antisymm, mul_one, one_mem, one_mul, subset_closure, sup_le
-/
theorem sup_eq_closure_mul (H K : Subgroup G) : H ⊔ K = closure ((H : Set G) * (K : Set G)) :=
  le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

@[to_additive]
/--
theorem `set_mul_normalizer_comm` / 定理 `set_mul_normalizer_comm`

English:
theorem set_mul_normalizer_comm
  given: (S : Set G) (N : Subgroup G) (hLE : S subseteq normalizer (N : Set G))
  proof: by
  rw [← iUnion_mul_left_image]; rw [← iUnion_mul_right_image]
  simp only [image_mul_left, image_mul_right, Set.preimage]
  congr! 5 with s hs x
  exact (mem_normalizer_iff'.mp (inv_mem (hLE hs)) x).symm

@[to_additive]

中文:
定理 set_mul_normalizer_comm
  条件: (S : 集合 G) (N : 子群 G) (hLE : S subseteq normalizer (N : 集合 G))
  证明: by
  rw [← iUnion_mul_left_image]; rw [← iUnion_mul_right_image]
  simp only [image_mul_left, image_mul_right, Set.preimage]
  congr! 5 with s hs x
  exact (mem_normalizer_iff'.mp (inv_mem (hLE hs)) x).symm

@[to_additive]

Depends on / 依赖: Set.preimage, iUnion_mul_left_image, iUnion_mul_right_image, image_mul_left, image_mul_right, inv_mem, mem_normalizer_iff, preimage
-/
theorem set_mul_normalizer_comm (S : Set G) (N : Subgroup G) (hLE : S subseteq normalizer (N : Set G)) :
    S * N = N * S := by
  rw [← iUnion_mul_left_image]; rw [← iUnion_mul_right_image]
  simp only [image_mul_left, image_mul_right, Set.preimage]
  congr! 5 with s hs x
  exact (mem_normalizer_iff'.mp (inv_mem (hLE hs)) x).symm

@[to_additive]
/--
theorem `set_mul_normal_comm` / 定理 `set_mul_normal_comm`

English:
theorem set_mul_normal_comm
  given: (S : Set G) (N : Subgroup G) [hN : N.Normal]
  proof: set_mul_normalizer_comm S N subset_normalizer_of_normal

中文:
定理 set_mul_normal_comm
  条件: (S : 集合 G) (N : 子群 G) [hN : N.正规]
  证明: set_mul_normalizer_comm S N subset_normalizer_of_normal

Depends on / 依赖: set_mul_normalizer_comm, subset_normalizer_of_normal
-/
theorem set_mul_normal_comm (S : Set G) (N : Subgroup G) [hN : N.Normal] :
    S * (N : Set G) = (N : Set G) * S := set_mul_normalizer_comm S N subset_normalizer_of_normal

/-- The carrier of `H ⊔ N` is just `↑H * ↑N` (pointwise set product)
when `H` is a subgroup of the normalizer of `N` in `G`. -/
@[to_additive /-- The carrier of `H ⊔ N` is just `↑H + ↑N` (pointwise set addition)
when `H` is a subgroup of the normalizer of `N` in `G`. -/]
/--
theorem `coe_mul_of_left_le_normalizer_right` / 定理 `coe_mul_of_left_le_normalizer_right`

English:
theorem coe_mul_of_left_le_normalizer_right
  given: (H N : Subgroup G) (hLE : H <= normalizer N)
  proof: by
  rw [sup_eq_closure_mul]
  refine Set.Subset.antisymm (fun x hx => ?_) subset_closure
  induction hx using closure_induction'' with
  | one => exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  | mem _ hx => exact hx
  | inv_mem x hx =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    simpa only [mul_inv_rev, mul_assoc, inv_inv, inv_mul_cancel_left]
      using mul_mem_mul (inv_mem hx) ((mem_normalizer_iff.mp (hLE hx) y⁻¹).mp (inv_mem hy))
  | mul x' x' _ _ hx hx' =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    obtain ⟨x', hx', y', hy', rfl⟩ := hx'
    refine ⟨x * x', mul_mem hx hx', x'⁻¹ * y * x' * y', mul_mem ?_ hy', ?_⟩
    · exact (mem_normalizer_iff''.mp (hLE hx') y).mp hy
    · simp only [mul_assoc, mul_inv_cancel_left]

中文:
定理 coe_mul_of_left_le_normalizer_right
  条件: (H N : 子群 G) (hLE : H <= normalizer N)
  证明: by
  rw [sup_eq_closure_mul]
  refine Set.Subset.antisymm (fun x hx => ?_) subset_closure
  induction hx using closure_induction'' with
  | one => exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  | mem _ hx => exact hx
  | inv_mem x hx =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    simpa only [mul_inv_rev, mul_assoc, inv_inv, inv_mul_cancel_left]
      using mul_mem_mul (inv_mem hx) ((mem_normalizer_iff.mp (hLE hx) y⁻¹).mp (inv_mem hy))
  | mul x' x' _ _ hx hx' =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    obtain ⟨x', hx', y', hy', rfl⟩ := hx'
    refine ⟨x * x', mul_mem hx hx', x'⁻¹ * y * x' * y', mul_mem ?_ hy', ?_⟩
    · exact (mem_normalizer_iff''.mp (hLE hx') y).mp hy
    · simp only [mul_assoc, mul_inv_cancel_left]

Depends on / 依赖: Set.Subset.antisymm, Subset, antisymm, closure_induction, inv_inv, inv_mem, inv_mul_cancel_left, mem_normalizer_iff, mem_normalizer_iff.mp, mul_assoc, mul_inv_rev, mul_mem_mul, mul_one, one_mem, subset_closure, sup_eq_closure_mul
-/
theorem coe_mul_of_left_le_normalizer_right (H N : Subgroup G) (hLE : H <= normalizer N) :
    (↑(H ⊔ N) : Set G) = H * N := by
  rw [sup_eq_closure_mul]
  refine Set.Subset.antisymm (fun x hx => ?_) subset_closure
  induction hx using closure_induction'' with
  | one => exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  | mem _ hx => exact hx
  | inv_mem x hx =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    simpa only [mul_inv_rev, mul_assoc, inv_inv, inv_mul_cancel_left]
      using mul_mem_mul (inv_mem hx) ((mem_normalizer_iff.mp (hLE hx) y⁻¹).mp (inv_mem hy))
  | mul x' x' _ _ hx hx' =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    obtain ⟨x', hx', y', hy', rfl⟩ := hx'
    refine ⟨x * x', mul_mem hx hx', x'⁻¹ * y * x' * y', mul_mem ?_ hy', ?_⟩
    · exact (mem_normalizer_iff''.mp (hLE hx') y).mp hy
    · simp only [mul_assoc, mul_inv_cancel_left]

/-- The carrier of `N ⊔ H` is just `↑N * ↑H` (pointwise set product) when
`H` is a subgroup of the normalizer of `N` in `G`. -/
@[to_additive /-- The carrier of `N ⊔ H` is just `↑N + ↑H` (pointwise set addition)
when `H` is a subgroup of the normalizer of `N` in `G`. -/]
/--
theorem `coe_mul_of_right_le_normalizer_left` / 定理 `coe_mul_of_right_le_normalizer_left`

English:
theorem coe_mul_of_right_le_normalizer_left
  given: (N H : Subgroup G) (hLE : H <= normalizer N)
  proof: by
  rw [← set_mul_normalizer_comm _ _ hLE]; rw [sup_comm]; rw [coe_mul_of_left_le_normalizer_right _ _ hLE]

中文:
定理 coe_mul_of_right_le_normalizer_left
  条件: (N H : 子群 G) (hLE : H <= normalizer N)
  证明: by
  rw [← set_mul_normalizer_comm _ _ hLE]; rw [sup_comm]; rw [coe_mul_of_left_le_normalizer_right _ _ hLE]

Depends on / 依赖: coe_mul_of_left_le_normalizer_right, set_mul_normalizer_comm, sup_comm
-/
theorem coe_mul_of_right_le_normalizer_left (N H : Subgroup G) (hLE : H <= normalizer N) :
    (↑(N ⊔ H) : Set G) = N * H := by
  rw [← set_mul_normalizer_comm _ _ hLE]; rw [sup_comm]; rw [coe_mul_of_left_le_normalizer_right _ _ hLE]

/-- The carrier of `H ⊔ N` is just `↑H * ↑N` (pointwise set product) when `N` is normal. -/
@[to_additive /-- The carrier of `H ⊔ N` is just `↑H + ↑N` (pointwise set addition)
when `N` is normal. -/]
/--
theorem `mul_normal` / 定理 `mul_normal`

English:
theorem mul_normal
  given: (H N : Subgroup G) [hN : N.Normal]
  statement: (↑(H ⊔ N) : Set G) = H * N
  proof: coe_mul_of_left_le_normalizer_right H N le_normalizer_of_normal

中文:
定理 mul_normal
  条件: (H N : 子群 G) [hN : N.正规]
  结论: (↑(H ⊔ N) : 集合 G) = H * N
  证明: coe_mul_of_left_le_normalizer_right H N le_normalizer_of_normal

Depends on / 依赖: coe_mul_of_left_le_normalizer_right, le_normalizer_of_normal
-/
theorem mul_normal (H N : Subgroup G) [hN : N.Normal] : (↑(H ⊔ N) : Set G) = H * N :=
  coe_mul_of_left_le_normalizer_right H N le_normalizer_of_normal

/-- The carrier of `N ⊔ H` is just `↑N * ↑H` (pointwise set product) when `N` is normal. -/
@[to_additive /-- The carrier of `N ⊔ H` is just `↑N + ↑H` (pointwise set addition)
when `N` is normal. -/]
/--
theorem `normal_mul` / 定理 `normal_mul`

English:
theorem normal_mul
  given: (N H : Subgroup G) [N.Normal]
  statement: (↑(N ⊔ H) : Set G) = N * H
  proof: coe_mul_of_right_le_normalizer_left N H le_normalizer_of_normal

@[to_additive]

中文:
定理 normal_mul
  条件: (N H : 子群 G) [N.正规]
  结论: (↑(N ⊔ H) : 集合 G) = N * H
  证明: coe_mul_of_right_le_normalizer_left N H le_normalizer_of_normal

@[to_additive]

Depends on / 依赖: coe_mul_of_right_le_normalizer_left, le_normalizer_of_normal
-/
theorem normal_mul (N H : Subgroup G) [N.Normal] : (↑(N ⊔ H) : Set G) = N * H :=
  coe_mul_of_right_le_normalizer_left N H le_normalizer_of_normal

@[to_additive]
/--
theorem `mul_inf_assoc` / 定理 `mul_inf_assoc`

English:
theorem mul_inf_assoc
  given: (A B C : Subgroup G) (h : A <= C)
  proof: by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, z, ⟨hzB, hzC⟩, rfl⟩
    refine ⟨?_, mul_mem (h hy) hzC⟩
    exact ⟨y, hy, z, hzB, rfl⟩
  rintro ⟨⟨y, hy, z, hz, rfl⟩, hyz⟩
  refine ⟨y, hy, z, ⟨hz, ?_⟩, rfl⟩
  suffices y⁻¹ * (y * z) in C by simpa
  exact mul_mem (inv_mem (h hy)) hyz

@[to_additive]

中文:
定理 mul_inf_assoc
  条件: (A B C : 子群 G) (h : A <= C)
  证明: by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, z, ⟨hzB, hzC⟩, rfl⟩
    refine ⟨?_, mul_mem (h hy) hzC⟩
    exact ⟨y, hy, z, hzB, rfl⟩
  rintro ⟨⟨y, hy, z, hz, rfl⟩, hyz⟩
  refine ⟨y, hy, z, ⟨hz, ?_⟩, rfl⟩
  suffices y⁻¹ * (y * z) in C by simpa
  exact mul_mem (inv_mem (h hy)) hyz

@[to_additive]

Depends on / 依赖: Set.mem_inter_iff, Set.mem_mul, coe_inf, inv_mem, mem_inter_iff, mem_mul, mul_mem
-/
theorem mul_inf_assoc (A B C : Subgroup G) (h : A <= C) :
    (A : Set G) * ↑(B ⊓ C) = (A : Set G) * (B : Set G) inter C := by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, z, ⟨hzB, hzC⟩, rfl⟩
    refine ⟨?_, mul_mem (h hy) hzC⟩
    exact ⟨y, hy, z, hzB, rfl⟩
  rintro ⟨⟨y, hy, z, hz, rfl⟩, hyz⟩
  refine ⟨y, hy, z, ⟨hz, ?_⟩, rfl⟩
  suffices y⁻¹ * (y * z) in C by simpa
  exact mul_mem (inv_mem (h hy)) hyz

@[to_additive]
/--
theorem `inf_mul_assoc` / 定理 `inf_mul_assoc`

English:
theorem inf_mul_assoc
  given: (A B C : Subgroup G) (h : C <= A)
  proof: by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, z, hz, rfl⟩
    refine ⟨A.mul_mem hyA (h hz), ?_⟩
    exact ⟨y, hyB, z, hz, rfl⟩
  rintro ⟨hyz, y, hy, z, hz, rfl⟩
  refine ⟨y, ⟨?_, hy⟩, z, hz, rfl⟩
  suffices y * z * z⁻¹ in A by simpa
  exact mul_mem hyz (inv_mem (h hz))

@[to_additive]

中文:
定理 inf_mul_assoc
  条件: (A B C : 子群 G) (h : C <= A)
  证明: by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, z, hz, rfl⟩
    refine ⟨A.mul_mem hyA (h hz), ?_⟩
    exact ⟨y, hyB, z, hz, rfl⟩
  rintro ⟨hyz, y, hy, z, hz, rfl⟩
  refine ⟨y, ⟨?_, hy⟩, z, hz, rfl⟩
  suffices y * z * z⁻¹ in A by simpa
  exact mul_mem hyz (inv_mem (h hz))

@[to_additive]

Depends on / 依赖: A.mul_mem, Set.mem_inter_iff, Set.mem_mul, coe_inf, inv_mem, mem_inter_iff, mem_mul, mul_mem
-/
theorem inf_mul_assoc (A B C : Subgroup G) (h : C <= A) :
    ((A ⊓ B : Subgroup G) : Set G) * C = (A : Set G) inter (↑B * ↑C) := by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, z, hz, rfl⟩
    refine ⟨A.mul_mem hyA (h hz), ?_⟩
    exact ⟨y, hyB, z, hz, rfl⟩
  rintro ⟨hyz, y, hy, z, hz, rfl⟩
  refine ⟨y, ⟨?_, hy⟩, z, hz, rfl⟩
  suffices y * z * z⁻¹ in A by simpa
  exact mul_mem hyz (inv_mem (h hz))

@[to_additive]
/--
lemma `normalizer_inf_normalizer_le_normalizer_sup` / 引理 `normalizer_inf_normalizer_le_normalizer_sup`

English:
lemma normalizer_inf_normalizer_le_normalizer_sup
  given: (H K : Subgroup G)
  proof: by
  intro g hg
  simp_rw [mem_inf, mem_normalizer_iff_map_conj_eq, map_sup, hg.1, hg.2] at hg ⊢

@[to_additive]

中文:
引理 normalizer_inf_normalizer_le_normalizer_sup
  条件: (H K : 子群 G)
  证明: by
  intro g hg
  simp_rw [mem_inf, mem_normalizer_iff_map_conj_eq, map_sup, hg.1, hg.2] at hg ⊢

@[to_additive]

Depends on / 依赖: map_sup, mem_inf, mem_normalizer_iff_map_conj_eq, simp_rw
-/
lemma normalizer_inf_normalizer_le_normalizer_sup (H K : Subgroup G) :
    normalizer H ⊓ normalizer K <= normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  intro g hg
  simp_rw [mem_inf, mem_normalizer_iff_map_conj_eq, map_sup, hg.1, hg.2] at hg ⊢

@[to_additive]
/--
theorem `iInf_normalizer_le_normalizer_iSup` / 定理 `iInf_normalizer_le_normalizer_iSup`

English:
theorem iInf_normalizer_le_normalizer_iSup
  given: {ι : Sort*} (H : ι -> Subgroup G)
  proof: by
  intro g hg
  simp_rw [mem_iInf, mem_normalizer_iff_map_conj_eq, map_iSup, hg] at hg ⊢

@[to_additive]

中文:
定理 iInf_normalizer_le_normalizer_iSup
  条件: {ι : 类型层*} (H : ι -> 子群 G)
  证明: by
  intro g hg
  simp_rw [mem_iInf, mem_normalizer_iff_map_conj_eq, map_iSup, hg] at hg ⊢

@[to_additive]

Depends on / 依赖: map_iSup, mem_iInf, mem_normalizer_iff_map_conj_eq, simp_rw
-/
theorem iInf_normalizer_le_normalizer_iSup {ι : Sort*} (H : ι -> Subgroup G) :
    ⨅ i, normalizer (H i) <= normalizer ((⨆ i, H i : Subgroup G) : Set G) := by
  intro g hg
  simp_rw [mem_iInf, mem_normalizer_iff_map_conj_eq, map_iSup, hg] at hg ⊢

@[to_additive]
/--
lemma `conj_mem_sup_of_mem_inf_normalizer_of_mem_inf` / 引理 `conj_mem_sup_of_mem_inf_normalizer_of_mem_inf`

English:
lemma conj_mem_sup_of_mem_inf_normalizer_of_mem_inf
  proof: (normalizer_inf_normalizer_le_normalizer_sup H K hs g).mp hg

@[to_additive]

中文:
引理 conj_mem_sup_of_mem_inf_normalizer_of_mem_inf
  证明: (normalizer_inf_normalizer_le_normalizer_sup H K hs g).mp hg

@[to_additive]

Depends on / 依赖: normalizer_inf_normalizer_le_normalizer_sup
-/
lemma conj_mem_sup_of_mem_inf_normalizer_of_mem_inf
    {H K : Subgroup G} {s : G} (hs : s in normalizer H ⊓ normalizer K) (g : G) (hg : g in H ⊔ K) :
    s * g * s⁻¹ in H ⊔ K :=
  (normalizer_inf_normalizer_le_normalizer_sup H K hs g).mp hg

@[to_additive]
/--
lemma `normalizer_le_normalizer_sup_of_normalizer_le_left` / 引理 `normalizer_le_normalizer_sup_of_normalizer_le_left`

English:
lemma normalizer_le_normalizer_sup_of_normalizer_le_left
  proof: (inf_of_le_left hHnK).symm.trans_le (H.normalizer_inf_normalizer_le_normalizer_sup K)

@[to_additive]

中文:
引理 normalizer_le_normalizer_sup_of_normalizer_le_left
  证明: (inf_of_le_left hHnK).symm.trans_le (H.normalizer_inf_normalizer_le_normalizer_sup K)

@[to_additive]

Depends on / 依赖: H.normalizer_inf_normalizer_le_normalizer_sup, inf_of_le_left, normalizer_inf_normalizer_le_normalizer_sup, symm.trans_le, trans_le
-/
lemma normalizer_le_normalizer_sup_of_normalizer_le_left
    {H K : Subgroup G} (hHnK : normalizer H <= normalizer (K : Set G)) :
    normalizer H <= normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  (inf_of_le_left hHnK).symm.trans_le (H.normalizer_inf_normalizer_le_normalizer_sup K)

@[to_additive]
/--
lemma `normalizer_le_normalizer_sup_of_normalizer_le_right` / 引理 `normalizer_le_normalizer_sup_of_normalizer_le_right`

English:
lemma normalizer_le_normalizer_sup_of_normalizer_le_right
  statement: {H K : Subgroup G}
  proof: by
  rw [sup_comm]
  exact normalizer_le_normalizer_sup_of_normalizer_le_left hHnK

@[to_additive]

中文:
引理 normalizer_le_normalizer_sup_of_normalizer_le_right
  结论: {H K : 子群 G}
  证明: by
  rw [sup_comm]
  exact normalizer_le_normalizer_sup_of_normalizer_le_left hHnK

@[to_additive]

Depends on / 依赖: normalizer_le_normalizer_sup_of_normalizer_le_left, sup_comm
-/
lemma normalizer_le_normalizer_sup_of_normalizer_le_right {H K : Subgroup G}
    (hHnK : normalizer H <= normalizer (K : Set G)) :
    normalizer H <= normalizer ((K ⊔ H : Subgroup G) : Set G) := by
  rw [sup_comm]
  exact normalizer_le_normalizer_sup_of_normalizer_le_left hHnK

@[to_additive]
/--
lemma `normalizer_le_normalizer_sup_normal` / 引理 `normalizer_le_normalizer_sup_normal`

English:
lemma normalizer_le_normalizer_sup_normal
  given: {H K : Subgroup G} [hK : K.Normal]
  proof: normalizer_le_normalizer_sup_of_normalizer_le_left le_normalizer_of_normal

@[to_additive]

中文:
引理 normalizer_le_normalizer_sup_normal
  条件: {H K : 子群 G} [hK : K.正规]
  证明: normalizer_le_normalizer_sup_of_normalizer_le_left le_normalizer_of_normal

@[to_additive]

Depends on / 依赖: le_normalizer_of_normal, normalizer_le_normalizer_sup_of_normalizer_le_left
-/
lemma normalizer_le_normalizer_sup_normal {H K : Subgroup G} [hK : K.Normal] :
    normalizer H <= normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  normalizer_le_normalizer_sup_of_normalizer_le_left le_normalizer_of_normal

@[to_additive]
/--
Instance `sup_normal` / 实例 `sup_normal`

English:
instance sup_normal
  signature: (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal]
  body: by
    rw [← SetLike.mem_coe]; rw [normal_mul] at hmem ⊢
    rcases hmem with ⟨h, hh, k, hk, rfl⟩
    refine ⟨g * h * g⁻¹, hH.conj_mem h hh g, g * k * g⁻¹, hK.conj_mem k hk g, ?_⟩
    simp only [mul_assoc, inv_mul_cancel_left]

@[to_additive]

中文:
实例 sup_normal
  签名: (H K : 子群 G) [hH : H.正规] [hK : K.正规]
  定义体: by
    rw [← SetLike.mem_coe]; rw [normal_mul] at hmem ⊢
    rcases hmem with ⟨h, hh, k, hk, rfl⟩
    refine ⟨g * h * g⁻¹, hH.conj_mem h hh g, g * k * g⁻¹, hK.conj_mem k hk g, ?_⟩
    simp only [mul_assoc, inv_mul_cancel_left]

@[to_additive]

Depends on / 依赖: SetLike, SetLike.mem_coe, conj_mem, hH.conj_mem, hK.conj_mem, inv_mul_cancel_left, mem_coe, mul_assoc, normal_mul
-/
instance sup_normal (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal] : (H ⊔ K).Normal where
  conj_mem n hmem g := by
    rw [← SetLike.mem_coe]; rw [normal_mul] at hmem ⊢
    rcases hmem with ⟨h, hh, k, hk, rfl⟩
    refine ⟨g * h * g⁻¹, hH.conj_mem h hh g, g * k * g⁻¹, hK.conj_mem k hk g, ?_⟩
    simp only [mul_assoc, inv_mul_cancel_left]

@[to_additive]
/--
Instance `iSup_normal` / 实例 `iSup_normal`

English:
instance iSup_normal
  signature: {ι : Sort*} (H : ι -> Subgroup G) [forall i, (H i).Normal]
  body: by ⨆ i, H i
  grw [← normalizer_eq_top_iff, eq_top_iff, ← iInf_normalizer_le_normalizer_iSup]
  simp [normalizer_eq_top]

@[to_additive]

中文:
实例 iSup_normal
  签名: {ι : 类型层*} (H : ι -> 子群 G) [对任意 i, (H i).正规]
  定义体: by ⨆ i, H i
  grw [← normalizer_eq_top_iff, eq_top_iff, ← iInf_normalizer_le_normalizer_iSup]
  simp [normalizer_eq_top]

@[to_additive]

Depends on / 依赖: eq_top_iff, iInf_normalizer_le_normalizer_iSup, normalizer_eq_top, normalizer_eq_top_iff
-/
instance iSup_normal {ι : Sort*} (H : ι -> Subgroup G) [forall i, (H i).Normal] :
.Normal := by ⨆ i, H i
  grw [← normalizer_eq_top_iff, eq_top_iff, ← iInf_normalizer_le_normalizer_iSup]
  simp [normalizer_eq_top]

@[to_additive]
/--
theorem `biSup_normal` / 定理 `biSup_normal`

English:
theorem biSup_normal
  given: {ι : Type*} (s : Set ι) (H : ι -> Subgroup G) (h : forall i in s, (H i).Normal)
  proof: by ⨆ i in s, H i
  rw [← iSup_subtype'']
  have : forall i : s, (H i).Normal := fun i => h i i.property
  apply iSup_normal

@[to_additive]
.Normal := by theorem sSup_normal (Hs : Set (Subgroup G)) (h : forall H in Hs, H.Normal) : sSup Hs
  rw [sSup_eq_iSup]
  exact biSup_normal Hs id h

@[to_additive]

中文:
定理 biSup_normal
  条件: {ι : 类型} (s : 集合 ι) (H : ι -> 子群 G) (h : 对任意 i in s, (H i).正规)
  证明: by ⨆ i in s, H i
  rw [← iSup_subtype'']
  have : forall i : s, (H i).Normal := fun i => h i i.property
  apply iSup_normal

@[to_additive]
.Normal := by theorem sSup_normal (Hs : Set (Subgroup G)) (h : forall H in Hs, H.Normal) : sSup Hs
  rw [sSup_eq_iSup]
  exact biSup_normal Hs id h

@[to_additive]

Depends on / 依赖: Normal, i.property, iSup_normal, iSup_subtype, property
-/
theorem biSup_normal {ι : Type*} (s : Set ι) (H : ι -> Subgroup G) (h : forall i in s, (H i).Normal) :
.Normal := by ⨆ i in s, H i
  rw [← iSup_subtype'']
  have : forall i : s, (H i).Normal := fun i => h i i.property
  apply iSup_normal

@[to_additive]
.Normal := by theorem sSup_normal (Hs : Set (Subgroup G)) (h : forall H in Hs, H.Normal) : sSup Hs
  rw [sSup_eq_iSup]
  exact biSup_normal Hs id h

@[to_additive]
/--
theorem `smul_mem_of_mem_closure_of_mem` / 定理 `smul_mem_of_mem_closure_of_mem`

English:
theorem smul_mem_of_mem_closure_of_mem
  statement: {X : Type*} [MulAction G X] {s : Set G} {t : Set X}
  proof: by
  induction hg using Subgroup.closure_induction'' generalizing x with
  | one => simpa
  | mem g' hg' => exact hst g' hg' x hx
  | inv_mem g' hg' => exact hst g'⁻¹ (hs g' hg') x hx
  | mul _ _ _ _ h₁ h₂ => rw [mul_smul]; exact h₁ (h₂ hx)

@[to_additive]

中文:
定理 smul_mem_of_mem_closure_of_mem
  结论: {X : 类型} [乘法作用 G X] {s : 集合 G} {t : 集合 X}
  证明: by
  induction hg using Subgroup.closure_induction'' generalizing x with
  | one => simpa
  | mem g' hg' => exact hst g' hg' x hx
  | inv_mem g' hg' => exact hst g'⁻¹ (hs g' hg') x hx
  | mul _ _ _ _ h₁ h₂ => rw [mul_smul]; exact h₁ (h₂ hx)

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.closure_induction, closure_induction, generalizing, inv_mem, mul_smul
-/
theorem smul_mem_of_mem_closure_of_mem {X : Type*} [MulAction G X] {s : Set G} {t : Set X}
    (hs : forall g in s, g⁻¹ in s) (hst : forallᵉ (g in s) (x in t), g • x in t) {g : G}
    (hg : g in Subgroup.closure s) {x : X} (hx : x in t) : g • x in t := by
  induction hg using Subgroup.closure_induction'' generalizing x with
  | one => simpa
  | mem g' hg' => exact hst g' hg' x hx
  | inv_mem g' hg' => exact hst g'⁻¹ (hs g' hg') x hx
  | mul _ _ _ _ h₁ h₂ => rw [mul_smul]; exact h₁ (h₂ hx)

@[to_additive]
/--
theorem `smul_opposite_image_mul_preimage'` / 定理 `smul_opposite_image_mul_preimage'`

English:
theorem smul_opposite_image_mul_preimage'
  given: (g : G) (h : Gᵐᵒᵖ) (s : Set G)
  proof: by
  simp [preimage_preimage, mul_assoc]

中文:
定理 smul_opposite_image_mul_preimage'
  条件: (g : G) (h : Gᵐᵒᵖ) (s : 集合 G)
  证明: by
  simp [preimage_preimage, mul_assoc]

Depends on / 依赖: mul_assoc, preimage_preimage
-/
theorem smul_opposite_image_mul_preimage' (g : G) (h : Gᵐᵒᵖ) (s : Set G) :
    (fun y => h • y) '' (g * ·) ⁻¹' s = (g * ·) ⁻¹' (fun y => h • y) '' s := by
  simp [preimage_preimage, mul_assoc]

-- TODO: deprecate?
@[to_additive]
/--
theorem `smul_opposite_image_mul_preimage` / 定理 `smul_opposite_image_mul_preimage`

English:
theorem smul_opposite_image_mul_preimage
  given: {H : Subgroup G} (g : G) (h : H.op) (s : Set G)
  proof: smul_opposite_image_mul_preimage' g h s

中文:
定理 smul_opposite_image_mul_preimage
  条件: {H : 子群 G} (g : G) (h : H.op) (s : 集合 G)
  证明: smul_opposite_image_mul_preimage' g h s

Depends on / 依赖: smul_opposite_image_mul_preimage
-/
theorem smul_opposite_image_mul_preimage {H : Subgroup G} (g : G) (h : H.op) (s : Set G) :
    (fun y => h • y) '' (g * ·) ⁻¹' s = (g * ·) ⁻¹' (fun y => h • y) '' s :=
  smul_opposite_image_mul_preimage' g h s

/-! ### Pointwise action -/


section Monoid

variable [Monoid α] [MulDistribMulAction α G]

/-- The action on a subgroup corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseMulAction` / `pointwiseMulAction` 的定义

English:
definition pointwiseMulAction
  signature: : MulAction α (Subgroup G) where
  body: S.map (MulDistribMulAction.toMonoidEnd _ _ a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using! S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : Monoid.End G => S.map f) (map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subgroup.pointwiseMulAction

中文:
定义 pointwiseMulAction
  签名: : 乘法作用 α (子群 G) where
  定义体: S.map (MulDistribMulAction.toMonoidEnd _ _ a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using! S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : Monoid.End G => S.map f) (map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subgroup.pointwiseMulAction
-/
protected def pointwiseMulAction : MulAction α (Subgroup G) where
  smul a S := S.map (MulDistribMulAction.toMonoidEnd _ _ a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using! S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : Monoid.End G => S.map f) (map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subgroup.pointwiseMulAction

/--
theorem `pointwise_smul_def` / 定理 `pointwise_smul_def`

English:
theorem pointwise_smul_def
  given: {a : α} (S : Subgroup G)
  proof: rfl

@[simp, norm_cast]

中文:
定理 pointwise_smul_def
  条件: {a : α} (S : 子群 G)
  证明: rfl

@[simp, norm_cast]
-/
theorem pointwise_smul_def {a : α} (S : Subgroup G) :
    a • S = S.map (MulDistribMulAction.toMonoidEnd _ _ a) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_pointwise_smul` / 定理 `coe_pointwise_smul`

English:
theorem coe_pointwise_smul
  given: (a : α) (S : Subgroup G)
  statement: ↑(a • S) = a • (S : Set G)
  proof: rfl

@[simp]

中文:
定理 coe_pointwise_smul
  条件: (a : α) (S : 子群 G)
  结论: ↑(a • S) = a • (S : 集合 G)
  证明: rfl

@[simp]
-/
theorem coe_pointwise_smul (a : α) (S : Subgroup G) : ↑(a • S) = a • (S : Set G) :=
  rfl

@[simp]
/--
theorem `pointwise_smul_toSubmonoid` / 定理 `pointwise_smul_toSubmonoid`

English:
theorem pointwise_smul_toSubmonoid
  given: (a : α) (S : Subgroup G)
  proof: rfl

中文:
定理 pointwise_smul_toSubmonoid
  条件: (a : α) (S : 子群 G)
  证明: rfl
-/
theorem pointwise_smul_toSubmonoid (a : α) (S : Subgroup G) :
    (a • S).toSubmonoid = a • S.toSubmonoid :=
  rfl

/--
theorem `smul_mem_pointwise_smul` / 定理 `smul_mem_pointwise_smul`

English:
theorem smul_mem_pointwise_smul
  given: (m : G) (a : α) (S : Subgroup G)
  statement: m in S -> a • m in a • S
  proof: (Set.smul_mem_smul_set : _ -> _ in a • (S : Set G))

中文:
定理 smul_mem_pointwise_smul
  条件: (m : G) (a : α) (S : 子群 G)
  结论: m in S -> a • m in a • S
  证明: (Set.smul_mem_smul_set : _ -> _ in a • (S : Set G))

Depends on / 依赖: Set.smul_mem_smul_set, smul_mem_smul_set
-/
theorem smul_mem_pointwise_smul (m : G) (a : α) (S : Subgroup G) : m in S -> a • m in a • S :=
  (Set.smul_mem_smul_set : _ -> _ in a • (S : Set G))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CovariantClass α (Subgroup G) HSMul.hSMul LE.le
  body: ⟨fun _ _ => image_mono⟩

中文:
实例 :
  签名: 协变类 α (子群 G) 异质标量乘法.hSMul LE.le
  定义体: ⟨fun _ _ => image_mono⟩

Depends on / 依赖: image_mono
-/
instance : CovariantClass α (Subgroup G) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_mono⟩

/--
theorem `mem_smul_pointwise_iff_exists` / 定理 `mem_smul_pointwise_iff_exists`

English:
theorem mem_smul_pointwise_iff_exists
  given: (m : G) (a : α) (S : Subgroup G)
  proof: (Set.mem_smul_set : m in a • (S : Set G) ↔ _)

@[simp]

中文:
定理 mem_smul_pointwise_iff_存在
  条件: (m : G) (a : α) (S : 子群 G)
  证明: (Set.mem_smul_set : m in a • (S : Set G) ↔ _)

@[simp]

Depends on / 依赖: Set.mem_smul_set, mem_smul_set
-/
theorem mem_smul_pointwise_iff_exists (m : G) (a : α) (S : Subgroup G) :
    m in a • S ↔ exists s : G, s in S ∧ a • s = m :=
  (Set.mem_smul_set : m in a • (S : Set G) ↔ _)

@[simp]
/--
theorem `smul_bot` / 定理 `smul_bot`

English:
theorem smul_bot
  given: (a : α)
  statement: a • (⊥ : Subgroup G) = ⊥
  proof: map_bot _

中文:
定理 smul_bot
  条件: (a : α)
  结论: a • (⊥ : 子群 G) = ⊥
  证明: map_bot _

Depends on / 依赖: map_bot
-/
theorem smul_bot (a : α) : a • (⊥ : Subgroup G) = ⊥ :=
  map_bot _

/--
theorem `smul_sup` / 定理 `smul_sup`

English:
theorem smul_sup
  given: (a : α) (S T : Subgroup G)
  statement: a • (S ⊔ T) = a • S ⊔ a • T
  proof: map_sup _ _ _

中文:
定理 smul_sup
  条件: (a : α) (S T : 子群 G)
  结论: a • (S ⊔ T) = a • S ⊔ a • T
  证明: map_sup _ _ _

Depends on / 依赖: map_sup
-/
theorem smul_sup (a : α) (S T : Subgroup G) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

/--
theorem `smul_closure` / 定理 `smul_closure`

English:
theorem smul_closure
  given: (a : α) (s : Set G)
  statement: a • closure s = closure (a • s)
  proof: MonoidHom.map_closure _ _

中文:
定理 smul_closure
  条件: (a : α) (s : 集合 G)
  结论: a • closure s = closure (a • s)
  证明: MonoidHom.map_closure _ _

Depends on / 依赖: MonoidHom, MonoidHom.map_closure, map_closure
-/
theorem smul_closure (a : α) (s : Set G) : a • closure s = closure (a • s) :=
  MonoidHom.map_closure _ _

/--
Instance `pointwise_isCentralScalar` / 实例 `pointwise_isCentralScalar`

English:
instance pointwise_isCentralScalar
  signature: [MulDistribMulAction αᵐᵒᵖ G] [IsCentralScalar α G]
  body: ⟨fun _ S => (congr_arg fun f => S.map f) MonoidHom.ext op_smul_eq_smul _⟩

中文:
实例 pointwise_isCentralScalar
  签名: [MulDistribMul作用 αᵐᵒᵖ G] [中心标量 α G]
  定义体: ⟨fun _ S => (congr_arg fun f => S.map f) MonoidHom.ext op_smul_eq_smul _⟩

Depends on / 依赖: MonoidHom, MonoidHom.ext, S.map, congr_arg, op_smul_eq_smul
-/
instance pointwise_isCentralScalar [MulDistribMulAction αᵐᵒᵖ G] [IsCentralScalar α G] :
    IsCentralScalar α (Subgroup G) :=
⟨fun _ S => (congr_arg fun f => S.map f) MonoidHom.ext op_smul_eq_smul _⟩

end Monoid

section Group

variable [Group α] [MulDistribMulAction α G]

@[simp]
/--
theorem `smul_mem_pointwise_smul_iff` / 定理 `smul_mem_pointwise_smul_iff`

English:
theorem smul_mem_pointwise_smul_iff
  given: {a : α} {S : Subgroup G} {x : G}
  statement: a • x in a • S ↔ x in S
  proof: smul_mem_smul_set_iff

中文:
定理 smul_mem_pointwise_smul_iff
  条件: {a : α} {S : 子群 G} {x : G}
  结论: a • x in a • S ↔ x in S
  证明: smul_mem_smul_set_iff

Depends on / 依赖: smul_mem_smul_set_iff
-/
theorem smul_mem_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : a • x in a • S ↔ x in S :=
  smul_mem_smul_set_iff

/--
theorem `mem_pointwise_smul_iff_inv_smul_mem` / 定理 `mem_pointwise_smul_iff_inv_smul_mem`

English:
theorem mem_pointwise_smul_iff_inv_smul_mem
  given: {a : α} {S : Subgroup G} {x : G}
  proof: mem_smul_set_iff_inv_smul_mem

中文:
定理 mem_pointwise_smul_iff_inv_smul_mem
  条件: {a : α} {S : 子群 G} {x : G}
  证明: mem_smul_set_iff_inv_smul_mem

Depends on / 依赖: mem_smul_set_iff_inv_smul_mem
-/
theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Subgroup G} {x : G} :
    x in a • S ↔ a⁻¹ • x in S :=
  mem_smul_set_iff_inv_smul_mem

/--
theorem `mem_inv_pointwise_smul_iff` / 定理 `mem_inv_pointwise_smul_iff`

English:
theorem mem_inv_pointwise_smul_iff
  given: {a : α} {S : Subgroup G} {x : G}
  statement: x in a⁻¹ • S ↔ a • x in S
  proof: mem_inv_smul_set_iff

@[simp]

中文:
定理 mem_inv_pointwise_smul_iff
  条件: {a : α} {S : 子群 G} {x : G}
  结论: x in a⁻¹ • S ↔ a • x in S
  证明: mem_inv_smul_set_iff

@[simp]

Depends on / 依赖: mem_inv_smul_set_iff
-/
theorem mem_inv_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : x in a⁻¹ • S ↔ a • x in S :=
  mem_inv_smul_set_iff

@[simp]
/--
theorem `pointwise_smul_le_pointwise_smul_iff` / 定理 `pointwise_smul_le_pointwise_smul_iff`

English:
theorem pointwise_smul_le_pointwise_smul_iff
  given: {a : α} {S T : Subgroup G}
  statement: a • S <= a • T ↔ S <= T
  proof: smul_set_subset_smul_set_iff

中文:
定理 pointwise_smul_le_pointwise_smul_iff
  条件: {a : α} {S T : 子群 G}
  结论: a • S <= a • T ↔ S <= T
  证明: smul_set_subset_smul_set_iff

Depends on / 依赖: smul_set_subset_smul_set_iff
-/
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Subgroup G} : a • S <= a • T ↔ S <= T :=
  smul_set_subset_smul_set_iff

/--
theorem `pointwise_smul_subset_iff` / 定理 `pointwise_smul_subset_iff`

English:
theorem pointwise_smul_subset_iff
  given: {a : α} {S T : Subgroup G}
  statement: a • S <= T ↔ S <= a⁻¹ • T
  proof: smul_set_subset_iff_subset_inv_smul_set

中文:
定理 pointwise_smul_subset_iff
  条件: {a : α} {S T : 子群 G}
  结论: a • S <= T ↔ S <= a⁻¹ • T
  证明: smul_set_subset_iff_subset_inv_smul_set

Depends on / 依赖: smul_set_subset_iff_subset_inv_smul_set
-/
theorem pointwise_smul_subset_iff {a : α} {S T : Subgroup G} : a • S <= T ↔ S <= a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set

/--
theorem `subset_pointwise_smul_iff` / 定理 `subset_pointwise_smul_iff`

English:
theorem subset_pointwise_smul_iff
  given: {a : α} {S T : Subgroup G}
  statement: S <= a • T ↔ a⁻¹ • S <= T
  proof: subset_smul_set_iff

中文:
定理 subset_pointwise_smul_iff
  条件: {a : α} {S T : 子群 G}
  结论: S <= a • T ↔ a⁻¹ • S <= T
  证明: subset_smul_set_iff

Depends on / 依赖: subset_smul_set_iff
-/
theorem subset_pointwise_smul_iff {a : α} {S T : Subgroup G} : S <= a • T ↔ a⁻¹ • S <= T :=
  subset_smul_set_iff

/--
theorem `conj_smul_le_of_le` / 定理 `conj_smul_le_of_le`

English:
theorem conj_smul_le_of_le
  given: {P H : Subgroup G} (hP : P <= H) (h : H)
  proof: by
  rintro - ⟨g, hg, rfl⟩
  exact H.mul_mem (H.mul_mem h.2 (hP hg)) (H.inv_mem h.2)

中文:
定理 conj_smul_le_of_le
  条件: {P H : 子群 G} (hP : P <= H) (h : H)
  证明: by
  rintro - ⟨g, hg, rfl⟩
  exact H.mul_mem (H.mul_mem h.2 (hP hg)) (H.inv_mem h.2)

Depends on / 依赖: H.inv_mem, H.mul_mem, inv_mem, mul_mem
-/
theorem conj_smul_le_of_le {P H : Subgroup G} (hP : P <= H) (h : H) :
    MulAut.conj (h : G) • P <= H := by
  rintro - ⟨g, hg, rfl⟩
  exact H.mul_mem (H.mul_mem h.2 (hP hg)) (H.inv_mem h.2)

/--
theorem `conj_smul_eq_self_of_mem` / 定理 `conj_smul_eq_self_of_mem`

English:
theorem conj_smul_eq_self_of_mem
  given: {H : Subgroup G} {h : G} (hh : h in H)
  proof: by
  refine le_antisymm ?_ ?_
  · exact (conj_smul_le_of_le (le_refl H) ⟨h, hh⟩)
  · rw [subset_pointwise_smul_iff, ← map_inv]
    exact conj_smul_le_of_le (le_refl H) ⟨h⁻¹, H.inv_mem hh⟩

中文:
定理 conj_smul_eq_self_of_mem
  条件: {H : 子群 G} {h : G} (hh : h in H)
  证明: by
  refine le_antisymm ?_ ?_
  · exact (conj_smul_le_of_le (le_refl H) ⟨h, hh⟩)
  · rw [subset_pointwise_smul_iff, ← map_inv]
    exact conj_smul_le_of_le (le_refl H) ⟨h⁻¹, H.inv_mem hh⟩

Depends on / 依赖: AddSubsemigroup, AddSubsemigroup.closure_le, AddSubsemigroup.subset_closure, AddSubsemigroup.toSubsemigroup, Additive, H.inv_mem, Subsemigroup, Subsemigroup.closure_le, Subsemigroup.subset_closure, closure_le, conj_smul_le_of_le, inv_mem, le_antisymm, le_refl, le_symm_apply, map_inv, subset_closure, subset_pointwise_smul_iff, toSubsemigroup
-/
theorem conj_smul_eq_self_of_mem {H : Subgroup G} {h : G} (hh : h in H) :
    MulAut.conj h • H = H := by
  refine le_antisymm ?_ ?_
  · exact (conj_smul_le_of_le (le_refl H) ⟨h, hh⟩)
  · rw [subset_pointwise_smul_iff, ← map_inv]
    exact conj_smul_le_of_le (le_refl H) ⟨h⁻¹, H.inv_mem hh⟩

/--
theorem `conj_smul_subgroupOf` / 定理 `conj_smul_subgroupOf`

English:
theorem conj_smul_subgroupOf
  given: {P H : Subgroup G} (hP : P <= H) (h : H)
  proof: by
  refine le_antisymm ?_ ?_
  · rintro - ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro p ⟨g, hg, hp⟩
    exact ⟨⟨g, hP hg⟩, hg, Subtype.ext hp⟩

@[simp]

中文:
定理 conj_smul_subgroupOf
  条件: {P H : 子群 G} (hP : P <= H) (h : H)
  证明: by
  refine le_antisymm ?_ ?_
  · rintro - ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro p ⟨g, hg, hp⟩
    exact ⟨⟨g, hP hg⟩, hg, Subtype.ext hp⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, le_antisymm
-/
theorem conj_smul_subgroupOf {P H : Subgroup G} (hP : P <= H) (h : H) :
    MulAut.conj h • P.subgroupOf H = (MulAut.conj (h : G) • P).subgroupOf H := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro p ⟨g, hg, hp⟩
    exact ⟨⟨g, hP hg⟩, hg, Subtype.ext hp⟩

@[simp]
/--
theorem `smul_inf` / 定理 `smul_inf`

English:
theorem smul_inf
  given: (a : α) (S T : Subgroup G)
  statement: a • (S ⊓ T) = a • S ⊓ a • T
  proof: by
  simp [SetLike.ext_iff, mem_pointwise_smul_iff_inv_smul_mem]

中文:
定理 smul_inf
  条件: (a : α) (S T : 子群 G)
  结论: a • (S ⊓ T) = a • S ⊓ a • T
  证明: by
  simp [SetLike.ext_iff, mem_pointwise_smul_iff_inv_smul_mem]

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff, mem_pointwise_smul_iff_inv_smul_mem
-/
theorem smul_inf (a : α) (S T : Subgroup G) : a • (S ⊓ T) = a • S ⊓ a • T := by
  simp [SetLike.ext_iff, mem_pointwise_smul_iff_inv_smul_mem]

/-- Applying a `MulDistribMulAction` results in an isomorphic subgroup -/
@[simps!]
/--
Definition of `equivSMul` / `equivSMul` 的定义

English:
definition equivSMul
  signature: (a : α) (H : Subgroup G)
  body: (MulDistribMulAction.toMulEquiv G a).subgroupMap H

中文:
定义 equivSMul
  签名: (a : α) (H : 子群 G)
  定义体: (MulDistribMulAction.toMulEquiv G a).subgroupMap H

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.toMulEquiv, subgroupMap, toMulEquiv
-/
def equivSMul (a : α) (H : Subgroup G) : H ≃* (a • H : Subgroup G) :=
  (MulDistribMulAction.toMulEquiv G a).subgroupMap H

/--
theorem `subgroup_mul_singleton` / 定理 `subgroup_mul_singleton`

English:
theorem subgroup_mul_singleton
  given: {H : Subgroup G} {h : G} (hh : h in H)
  statement: (H : Set G) * {h} = H
  proof: by
  simp [preimage, mul_mem_cancel_right (inv_mem hh)]

中文:
定理 subgroup_mul_singleton
  条件: {H : 子群 G} {h : G} (hh : h in H)
  结论: (H : 集合 G) * {h} = H
  证明: by
  simp [preimage, mul_mem_cancel_right (inv_mem hh)]

Depends on / 依赖: AddSubsemigroup, AddSubsemigroup.closure_le, AddSubsemigroup.subset_closure, Multiplicative, Subsemigroup, Subsemigroup.closure_le, Subsemigroup.subset_closure, Subsemigroup.toAddSubsemigroup, closure_le, inv_mem, l_le, le_antisymm, mul_mem_cancel_right, preimage, subset_closure, toAddSubsemigroup, to_galoisConnection, to_galoisConnection.l_le
-/
theorem subgroup_mul_singleton {H : Subgroup G} {h : G} (hh : h in H) : (H : Set G) * {h} = H := by
  simp [preimage, mul_mem_cancel_right (inv_mem hh)]

/--
theorem `singleton_mul_subgroup` / 定理 `singleton_mul_subgroup`

English:
theorem singleton_mul_subgroup
  given: {H : Subgroup G} {h : G} (hh : h in H)
  statement: {h} * (H : Set G) = H
  proof: by
  simp [preimage, mul_mem_cancel_left (inv_mem hh)]

中文:
定理 singleton_mul_subgroup
  条件: {H : 子群 G} {h : G} (hh : h in H)
  结论: {h} * (H : 集合 G) = H
  证明: by
  simp [preimage, mul_mem_cancel_left (inv_mem hh)]

Depends on / 依赖: inv_mem, mul_mem_cancel_left, preimage
-/
theorem singleton_mul_subgroup {H : Subgroup G} {h : G} (hh : h in H) : {h} * (H : Set G) = H := by
  simp [preimage, mul_mem_cancel_left (inv_mem hh)]

/--
theorem `Normal.conjAct` / 定理 `Normal.conjAct`

English:
theorem Normal.conjAct
  given: {H : Subgroup G} (hH : H.Normal) (g : ConjAct G)
  statement: g • H = H
  proof: have : forall g : ConjAct G, g • H <= H :=
    fun _ => map_le_iff_le_comap.2 fun _ h => hH.conj_mem _ h _
(this g).antisymm (smul_inv_smul g H).symm.trans_le (map_mono <| this _)

@[simp]

中文:
定理 正规.conjAct
  条件: {H : 子群 G} (hH : H.正规) (g : ConjAct G)
  结论: g • H = H
  证明: have : forall g : ConjAct G, g • H <= H :=
    fun _ => map_le_iff_le_comap.2 fun _ h => hH.conj_mem _ h _
(this g).antisymm (smul_inv_smul g H).symm.trans_le (map_mono <| this _)

@[simp]

Depends on / 依赖: ConjAct, antisymm, conj_mem, hH.conj_mem, map_le_iff_le_comap, map_mono, smul_inv_smul, symm.trans_le, trans_le
-/
theorem Normal.conjAct {H : Subgroup G} (hH : H.Normal) (g : ConjAct G) : g • H = H :=
  have : forall g : ConjAct G, g • H <= H :=
    fun _ => map_le_iff_le_comap.2 fun _ h => hH.conj_mem _ h _
(this g).antisymm (smul_inv_smul g H).symm.trans_le (map_mono <| this _)

@[simp]
/--
theorem `Normal.conj_smul_eq_self` / 定理 `Normal.conj_smul_eq_self`

English:
theorem Normal.conj_smul_eq_self
  given: (g : G) (H : Subgroup G) [h : Normal H]
  statement: MulAut.conj g • H = H
  proof: h.conjAct g

中文:
定理 正规.conj_smul_eq_self
  条件: (g : G) (H : 子群 G) [h : 正规 H]
  结论: MulAut.conj g • H = H
  证明: h.conjAct g

Depends on / 依赖: conjAct, h.conjAct
-/
theorem Normal.conj_smul_eq_self (g : G) (H : Subgroup G) [h : Normal H] : MulAut.conj g • H = H :=
  h.conjAct g

/--
theorem `Normal.of_conjugate_fixed` / 定理 `Normal.of_conjugate_fixed`

English:
theorem Normal.of_conjugate_fixed
  given: {H : Subgroup G} (h : forall g : G, (MulAut.conj g) • H = H)
  proof: by
  constructor
  intro n hn g
  rw [← h g]; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]; rw [← map_inv]; rw [MulAut.smul_def]; rw [MulAut.conj_apply]; rw [inv_inv]; rw [mul_assoc]; rw [mul_assoc]; rw [inv_mul_cancel]; rw [mul_one]; rw [← mul_assoc]; rw [inv_mul_cancel]; rw [one_mul]
  exact hn

中文:
定理 正规.of_conjugate_fixed
  条件: {H : 子群 G} (h : 对任意 g : G, (MulAut.conj g) • H = H)
  证明: by
  constructor
  intro n hn g
  rw [← h g]; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]; rw [← map_inv]; rw [MulAut.smul_def]; rw [MulAut.conj_apply]; rw [inv_inv]; rw [mul_assoc]; rw [mul_assoc]; rw [inv_mul_cancel]; rw [mul_one]; rw [← mul_assoc]; rw [inv_mul_cancel]; rw [one_mul]
  exact hn

Depends on / 依赖: MulAut, MulAut.conj_apply, MulAut.smul_def, Subgroup, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, conj_apply, inv_inv, inv_mul_cancel, map_inv, mem_pointwise_smul_iff_inv_smul_mem, mul_assoc, mul_one, one_mul, smul_def
-/
theorem Normal.of_conjugate_fixed {H : Subgroup G} (h : forall g : G, (MulAut.conj g) • H = H) :
    H.Normal := by
  constructor
  intro n hn g
  rw [← h g]; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]; rw [← map_inv]; rw [MulAut.smul_def]; rw [MulAut.conj_apply]; rw [inv_inv]; rw [mul_assoc]; rw [mul_assoc]; rw [inv_mul_cancel]; rw [mul_one]; rw [← mul_assoc]; rw [inv_mul_cancel]; rw [one_mul]
  exact hn

set_option backward.isDefEq.respectTransparency false in
/--
theorem `normalCore_eq_iInf_conjAct` / 定理 `normalCore_eq_iInf_conjAct`

English:
theorem normalCore_eq_iInf_conjAct
  given: (H : Subgroup G)
  proof: by
  ext g
  simp only [Subgroup.normalCore, Subgroup.mem_iInf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  refine ⟨fun h x => h x⁻¹, fun h x => ?_⟩
  simpa only [ConjAct.toConjAct_inv, inv_inv] using! h x⁻¹

中文:
定理 normalCore_eq_iInf_conjAct
  条件: (H : 子群 G)
  证明: by
  ext g
  simp only [Subgroup.normalCore, Subgroup.mem_iInf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  refine ⟨fun h x => h x⁻¹, fun h x => ?_⟩
  simpa only [ConjAct.toConjAct_inv, inv_inv] using! h x⁻¹

Depends on / 依赖: ConjAct, ConjAct.toConjAct_inv, Subgroup, Subgroup.mem_iInf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.normalCore, inv_inv, mem_iInf, mem_pointwise_smul_iff_inv_smul_mem, normalCore, toConjAct_inv
-/
theorem normalCore_eq_iInf_conjAct (H : Subgroup G) :
    H.normalCore = ⨅ (g : ConjAct G), g • H := by
  ext g
  simp only [Subgroup.normalCore, Subgroup.mem_iInf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  refine ⟨fun h x => h x⁻¹, fun h x => ?_⟩
  simpa only [ConjAct.toConjAct_inv, inv_inv] using! h x⁻¹

/--
lemma `conjAct_pointwise_smul_iff` / 引理 `conjAct_pointwise_smul_iff`

English:
lemma conjAct_pointwise_smul_iff
  given: {H : Subgroup G} {g : G}
  proof: by
  rw [← (normalizer H : Subgroup G).inv_mem_iff]
  simp only [Subgroup.ext_iff, mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, mem_normalizer_iff, inv_inv, Iff.comm]

中文:
引理 conjAct_pointwise_smul_iff
  条件: {H : 子群 G} {g : G}
  证明: by
  rw [← (normalizer H : Subgroup G).inv_mem_iff]
  simp only [Subgroup.ext_iff, mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, mem_normalizer_iff, inv_inv, Iff.comm]

Depends on / 依赖: ConjAct, ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, Iff.comm, Subgroup, Subgroup.ext_iff, ext_iff, inv_inv, inv_mem_iff, mem_normalizer_iff, mem_pointwise_smul_iff_inv_smul_mem, normalizer, toConjAct_inv, toConjAct_smul
-/
lemma conjAct_pointwise_smul_iff {H : Subgroup G} {g : G} :
    ConjAct.toConjAct g • H = H ↔ g in normalizer H := by
  rw [← (normalizer H : Subgroup G).inv_mem_iff]
  simp only [Subgroup.ext_iff, mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, mem_normalizer_iff, inv_inv, Iff.comm]

/--
lemma `conjAct_pointwise_smul_eq_self` / 引理 `conjAct_pointwise_smul_eq_self`

English:
lemma conjAct_pointwise_smul_eq_self
  given: {H : Subgroup G} {g : G} (hg : g in normalizer H)
  proof: conjAct_pointwise_smul_iff.2 hg

中文:
引理 conjAct_pointwise_smul_eq_self
  条件: {H : 子群 G} {g : G} (hg : g in normalizer H)
  证明: conjAct_pointwise_smul_iff.2 hg

Depends on / 依赖: conjAct_pointwise_smul_iff
-/
lemma conjAct_pointwise_smul_eq_self {H : Subgroup G} {g : G} (hg : g in normalizer H) :
    ConjAct.toConjAct g • H = H :=
  conjAct_pointwise_smul_iff.2 hg

end Group
end Subgroup
