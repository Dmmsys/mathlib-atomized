/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Order.Group.Action
public import Mathlib.Algebra.Module.Submodule.Range

/-! # Pointwise instances on `Submodule`s

This file provides:

* `Submodule.pointwiseNeg`

and the actions

* `Submodule.pointwiseDistribMulAction`
* `Submodule.pointwiseMulActionWithZero`

which matches the action of `Set.mulActionSet`.

This file also provides:
* `Submodule.pointwiseSetSMulSubmodule`: for `R`-module `M`, a `s : Set R` can act on
  `N : Submodule R M` by defining `s • N` to be the smallest submodule containing all `a • n`
  where `a ∈ s` and `n ∈ N`.

These actions are available in the `Pointwise` locale.

## Implementation notes

For an `R`-module `M`, the action of a subset of `R` acting on a submodule of `M` introduced in
section `set_acting_on_submodules` does not have a counterpart in the files
`Mathlib/Algebra/Group/Submonoid/Pointwise.lean` and
`Mathlib/Algebra/GroupWithZero/Submonoid/Pointwise.lean`.

Other than section `DistribMulAction`, most of the lemmas in this file are direct copies of
lemmas from the file `Mathlib/Algebra/Group/Submonoid/Pointwise.lean`.
-/

@[expose] public section

assert_not_exists Ideal

variable {α : Type*} {R : Type*} {M : Type*}

open scoped Pointwise

namespace Submodule

section Neg

section Semiring

variable [Semiring R] [AddCommGroup M] [Module R M]

/-- The submodule with every element negated. Note if `R` is a ring and not just a semiring, this
is a no-op, as shown by `Submodule.neg_eq_self`.

Recall that When `R` is the semiring corresponding to the nonnegative elements of `R'`,
`Submodule R' M` is the type of cones of `M`. This instance reflects such cones about `0`.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseNeg` / `pointwiseNeg` 的定义

English:
definition pointwiseNeg
  signature: : Neg (Submodule R M) where
  body: { -p.toAddSubmonoid with
smul_mem' := fun r m hm => Set.mem_neg.2 smul_neg r m ▸ p.smul_mem r Set.mem_neg.1 hm }

scoped[Pointwise] attribute [instance] Submodule.pointwiseNeg

中文:
定义 pointwiseNeg
  签名: : Neg (Submodule R M) where
  定义体: { -p.toAddSubmonoid with
smul_mem' := fun r m hm => Set.mem_neg.2 smul_neg r m ▸ p.smul_mem r Set.mem_neg.1 hm }

scoped[Pointwise] attribute [instance] Submodule.pointwiseNeg
-/
protected def pointwiseNeg : Neg (Submodule R M) where
  neg p :=
    { -p.toAddSubmonoid with
smul_mem' := fun r m hm => Set.mem_neg.2 smul_neg r m ▸ p.smul_mem r Set.mem_neg.1 hm }

scoped[Pointwise] attribute [instance] Submodule.pointwiseNeg

open scoped Pointwise

@[simp]
/--
theorem `coe_set_neg` / 定理 `coe_set_neg`

English:
theorem coe_set_neg
  given: (S : Submodule R M)
  statement: ↑(-S) = -(S : Set M)
  proof: rfl

@[simp]

中文:
定理 coe_set_neg
  条件: (S : Submodule R M)
  结论: ↑(-S) = -(S : Set M)
  证明: rfl

@[simp]
-/
theorem coe_set_neg (S : Submodule R M) : ↑(-S) = -(S : Set M) :=
  rfl

@[simp]
/--
theorem `neg_toAddSubmonoid` / 定理 `neg_toAddSubmonoid`

English:
theorem neg_toAddSubmonoid
  given: (S : Submodule R M)
  statement: (-S).toAddSubmonoid = -S.toAddSubmonoid
  proof: rfl

@[simp]

中文:
定理 neg_toAddSubmonoid
  条件: (S : Submodule R M)
  结论: (-S).toAddSubmonoid = -S.toAddSubmonoid
  证明: rfl

@[simp]
-/
theorem neg_toAddSubmonoid (S : Submodule R M) : (-S).toAddSubmonoid = -S.toAddSubmonoid :=
  rfl

@[simp]
/--
theorem `mem_neg` / 定理 `mem_neg`

English:
theorem mem_neg
  given: {g : M} {S : Submodule R M}
  statement: g in -S ↔ -g in S
  proof: Iff.rfl

中文:
定理 mem_neg
  条件: {g : M} {S : Submodule R M}
  结论: g in -S ↔ -g in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_neg {g : M} {S : Submodule R M} : g in -S ↔ -g in S :=
  Iff.rfl

/-- `Submodule.pointwiseNeg` is involutive.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `involutivePointwiseNeg` / `involutivePointwiseNeg` 的定义

English:
definition involutivePointwiseNeg
  signature: : InvolutiveNeg (Submodule R M) where
  body: SetLike.coe_injective neg_neg _

scoped[Pointwise] attribute [instance] Submodule.involutivePointwiseNeg

@[simp]

中文:
定义 involutivePointwiseNeg
  签名: : InvolutiveNeg (Submodule R M) where
  定义体: SetLike.coe_injective neg_neg _

scoped[Pointwise] attribute [instance] Submodule.involutivePointwiseNeg

@[simp]
-/
protected def involutivePointwiseNeg : InvolutiveNeg (Submodule R M) where
neg_neg _S := SetLike.coe_injective neg_neg _

scoped[Pointwise] attribute [instance] Submodule.involutivePointwiseNeg

@[simp]
/--
theorem `neg_le_neg` / 定理 `neg_le_neg`

English:
theorem neg_le_neg
  given: {S T : Submodule R M}
  statement: -S <= -T ↔ S <= T
  proof: SetLike.coe_subset_coe.symm.trans Set.neg_subset_neg

中文:
定理 neg_le_neg
  条件: {S T : Submodule R M}
  结论: -S <= -T ↔ S <= T
  证明: SetLike.coe_subset_coe.symm.trans Set.neg_subset_neg

Depends on / 依赖: Set.neg_subset_neg, SetLike, SetLike.coe_subset_coe.symm.trans, coe_subset_coe, neg_subset_neg
-/
theorem neg_le_neg {S T : Submodule R M} : -S <= -T ↔ S <= T :=
  SetLike.coe_subset_coe.symm.trans Set.neg_subset_neg

/--
theorem `neg_le` / 定理 `neg_le`

English:
theorem neg_le
  given: {S T : Submodule R M}
  statement: -S <= T ↔ S <= -T
  proof: SetLike.coe_subset_coe.symm.trans Set.neg_subset

中文:
定理 neg_le
  条件: {S T : Submodule R M}
  结论: -S <= T ↔ S <= -T
  证明: SetLike.coe_subset_coe.symm.trans Set.neg_subset

Depends on / 依赖: Set.neg_subset, SetLike, SetLike.coe_subset_coe.symm.trans, coe_subset_coe, neg_subset
-/
theorem neg_le {S T : Submodule R M} : -S <= T ↔ S <= -T :=
  SetLike.coe_subset_coe.symm.trans Set.neg_subset

/--
theorem `neg_eq_self_iff_neg_le` / 定理 `neg_eq_self_iff_neg_le`

English:
theorem neg_eq_self_iff_neg_le
  given: {S : Submodule R M}
  statement: -S = S ↔ -S <= S
  proof: ⟨le_of_eq, fun h => antisymm h neg_le.mp h⟩

中文:
定理 neg_eq_self_iff_neg_le
  条件: {S : Submodule R M}
  结论: -S = S ↔ -S <= S
  证明: ⟨le_of_eq, fun h => antisymm h neg_le.mp h⟩

Depends on / 依赖: antisymm, le_of_eq, neg_le, neg_le.mp
-/
theorem neg_eq_self_iff_neg_le {S : Submodule R M} : -S = S ↔ -S <= S :=
⟨le_of_eq, fun h => antisymm h neg_le.mp h⟩

/--
Definition of `negOrderIso` / `negOrderIso` 的定义

English:
definition negOrderIso
  signature: : Submodule R M ≃o Submodule R M where
  body: Equiv.neg _
  map_rel_iff' := @neg_le_neg _ _ _ _ _

@[simp]

中文:
定义 negOrderIso
  签名: : Submodule R M ≃o Submodule R M where
  定义体: Equiv.neg _
  map_rel_iff' := @neg_le_neg _ _ _ _ _

@[simp]

Depends on / 依赖: Equiv.neg
-/
def negOrderIso : Submodule R M ≃o Submodule R M where
  toEquiv := Equiv.neg _
  map_rel_iff' := @neg_le_neg _ _ _ _ _

@[simp]
/--
theorem `neg_inf` / 定理 `neg_inf`

English:
theorem neg_inf
  given: (S T : Submodule R M)
  statement: -(S ⊓ T) = -S ⊓ -T
  proof: rfl

@[simp]

中文:
定理 neg_inf
  条件: (S T : Submodule R M)
  结论: -(S ⊓ T) = -S ⊓ -T
  证明: rfl

@[simp]
-/
theorem neg_inf (S T : Submodule R M) : -(S ⊓ T) = -S ⊓ -T := rfl

@[simp]
/--
theorem `neg_sup` / 定理 `neg_sup`

English:
theorem neg_sup
  given: (S T : Submodule R M)
  statement: -(S ⊔ T) = -S ⊔ -T
  proof: (negOrderIso : Submodule R M ≃o Submodule R M).map_sup S T

@[simp]

中文:
定理 neg_sup
  条件: (S T : Submodule R M)
  结论: -(S ⊔ T) = -S ⊔ -T
  证明: (negOrderIso : Submodule R M ≃o Submodule R M).map_sup S T

@[simp]

Depends on / 依赖: Submodule, map_sup, negOrderIso
-/
theorem neg_sup (S T : Submodule R M) : -(S ⊔ T) = -S ⊔ -T :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_sup S T

@[simp]
/--
theorem `neg_bot` / 定理 `neg_bot`

English:
theorem neg_bot
  statement: -(⊥ : Submodule R M) = ⊥
  proof: SetLike.coe_injective (Set.neg_singleton 0).trans congr_arg _ neg_zero

@[simp]

中文:
定理 neg_bot
  结论: -(⊥ : Submodule R M) = ⊥
  证明: SetLike.coe_injective (Set.neg_singleton 0).trans congr_arg _ neg_zero

@[simp]

Depends on / 依赖: Set.neg_singleton, SetLike, SetLike.coe_injective, coe_injective, congr_arg, neg_singleton, neg_zero
-/
theorem neg_bot : -(⊥ : Submodule R M) = ⊥ :=
SetLike.coe_injective (Set.neg_singleton 0).trans congr_arg _ neg_zero

@[simp]
/--
theorem `neg_top` / 定理 `neg_top`

English:
theorem neg_top
  statement: -(⊤ : Submodule R M) = ⊤
  proof: SetLike.coe_injective Set.neg_univ

@[simp]

中文:
定理 neg_top
  结论: -(⊤ : Submodule R M) = ⊤
  证明: SetLike.coe_injective Set.neg_univ

@[simp]

Depends on / 依赖: Set.neg_univ, SetLike, SetLike.coe_injective, coe_injective, neg_univ
-/
theorem neg_top : -(⊤ : Submodule R M) = ⊤ :=
SetLike.coe_injective Set.neg_univ

@[simp]
/--
theorem `neg_iInf` / 定理 `neg_iInf`

English:
theorem neg_iInf
  given: {ι : Sort*} (S : ι -> Submodule R M)
  statement: (-⨅ i, S i) = ⨅ i, -S i
  proof: (negOrderIso : Submodule R M ≃o Submodule R M).map_iInf _

@[simp]

中文:
定理 neg_iInf
  条件: {ι : Sort*} (S : ι -> Submodule R M)
  结论: (-⨅ i, S i) = ⨅ i, -S i
  证明: (negOrderIso : Submodule R M ≃o Submodule R M).map_iInf _

@[simp]

Depends on / 依赖: Submodule, map_iInf, negOrderIso
-/
theorem neg_iInf {ι : Sort*} (S : ι -> Submodule R M) : (-⨅ i, S i) = ⨅ i, -S i :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_iInf _

@[simp]
/--
theorem `neg_iSup` / 定理 `neg_iSup`

English:
theorem neg_iSup
  given: {ι : Sort*} (S : ι -> Submodule R M)
  statement: (-⨆ i, S i) = ⨆ i, -S i
  proof: (negOrderIso : Submodule R M ≃o Submodule R M).map_iSup _

中文:
定理 neg_iSup
  条件: {ι : Sort*} (S : ι -> Submodule R M)
  结论: (-⨆ i, S i) = ⨆ i, -S i
  证明: (negOrderIso : Submodule R M ≃o Submodule R M).map_iSup _

Depends on / 依赖: Submodule, map_iSup, negOrderIso
-/
theorem neg_iSup {ι : Sort*} (S : ι -> Submodule R M) : (-⨆ i, S i) = ⨆ i, -S i :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_iSup _

variable {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]

/--
theorem `neg_restrictScalars` / 定理 `neg_restrictScalars`

English:
theorem neg_restrictScalars
  given: (p : Submodule R M)
  proof: by ext; simp

中文:
定理 neg_restrictScalars
  条件: (p : Submodule R M)
  证明: by ext; simp
-/
@[simp] theorem neg_restrictScalars (p : Submodule R M) :
  -(restrictScalars S p) = restrictScalars S (-p) := by ext; simp

end Semiring

open scoped Pointwise

@[simp]
/--
theorem `neg_eq_self` / 定理 `neg_eq_self`

English:
theorem neg_eq_self
  given: [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)
  statement: -p = p
  proof: ext fun _ => p.neg_mem_iff

中文:
定理 neg_eq_self
  条件: [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)
  结论: -p = p
  证明: ext fun _ => p.neg_mem_iff

Depends on / 依赖: neg_mem_iff, p.neg_mem_iff
-/
theorem neg_eq_self [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M) : -p = p :=
  ext fun _ => p.neg_mem_iff

end Neg

variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
Instance `pointwiseZero` / 实例 `pointwiseZero`

English:
instance pointwiseZero
  signature: : Zero (Submodule R M) where
  body: ⊥

中文:
实例 pointwiseZero
  签名: : Zero (Submodule R M) where
  定义体: ⊥
-/
instance pointwiseZero : Zero (Submodule R M) where
  zero := ⊥

/--
Instance `pointwiseAdd` / 实例 `pointwiseAdd`

English:
instance pointwiseAdd
  signature: : Add (Submodule R M) where
  body: (· ⊔ ·)

中文:
实例 pointwiseAdd
  签名: : Add (Submodule R M) where
  定义体: (· ⊔ ·)
-/
instance pointwiseAdd : Add (Submodule R M) where
  add := (· ⊔ ·)

/--
Instance `pointwiseAddCommMonoid` / 实例 `pointwiseAddCommMonoid`

English:
instance pointwiseAddCommMonoid
  signature: : AddCommMonoid (Submodule R M) where
  body: sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

@[simp]

中文:
实例 pointwiseAddCommMonoid
  签名: : AddCommMonoid (Submodule R M) where
  定义体: sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

@[simp]

Depends on / 依赖: sup_assoc
-/
instance pointwiseAddCommMonoid : AddCommMonoid (Submodule R M) where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

@[simp]
/--
theorem `add_eq_sup` / 定理 `add_eq_sup`

English:
theorem add_eq_sup
  given: (p q : Submodule R M)
  statement: p + q = p ⊔ q
  proof: rfl

@[simp]

中文:
定理 add_eq_sup
  条件: (p q : Submodule R M)
  结论: p + q = p ⊔ q
  证明: rfl

@[simp]
-/
theorem add_eq_sup (p q : Submodule R M) : p + q = p ⊔ q :=
  rfl

@[simp]
/--
theorem `zero_eq_bot` / 定理 `zero_eq_bot`

English:
theorem zero_eq_bot
  statement: (0 : Submodule R M) = ⊥
  proof: rfl

中文:
定理 zero_eq_bot
  结论: (0 : Submodule R M) = ⊥
  证明: rfl
-/
theorem zero_eq_bot : (0 : Submodule R M) = ⊥ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedAddMonoid (Submodule R M)
  body: sup_le_sup_right

中文:
实例 :
  签名: IsOrderedAddMonoid (Submodule R M)
  定义体: sup_le_sup_right

Depends on / 依赖: sup_le_sup_right
-/
instance : IsOrderedAddMonoid (Submodule R M) where
  add_le_add_left _ _ := sup_le_sup_right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanonicallyOrderedAdd (Submodule R M)
  body: ⟨b, (sup_eq_right.2 h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add := fun _a _b => le_sup_left

中文:
实例 :
  签名: CanonicallyOrderedAdd (Submodule R M)
  定义体: ⟨b, (sup_eq_right.2 h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add := fun _a _b => le_sup_left

Depends on / 依赖: sup_eq_right
-/
instance : CanonicallyOrderedAdd (Submodule R M) where
  exists_add_of_le {_a b} h := ⟨b, (sup_eq_right.2 h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add := fun _a _b => le_sup_left

section

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseDistribMulAction` / `pointwiseDistribMulAction` 的定义

English:
definition pointwiseDistribMulAction
  signature: : DistribMulAction α (Submodule R M) where
  body: S.map (DistribSMul.toLinearMap R M a : M ->ₗ[R] M)
  one_smul S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| one_smul α)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| mul_smul _ _)).trans
      (S.map_comp _ _)

中文:
定义 pointwiseDistribMulAction
  签名: : DistribMulAction α (Submodule R M) where
  定义体: S.map (DistribSMul.toLinearMap R M a : M ->ₗ[R] M)
  one_smul S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| one_smul α)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| mul_smul _ _)).trans
      (S.map_comp _ _)
-/
protected def pointwiseDistribMulAction : DistribMulAction α (Submodule R M) where
  smul a S := S.map (DistribSMul.toLinearMap R M a : M ->ₗ[R] M)
  one_smul S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| one_smul α)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| mul_smul _ _)).trans
      (S.map_comp _ _)
  smul_zero _a := map_bot _
  smul_add _a _S₁ _S₂ := map_sup _ _ _

scoped[Pointwise] attribute [instance] Submodule.pointwiseDistribMulAction

/--
theorem `pointwise_smul_def` / 定理 `pointwise_smul_def`

English:
theorem pointwise_smul_def
  given: {a : α} {S : Submodule R M}
  proof: rfl

中文:
定理 pointwise_smul_def
  条件: {a : α} {S : Submodule R M}
  证明: rfl
-/
theorem pointwise_smul_def {a : α} {S : Submodule R M} :
    a • S = S.map (DistribSMul.toLinearMap R M a) := rfl

open scoped Pointwise

@[simp, norm_cast]
/--
theorem `coe_pointwise_smul` / 定理 `coe_pointwise_smul`

English:
theorem coe_pointwise_smul
  given: (a : α) (S : Submodule R M)
  statement: ↑(a • S) = a • (S : Set M)
  proof: rfl

@[simp]

中文:
定理 coe_pointwise_smul
  条件: (a : α) (S : Submodule R M)
  结论: ↑(a • S) = a • (S : Set M)
  证明: rfl

@[simp]
-/
theorem coe_pointwise_smul (a : α) (S : Submodule R M) : ↑(a • S) = a • (S : Set M) :=
  rfl

@[simp]
/--
theorem `pointwise_smul_toAddSubmonoid` / 定理 `pointwise_smul_toAddSubmonoid`

English:
theorem pointwise_smul_toAddSubmonoid
  given: (a : α) (S : Submodule R M)
  proof: rfl

@[simp]

中文:
定理 pointwise_smul_toAddSubmonoid
  条件: (a : α) (S : Submodule R M)
  证明: rfl

@[simp]
-/
theorem pointwise_smul_toAddSubmonoid (a : α) (S : Submodule R M) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl

@[simp]
/--
theorem `pointwise_smul_toAddSubgroup` / 定理 `pointwise_smul_toAddSubgroup`

English:
theorem pointwise_smul_toAddSubgroup
  statement: {R M : Type*} [Ring R] [AddCommGroup M] [DistribMulAction α M]
  proof: rfl

中文:
定理 pointwise_smul_toAddSubgroup
  结论: {R M : 类型} [Ring R] [AddCommGroup M] [DistribMulAction α M]
  证明: rfl
-/
theorem pointwise_smul_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [DistribMulAction α M]
    [Module R M] [SMulCommClass α R M] (a : α) (S : Submodule R M) :
    (a • S).toAddSubgroup = a • S.toAddSubgroup :=
  rfl

/--
theorem `mem_smul_pointwise_iff_exists` / 定理 `mem_smul_pointwise_iff_exists`

English:
theorem mem_smul_pointwise_iff_exists
  given: (m : M) (a : α) (S : Submodule R M)
  proof: Set.mem_smul_set

中文:
定理 mem_smul_pointwise_iff_exists
  条件: (m : M) (a : α) (S : Submodule R M)
  证明: Set.mem_smul_set

Depends on / 依赖: Set.mem_smul_set, mem_smul_set
-/
theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submodule R M) :
    m in a • S ↔ exists b in S, a • b = m :=
  Set.mem_smul_set

/--
theorem `smul_mem_pointwise_smul` / 定理 `smul_mem_pointwise_smul`

English:
theorem smul_mem_pointwise_smul
  given: (m : M) (a : α) (S : Submodule R M)
  statement: m in S -> a • m in a • S
  proof: (Set.smul_mem_smul_set : _ -> _ in a • (S : Set M))

中文:
定理 smul_mem_pointwise_smul
  条件: (m : M) (a : α) (S : Submodule R M)
  结论: m in S -> a • m in a • S
  证明: (Set.smul_mem_smul_set : _ -> _ in a • (S : Set M))

Depends on / 依赖: Set.smul_mem_smul_set, smul_mem_smul_set
-/
theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submodule R M) : m in S -> a • m in a • S :=
  (Set.smul_mem_smul_set : _ -> _ in a • (S : Set M))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CovariantClass α (Submodule R M) HSMul.hSMul LE.le
  body: ⟨fun _ _ => map_mono⟩

中文:
实例 :
  签名: CovariantClass α (Submodule R M) HSMul.hSMul LE.le
  定义体: ⟨fun _ _ => map_mono⟩

Depends on / 依赖: map_mono
-/
instance : CovariantClass α (Submodule R M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map_mono⟩

/-- See also `Submodule.smul_bot`. -/
@[simp]
/--
theorem `smul_bot'` / 定理 `smul_bot'`

English:
theorem smul_bot'
  given: (a : α)
  statement: a • (⊥ : Submodule R M) = ⊥
  proof: map_bot _

中文:
定理 smul_bot'
  条件: (a : α)
  结论: a • (⊥ : Submodule R M) = ⊥
  证明: map_bot _

Depends on / 依赖: map_bot
-/
theorem smul_bot' (a : α) : a • (⊥ : Submodule R M) = ⊥ :=
  map_bot _

/--
theorem `smul_sup'` / 定理 `smul_sup'`

English:
theorem smul_sup'
  given: (a : α) (S T : Submodule R M)
  statement: a • (S ⊔ T) = a • S ⊔ a • T
  proof: map_sup _ _ _

中文:
定理 smul_sup'
  条件: (a : α) (S T : Submodule R M)
  结论: a • (S ⊔ T) = a • S ⊔ a • T
  证明: map_sup _ _ _

Depends on / 依赖: map_sup
-/
theorem smul_sup' (a : α) (S T : Submodule R M) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

/--
theorem `smul_iSup'` / 定理 `smul_iSup'`

English:
theorem smul_iSup'
  given: (a : α) {ι : Sort*} (f : ι -> Submodule R M)
  proof: map_iSup _ _

中文:
定理 smul_iSup'
  条件: (a : α) {ι : Sort*} (f : ι -> Submodule R M)
  证明: map_iSup _ _

Depends on / 依赖: map_iSup
-/
theorem smul_iSup' (a : α) {ι : Sort*} (f : ι -> Submodule R M) :
    a • ⨆ i, f i = ⨆ i, a • f i :=
  map_iSup _ _

/--
Instance `pointwiseCentralScalar` / 实例 `pointwiseCentralScalar`

English:
instance pointwiseCentralScalar
  signature: [DistribMulAction αᵐᵒᵖ M] [SMulCommClass αᵐᵒᵖ R M]
  body: ⟨fun _a S => (congr_arg fun f : Module.End R M => S.map f) LinearMap.ext op_smul_eq_smul _⟩

@[simp]

中文:
实例 pointwiseCentralScalar
  签名: [DistribMulAction αᵐᵒᵖ M] [SMulCommClass αᵐᵒᵖ R M]
  定义体: ⟨fun _a S => (congr_arg fun f : Module.End R M => S.map f) LinearMap.ext op_smul_eq_smul _⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, Module, Module.End, S.map, congr_arg, op_smul_eq_smul
-/
instance pointwiseCentralScalar [DistribMulAction αᵐᵒᵖ M] [SMulCommClass αᵐᵒᵖ R M]
    [IsCentralScalar α M] : IsCentralScalar α (Submodule R M) :=
⟨fun _a S => (congr_arg fun f : Module.End R M => S.map f) LinearMap.ext op_smul_eq_smul _⟩

@[simp]
/--
theorem `smul_le_self_of_tower` / 定理 `smul_le_self_of_tower`

English:
theorem smul_le_self_of_tower
  statement: {α : Type*} [Monoid α] [SMul α R] [DistribMulAction α M]
  proof: by
  rintro y ⟨x, hx, rfl⟩
  exact smul_of_tower_mem _ a hx

中文:
定理 smul_le_self_of_tower
  结论: {α : 类型} [Monoid α] [SMul α R] [DistribMulAction α M]
  证明: by
  rintro y ⟨x, hx, rfl⟩
  exact smul_of_tower_mem _ a hx

Depends on / 依赖: smul_of_tower_mem
-/
theorem smul_le_self_of_tower {α : Type*} [Monoid α] [SMul α R] [DistribMulAction α M]
    [SMulCommClass α R M] [IsScalarTower α R M] (a : α) (S : Submodule R M) : a • S <= S := by
  rintro y ⟨x, hx, rfl⟩
  exact smul_of_tower_mem _ a hx

end

section

variable [Semiring α] [Module α M] [SMulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `Submodule.pointwiseDistribMulAction`. Note that `add_smul` does
not hold so this cannot be stated as a `Module`. -/
@[instance_reducible]
/--
Definition of `pointwiseMulActionWithZero` / `pointwiseMulActionWithZero` 的定义

English:
definition pointwiseMulActionWithZero
  signature: : MulActionWithZero α (Submodule R M)
  body: { Submodule.pointwiseDistribMulAction with
    zero_smul := fun S =>
      (congr_arg (fun f : M ->ₗ[R] M => S.map f) (LinearMap.ext <| zero_smul α)).trans S.map_zero }

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulActionWithZero

中文:
定义 pointwiseMulActionWithZero
  签名: : MulActionWithZero α (Submodule R M)
  定义体: { Submodule.pointwiseDistribMulAction with
    zero_smul := fun S =>
      (congr_arg (fun f : M ->ₗ[R] M => S.map f) (LinearMap.ext <| zero_smul α)).trans S.map_zero }

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulActionWithZero
-/
protected def pointwiseMulActionWithZero : MulActionWithZero α (Submodule R M) :=
  { Submodule.pointwiseDistribMulAction with
    zero_smul := fun S =>
      (congr_arg (fun f : M ->ₗ[R] M => S.map f) (LinearMap.ext <| zero_smul α)).trans S.map_zero }

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulActionWithZero

end

/-!
### Sets acting on Submodules

Let `R` be a (semi)ring and `M` an `R`-module. Let `S` be a monoid which acts on `M` distributively,
then subsets of `S` can act on submodules of `M`.
For subset `s ⊆ S` and submodule `N ≤ M`, we define `s • N` to be the smallest submodule containing
all `r • n` where `r ∈ s` and `n ∈ N`.

#### Results
For arbitrary monoids `S` acting distributively on `M`, there is an induction principle for `s • N`:
To prove `P` holds for all `s • N`, it is enough
to prove:
- for all `r ∈ s` and `n ∈ N`, `P (r • n)`;
- for all `r` and `m ∈ s • N`, `P (r • n)`;
- for all `m₁, m₂`, `P m₁` and `P m₂` implies `P (m₁ + m₂)`;
- `P 0`.

To invoke this induction principle, use `induction x, hx using Submodule.set_smul_inductionOn` where
`x : M` and `hx : x ∈ s • N`

#### Notes
- If we assume the addition on subsets of `R` is the `⊔` and subtraction `⊓` i.e. use `SetSemiring`,
  then this action actually gives a module structure on submodules of `M` over subsets of `R`.
- If we generalize so that `r • N` makes sense for all `r : S`, then `Submodule.singleton_set_smul`
  and `Submodule.singleton_set_smul` can be generalized as well.
-/

section DistribMulAction

variable {S : Type*} [Monoid S]
variable [DistribMulAction S M]

/--
Let `s ⊆ R` be a set and `N ≤ M` be a submodule, then `s • N` is the smallest submodule containing
all `r • n` where `r ∈ s` and `n ∈ N`.
-/
@[instance_reducible]
/--
Definition of `pointwiseSetSMul` / `pointwiseSetSMul` 的定义

English:
definition pointwiseSetSMul
  signature: : SMul (Set S) (Submodule R M) where
  body: sInf { p | forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p }

scoped[Pointwise] attribute [instance] Submodule.pointwiseSetSMul

中文:
定义 pointwiseSetSMul
  签名: : SMul (Set S) (Submodule R M) where
  定义体: sInf { p | forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p }

scoped[Pointwise] attribute [instance] Submodule.pointwiseSetSMul
-/
protected def pointwiseSetSMul : SMul (Set S) (Submodule R M) where
  smul s N := sInf { p | forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p }

scoped[Pointwise] attribute [instance] Submodule.pointwiseSetSMul

variable (sR : Set R) (s : Set S) (N : Submodule R M)

/--
lemma `mem_set_smul_def` / 引理 `mem_set_smul_def`

English:
lemma mem_set_smul_def
  given: (x : M)
  proof: Iff.rfl

中文:
引理 mem_set_smul_def
  条件: (x : M)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_set_smul_def (x : M) :
    x in s • N ↔
    x in sInf { p : Submodule R M | forall ⦃r : S⦄ {n : M}, r in s -> n in N -> r • n in p } := Iff.rfl

variable {s N} in
@[aesop safe]
/--
lemma `mem_set_smul_of_mem_mem` / 引理 `mem_set_smul_of_mem_mem`

English:
lemma mem_set_smul_of_mem_mem
  given: {r : S} {m : M} (mem1 : r in s) (mem2 : m in N)
  proof: by
  rw [mem_set_smul_def]; rw [mem_sInf]
  exact fun _ h => h mem1 mem2

中文:
引理 mem_set_smul_of_mem_mem
  条件: {r : S} {m : M} (mem1 : r in s) (mem2 : m in N)
  证明: by
  rw [mem_set_smul_def]; rw [mem_sInf]
  exact fun _ h => h mem1 mem2

Depends on / 依赖: mem_sInf, mem_set_smul_def
-/
lemma mem_set_smul_of_mem_mem {r : S} {m : M} (mem1 : r in s) (mem2 : m in N) :
    r • m in s • N := by
  rw [mem_set_smul_def]; rw [mem_sInf]
  exact fun _ h => h mem1 mem2

/--
lemma `set_smul_le` / 引理 `set_smul_le`

English:
lemma set_smul_le
  statement: (p : Submodule R M)
  proof: sInf_le closed_under_smul

中文:
引理 set_smul_le
  结论: (p : Submodule R M)
  证明: sInf_le closed_under_smul

Depends on / 依赖: closed_under_smul, sInf_le
-/
lemma set_smul_le (p : Submodule R M)
    (closed_under_smul : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p) :
    s • N <= p :=
  sInf_le closed_under_smul

/--
lemma `set_smul_le_iff` / 引理 `set_smul_le_iff`

English:
lemma set_smul_le_iff
  given: (p : Submodule R M)
  proof: by
  fconstructor
  · intro h r n hr hn
exact h mem_set_smul_of_mem_mem hr hn
  · apply set_smul_le

中文:
引理 set_smul_le_iff
  条件: (p : Submodule R M)
  证明: by
  fconstructor
  · intro h r n hr hn
exact h mem_set_smul_of_mem_mem hr hn
  · apply set_smul_le

Depends on / 依赖: fconstructor, mem_set_smul_of_mem_mem, set_smul_le
-/
lemma set_smul_le_iff (p : Submodule R M) :
    s • N <= p ↔
    forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p := by
  fconstructor
  · intro h r n hr hn
exact h mem_set_smul_of_mem_mem hr hn
  · apply set_smul_le

/--
lemma `set_smul_eq_of_le` / 引理 `set_smul_eq_of_le`

English:
lemma set_smul_eq_of_le
  statement: (p : Submodule R M)
  proof: le_antisymm (set_smul_le s N p closed_under_smul) le

中文:
引理 set_smul_eq_of_le
  结论: (p : Submodule R M)
  证明: le_antisymm (set_smul_le s N p closed_under_smul) le

Depends on / 依赖: closed_under_smul, le_antisymm, set_smul_le
-/
lemma set_smul_eq_of_le (p : Submodule R M)
    (closed_under_smul : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p)
    (le : p <= s • N) :
    s • N = p :=
  le_antisymm (set_smul_le s N p closed_under_smul) le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CovariantClass (Set S) (Submodule R M) HSMul.hSMul LE.le
  body: ⟨fun _ _ _ le => set_smul_le _ _ _ fun _ _ hr hm => mem_set_smul_of_mem_mem (mem1 := hr)
    (mem2 := le hm)⟩

中文:
实例 :
  签名: CovariantClass (Set S) (Submodule R M) HSMul.hSMul LE.le
  定义体: ⟨fun _ _ _ le => set_smul_le _ _ _ fun _ _ hr hm => mem_set_smul_of_mem_mem (mem1 := hr)
    (mem2 := le hm)⟩

Depends on / 依赖: mem_set_smul_of_mem_mem, set_smul_le
-/
instance : CovariantClass (Set S) (Submodule R M) HSMul.hSMul LE.le :=
  ⟨fun _ _ _ le => set_smul_le _ _ _ fun _ _ hr hm => mem_set_smul_of_mem_mem (mem1 := hr)
    (mem2 := le hm)⟩

/--
lemma `set_smul_mono_left` / 引理 `set_smul_mono_left`

English:
lemma set_smul_mono_left
  given: {s t : Set S} (le : s <= t)
  proof: set_smul_le _ _ _ fun _ _ hr hm => mem_set_smul_of_mem_mem (mem1 := le hr)
    (mem2 := hm)

中文:
引理 set_smul_mono_left
  条件: {s t : Set S} (le : s <= t)
  证明: set_smul_le _ _ _ fun _ _ hr hm => mem_set_smul_of_mem_mem (mem1 := le hr)
    (mem2 := hm)

Depends on / 依赖: mem_set_smul_of_mem_mem, set_smul_le
-/
lemma set_smul_mono_left {s t : Set S} (le : s <= t) :
    s • N <= t • N :=
  set_smul_le _ _ _ fun _ _ hr hm => mem_set_smul_of_mem_mem (mem1 := le hr)
    (mem2 := hm)

/--
lemma `set_smul_le_of_le_le` / 引理 `set_smul_le_of_le_le`

English:
lemma set_smul_le_of_le_le
  statement: {s t : Set S} {p q : Submodule R M}
  proof: le_trans (set_smul_mono_left _ le_set) smul_mono_right _ le_submodule

中文:
引理 set_smul_le_of_le_le
  结论: {s t : Set S} {p q : Submodule R M}
  证明: le_trans (set_smul_mono_left _ le_set) smul_mono_right _ le_submodule

Depends on / 依赖: le_set, le_submodule, le_trans, set_smul_mono_left, smul_mono_right
-/
lemma set_smul_le_of_le_le {s t : Set S} {p q : Submodule R M}
    (le_set : s <= t) (le_submodule : p <= q) : s • p <= t • q :=
le_trans (set_smul_mono_left _ le_set) smul_mono_right _ le_submodule

/--
lemma `set_smul_eq_iSup` / 引理 `set_smul_eq_iSup`

English:
lemma set_smul_eq_iSup
  given: [SMulCommClass S R M] (s : Set S) (N : Submodule R M)
  proof: by
  refine Eq.trans (congrArg sInf ?_) csInf_Ici
  simp_rw [← Set.Ici_def, iSup_le_iff, @forall_comm M]
  exact Set.ext fun _ => forall₂_congr (fun _ _ => Iff.symm map_le_iff_le_comap)

中文:
引理 set_smul_eq_iSup
  条件: [SMulCommClass S R M] (s : Set S) (N : Submodule R M)
  证明: by
  refine Eq.trans (congrArg sInf ?_) csInf_Ici
  simp_rw [← Set.Ici_def, iSup_le_iff, @forall_comm M]
  exact Set.ext fun _ => forall₂_congr (fun _ _ => Iff.symm map_le_iff_le_comap)

Depends on / 依赖: Eq.trans, Ici_def, Iff.symm, Set.Ici_def, Set.ext, csInf_Ici, forall_comm, iSup_le_iff, map_le_iff_le_comap, simp_rw
-/
lemma set_smul_eq_iSup [SMulCommClass S R M] (s : Set S) (N : Submodule R M) :
    s • N = ⨆ (a in s), a • N := by
  refine Eq.trans (congrArg sInf ?_) csInf_Ici
  simp_rw [← Set.Ici_def, iSup_le_iff, @forall_comm M]
  exact Set.ext fun _ => forall₂_congr (fun _ _ => Iff.symm map_le_iff_le_comap)

variable {s N} in
/--
Induction principle for set acting on submodules. To prove `P` holds for all `s • N`, it is enough
to prove:
- for all `r ∈ s` and `n ∈ N`, `P (r • n)`;
- for all `r` and `m ∈ s • N`, `P (r • n)`;
- for all `m₁, m₂`, `P m₁` and `P m₂` implies `P (m₁ + m₂)`;
- `P 0`.

To invoke this induction principle, use `induction x, hx using Submodule.set_smul_inductionOn` where
`x : M` and `hx : x ∈ s • N`
-/
@[elab_as_elim]
/--
lemma `set_smul_inductionOn` / 引理 `set_smul_inductionOn`

English:
lemma set_smul_inductionOn
  statement: {motive : (x : M) -> (_ : x in s • N) -> Prop}
  proof: let ⟨_, h⟩ := set_smul_le s N
    { carrier := { m | exists (mem : m in s • N), motive m mem },
      zero_mem' := ⟨Submodule.zero_mem _, zero⟩
      add_mem' := fun ⟨mem, h⟩ ⟨mem', h'⟩ => ⟨_, add mem mem' h h'⟩
      smul_mem' := fun r _ ⟨mem, h⟩ => ⟨_, smul₁ r mem h⟩ }
    (fun _ _ mem mem' => ⟨me

中文:
引理 set_smul_inductionOn
  结论: {motive : (x : M) -> (_ : x in s • N) -> 命题}
  证明: let ⟨_, h⟩ := set_smul_le s N
    { carrier := { m | exists (mem : m in s • N), motive m mem },
      zero_mem' := ⟨Submodule.zero_mem _, zero⟩
      add_mem' := fun ⟨mem, h⟩ ⟨mem', h'⟩ => ⟨_, add mem mem' h h'⟩
      smul_mem' := fun r _ ⟨mem, h⟩ => ⟨_, smul₁ r mem h⟩ }
    (fun _ _ mem mem' => ⟨me

Depends on / 依赖: Submodule, Submodule.zero_mem, add_mem, carrier, mem_set_smul_of_mem_mem, motive, set_smul_le, smul_mem, zero_mem
-/
lemma set_smul_inductionOn {motive : (x : M) -> (_ : x in s • N) -> Prop}
    (x : M)
    (hx : x in s • N)
    (smul₀ : forall ⦃r : S⦄ ⦃n : M⦄ (mem₁ : r in s) (mem₂ : n in N),
      motive (r • n) (mem_set_smul_of_mem_mem mem₁ mem₂))
    (smul₁ : forall (r : R) ⦃m : M⦄ (mem : m in s • N),
      motive m mem -> motive (r • m) (Submodule.smul_mem _ r mem)) --
    (add : forall ⦃m₁ m₂ : M⦄ (mem₁ : m₁ in s • N) (mem₂ : m₂ in s • N),
      motive m₁ mem₁ -> motive m₂ mem₂ -> motive (m₁ + m₂) (Submodule.add_mem _ mem₁ mem₂))
    (zero : motive 0 (Submodule.zero_mem _)) :
    motive x hx :=
  let ⟨_, h⟩ := set_smul_le s N
    { carrier := { m | exists (mem : m in s • N), motive m mem },
      zero_mem' := ⟨Submodule.zero_mem _, zero⟩
      add_mem' := fun ⟨mem, h⟩ ⟨mem', h'⟩ => ⟨_, add mem mem' h h'⟩
      smul_mem' := fun r _ ⟨mem, h⟩ => ⟨_, smul₁ r mem h⟩ }
    (fun _ _ mem mem' => ⟨mem_set_smul_of_mem_mem mem mem', smul₀ mem mem'⟩) hx
  h

/--
lemma `empty_set_smul` / 引理 `empty_set_smul`

English:
lemma empty_set_smul
  statement: (∅ : Set S) • N = ⊥
  proof: by
  ext
  fconstructor
  · intro hx
    rw [mem_set_smul_def]; rw [Submodule.mem_sInf] at hx
    exact hx ⊥ (fun r _ hr => hr.elim)
  · rintro rfl; exact Submodule.zero_mem _

中文:
引理 empty_set_smul
  结论: (∅ : Set S) • N = ⊥
  证明: by
  ext
  fconstructor
  · intro hx
    rw [mem_set_smul_def]; rw [Submodule.mem_sInf] at hx
    exact hx ⊥ (fun r _ hr => hr.elim)
  · rintro rfl; exact Submodule.zero_mem _
-/
@[simp] lemma empty_set_smul : (∅ : Set S) • N = ⊥ := by
  ext
  fconstructor
  · intro hx
    rw [mem_set_smul_def]; rw [Submodule.mem_sInf] at hx
    exact hx ⊥ (fun r _ hr => hr.elim)
  · rintro rfl; exact Submodule.zero_mem _

/--
lemma `set_smul_bot` / 引理 `set_smul_bot`

English:
lemma set_smul_bot
  statement: s • (⊥ : Submodule R M) = ⊥
  proof: eq_bot_iff.mpr fun x hx => by induction x, hx using set_smul_inductionOn <;> aesop

中文:
引理 set_smul_bot
  结论: s • (⊥ : Submodule R M) = ⊥
  证明: eq_bot_iff.mpr fun x hx => by induction x, hx using set_smul_inductionOn <;> aesop
-/
@[simp] lemma set_smul_bot : s • (⊥ : Submodule R M) = ⊥ :=
  eq_bot_iff.mpr fun x hx => by induction x, hx using set_smul_inductionOn <;> aesop

/--
lemma `singleton_set_smul` / 引理 `singleton_set_smul`

English:
lemma singleton_set_smul
  given: [SMulCommClass S R M] (r : S)
  statement: ({r} : Set S) • N = r • N
  proof: by
  apply set_smul_eq_of_le
  · rintro _ m rfl hm; exact ⟨m, hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    rw [mem_set_smul_def]; rw [Submodule.mem_sInf]
    intro _ hp; exact hp rfl hm

中文:
引理 singleton_set_smul
  条件: [SMulCommClass S R M] (r : S)
  结论: ({r} : Set S) • N = r • N
  证明: by
  apply set_smul_eq_of_le
  · rintro _ m rfl hm; exact ⟨m, hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    rw [mem_set_smul_def]; rw [Submodule.mem_sInf]
    intro _ hp; exact hp rfl hm

Depends on / 依赖: Submodule, Submodule.mem_sInf, mem_sInf, mem_set_smul_def, set_smul_eq_of_le
-/
lemma singleton_set_smul [SMulCommClass S R M] (r : S) : ({r} : Set S) • N = r • N := by
  apply set_smul_eq_of_le
  · rintro _ m rfl hm; exact ⟨m, hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    rw [mem_set_smul_def]; rw [Submodule.mem_sInf]
    intro _ hp; exact hp rfl hm

/--
lemma `mem_singleton_set_smul` / 引理 `mem_singleton_set_smul`

English:
lemma mem_singleton_set_smul
  given: [SMulCommClass R S M] (r : S) (x : M)
  proof: by
  fconstructor
  · intro hx
    induction x, hx using Submodule.set_smul_inductionOn with
    | smul₀ => aesop
    | @smul₁ t n mem h =>
      rcases h with ⟨n, hn, rfl⟩
      exact ⟨t • n, by aesop, smul_comm _ _ _⟩
    | add mem₁ mem₂ h₁ h₂ =>
      rcases h₁ with ⟨m₁, h₁, rfl⟩
      rcases h₂ 

中文:
引理 mem_singleton_set_smul
  条件: [SMulCommClass R S M] (r : S) (x : M)
  证明: by
  fconstructor
  · intro hx
    induction x, hx using Submodule.set_smul_inductionOn with
    | smul₀ => aesop
    | @smul₁ t n mem h =>
      rcases h with ⟨n, hn, rfl⟩
      exact ⟨t • n, by aesop, smul_comm _ _ _⟩
    | add mem₁ mem₂ h₁ h₂ =>
      rcases h₁ with ⟨m₁, h₁, rfl⟩
      rcases h₂ 

Depends on / 依赖: Submodule, Submodule.add_mem, Submodule.set_smul_inductionOn, Submodule.zero_mem, add_mem, fconstructor, set_smul_inductionOn, smul_comm, zero_mem
-/
lemma mem_singleton_set_smul [SMulCommClass R S M] (r : S) (x : M) :
    x in ({r} : Set S) • N ↔ exists (m : M), m in N ∧ x = r • m := by
  fconstructor
  · intro hx
    induction x, hx using Submodule.set_smul_inductionOn with
    | smul₀ => aesop
    | @smul₁ t n mem h =>
      rcases h with ⟨n, hn, rfl⟩
      exact ⟨t • n, by aesop, smul_comm _ _ _⟩
    | add mem₁ mem₂ h₁ h₂ =>
      rcases h₁ with ⟨m₁, h₁, rfl⟩
      rcases h₂ with ⟨m₂, h₂, rfl⟩
      exact ⟨m₁ + m₂, Submodule.add_mem _ h₁ h₂, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  · aesop

/--
lemma `smul_inductionOn_pointwise` / 引理 `smul_inductionOn_pointwise`

English:
lemma smul_inductionOn_pointwise
  statement: [SMulCommClass S R M] {a : S} {p : (x : M) -> x in a • N -> Prop}
  proof: by
  simp_all only [← Submodule.singleton_set_smul]
  let p' (x : M) (hx : x in ({a} : Set S) • N) : Prop :=
    p x (by rwa [← Submodule.singleton_set_smul])
  refine Submodule.set_smul_inductionOn (motive := p') _ (N.singleton_set_smul a ▸ hx)
      (fun r n hr hn => ?_) smul₁ add zero
  · push _ 

中文:
引理 smul_inductionOn_pointwise
  结论: [SMulCommClass S R M] {a : S} {p : (x : M) -> x in a • N -> 命题}
  证明: by
  simp_all only [← Submodule.singleton_set_smul]
  let p' (x : M) (hx : x in ({a} : Set S) • N) : Prop :=
    p x (by rwa [← Submodule.singleton_set_smul])
  refine Submodule.set_smul_inductionOn (motive := p') _ (N.singleton_set_smul a ▸ hx)
      (fun r n hr hn => ?_) smul₁ add zero
  · push _ 

Depends on / 依赖: N.singleton_set_smul, Submodule, Submodule.set_smul_inductionOn, Submodule.singleton_set_smul, motive, set_smul_inductionOn, singleton_set_smul
-/
lemma smul_inductionOn_pointwise [SMulCommClass S R M] {a : S} {p : (x : M) -> x in a • N -> Prop}
    (smul₀ : forall (s : M) (hs : s in N), p (a • s) (Submodule.smul_mem_pointwise_smul _ _ _ hs))
    (smul₁ : forall (r : R) (m : M) (mem : m in a • N), p m mem -> p (r • m) (Submodule.smul_mem _ _ mem))
    (add : forall (x y : M) (hx : x in a • N) (hy : y in a • N),
      p x hx -> p y hy -> p (x + y) (Submodule.add_mem _ hx hy))
    (zero : p 0 (Submodule.zero_mem _)) {x : M} (hx : x in a • N) :
    p x hx := by
  simp_all only [← Submodule.singleton_set_smul]
  let p' (x : M) (hx : x in ({a} : Set S) • N) : Prop :=
    p x (by rwa [← Submodule.singleton_set_smul])
  refine Submodule.set_smul_inductionOn (motive := p') _ (N.singleton_set_smul a ▸ hx)
      (fun r n hr hn => ?_) smul₁ add zero
  · push _ in _ at hr
    subst hr
    exact smul₀ n hn

/--
lemma `sup_set_smul` / 引理 `sup_set_smul`

English:
lemma sup_set_smul
  given: (s t : Set S)
  proof: set_smul_eq_of_le _ _ _
    (by rintro _ _ (hr | hr) hn
        · exact Submodule.mem_sup_left (mem_set_smul_of_mem_mem hr hn)
        · exact Submodule.mem_sup_right (mem_set_smul_of_mem_mem hr hn))
    (sup_le (set_smul_mono_left _ le_sup_left) (set_smul_mono_left _ le_sup_right))

中文:
引理 sup_set_smul
  条件: (s t : Set S)
  证明: set_smul_eq_of_le _ _ _
    (by rintro _ _ (hr | hr) hn
        · exact Submodule.mem_sup_left (mem_set_smul_of_mem_mem hr hn)
        · exact Submodule.mem_sup_right (mem_set_smul_of_mem_mem hr hn))
    (sup_le (set_smul_mono_left _ le_sup_left) (set_smul_mono_left _ le_sup_right))

Depends on / 依赖: Submodule, Submodule.mem_sup_left, Submodule.mem_sup_right, le_sup_left, le_sup_right, mem_set_smul_of_mem_mem, mem_sup_left, mem_sup_right, set_smul_eq_of_le, set_smul_mono_left, sup_le
-/
lemma sup_set_smul (s t : Set S) :
    (s ⊔ t) • N = s • N ⊔ t • N :=
  set_smul_eq_of_le _ _ _
    (by rintro _ _ (hr | hr) hn
        · exact Submodule.mem_sup_left (mem_set_smul_of_mem_mem hr hn)
        · exact Submodule.mem_sup_right (mem_set_smul_of_mem_mem hr hn))
    (sup_le (set_smul_mono_left _ le_sup_left) (set_smul_mono_left _ le_sup_right))

end DistribMulAction

section Group

variable {R G M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Group G] [DistribMulAction G M] [SMulCommClass G R M]
    {S : Submodule R M}

open MulAction

/--
lemma `stabilizer_coe` / 引理 `stabilizer_coe`

English:
lemma stabilizer_coe
  proof: by
  ext
  rw [mem_stabilizer_iff]; rw [SetLike.ext'_iff]; rw [coe_pointwise_smul]; rw [← mem_stabilizer_iff]

中文:
引理 stabilizer_coe
  证明: by
  ext
  rw [mem_stabilizer_iff]; rw [SetLike.ext'_iff]; rw [coe_pointwise_smul]; rw [← mem_stabilizer_iff]

Depends on / 依赖: SetLike, SetLike.ext, _iff, coe_pointwise_smul, mem_stabilizer_iff
-/
lemma stabilizer_coe :
    stabilizer G S = stabilizer G (S : Set M) := by
  ext
  rw [mem_stabilizer_iff]; rw [SetLike.ext'_iff]; rw [coe_pointwise_smul]; rw [← mem_stabilizer_iff]

/--
theorem `mem_stabilizer_submodule_iff_map_eq` / 定理 `mem_stabilizer_submodule_iff_map_eq`

English:
theorem mem_stabilizer_submodule_iff_map_eq
  given: {e : G}
  proof: by
  rfl

中文:
定理 mem_stabilizer_submodule_iff_map_eq
  条件: {e : G}
  证明: by
  rfl
-/
theorem mem_stabilizer_submodule_iff_map_eq {e : G} :
    e in stabilizer G S ↔ S.map (DistribSMul.toLinearMap R M e) = S := by
  rfl

end Group

end Submodule
