/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise

/-!
# Subgroups in a group with zero
-/

@[expose] public section

assert_not_exists Ring

open Set
open scoped Pointwise

variable {G₀ G M A : Type*}

namespace Subgroup
section GroupWithZero
variable [GroupWithZero G₀] [Group G] [MulDistribMulAction G₀ G] {S T : Subgroup G} {a : G₀}

@[simp]
/--
lemma `smul_mem_pointwise_smul_iff₀` / 引理 `smul_mem_pointwise_smul_iff₀`

English:
lemma smul_mem_pointwise_smul_iff₀
  given: (ha : a != 0) (S : Subgroup G) (x : G)
  proof: smul_mem_smul_set_iff₀ ha (S : Set G) x

中文:
引理 smul_mem_pointwise_smul_iff₀
  条件: (ha : a != 0) (S : Subgroup G) (x : G)
  证明: smul_mem_smul_set_iff₀ ha (S : Set G) x
-/
lemma smul_mem_pointwise_smul_iff₀ (ha : a != 0) (S : Subgroup G) (x : G) :
    a • x in a • S ↔ x in S :=
  smul_mem_smul_set_iff₀ ha (S : Set G) x

/--
lemma `mem_pointwise_smul_iff_inv_smul_mem₀` / 引理 `mem_pointwise_smul_iff_inv_smul_mem₀`

English:
lemma mem_pointwise_smul_iff_inv_smul_mem₀
  given: (ha : a != 0) (S : Subgroup G) (x : G)
  proof: mem_smul_set_iff_inv_smul_mem₀ ha (S : Set G) x

中文:
引理 mem_pointwise_smul_iff_inv_smul_mem₀
  条件: (ha : a != 0) (S : Subgroup G) (x : G)
  证明: mem_smul_set_iff_inv_smul_mem₀ ha (S : Set G) x
-/
lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a != 0) (S : Subgroup G) (x : G) :
    x in a • S ↔ a⁻¹ • x in S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set G) x

/--
lemma `mem_inv_pointwise_smul_iff₀` / 引理 `mem_inv_pointwise_smul_iff₀`

English:
lemma mem_inv_pointwise_smul_iff₀
  given: (ha : a != 0) (S : Subgroup G) (x : G)
  proof: mem_inv_smul_set_iff₀ ha (S : Set G) x

@[simp]

中文:
引理 mem_inv_pointwise_smul_iff₀
  条件: (ha : a != 0) (S : Subgroup G) (x : G)
  证明: mem_inv_smul_set_iff₀ ha (S : Set G) x

@[simp]
-/
lemma mem_inv_pointwise_smul_iff₀ (ha : a != 0) (S : Subgroup G) (x : G) :
    x in a⁻¹ • S ↔ a • x in S :=
  mem_inv_smul_set_iff₀ ha (S : Set G) x

@[simp]
/--
lemma `pointwise_smul_le_pointwise_smul_iff₀` / 引理 `pointwise_smul_le_pointwise_smul_iff₀`

English:
lemma pointwise_smul_le_pointwise_smul_iff₀
  given: (ha : a != 0)
  statement: a • S <= a • T ↔ S <= T
  proof: smul_set_subset_smul_set_iff₀ ha

中文:
引理 pointwise_smul_le_pointwise_smul_iff₀
  条件: (ha : a != 0)
  结论: a • S <= a • T ↔ S <= T
  证明: smul_set_subset_smul_set_iff₀ ha
-/
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a != 0) : a • S <= a • T ↔ S <= T :=
  smul_set_subset_smul_set_iff₀ ha

/--
lemma `pointwise_smul_le_iff₀` / 引理 `pointwise_smul_le_iff₀`

English:
lemma pointwise_smul_le_iff₀
  given: (ha : a != 0)
  statement: a • S <= T ↔ S <= a⁻¹ • T
  proof: smul_set_subset_iff₀ ha

中文:
引理 pointwise_smul_le_iff₀
  条件: (ha : a != 0)
  结论: a • S <= T ↔ S <= a⁻¹ • T
  证明: smul_set_subset_iff₀ ha
-/
lemma pointwise_smul_le_iff₀ (ha : a != 0) : a • S <= T ↔ S <= a⁻¹ • T := smul_set_subset_iff₀ ha
/--
lemma `le_pointwise_smul_iff₀` / 引理 `le_pointwise_smul_iff₀`

English:
lemma le_pointwise_smul_iff₀
  given: (ha : a != 0)
  statement: S <= a • T ↔ a⁻¹ • S <= T
  proof: subset_smul_set_iff₀ ha

中文:
引理 le_pointwise_smul_iff₀
  条件: (ha : a != 0)
  结论: S <= a • T ↔ a⁻¹ • S <= T
  证明: subset_smul_set_iff₀ ha
-/
lemma le_pointwise_smul_iff₀ (ha : a != 0) : S <= a • T ↔ a⁻¹ • S <= T := subset_smul_set_iff₀ ha

end GroupWithZero
end Subgroup

namespace AddSubgroup
section Monoid
variable [Monoid M] [AddGroup A] [DistribMulAction M A] {a : M}

/-- The action on an additive subgroup corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseMulAction` / `pointwiseMulAction` 的定义

English:
definition pointwiseMulAction
  signature: : MulAction M (AddSubgroup A) where
  body: S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_mul _ _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Ad

中文:
定义 pointwiseMulAction
  签名: : MulAction M (AddSubgroup A) where
  定义体: S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_mul _ _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Ad
-/
protected def pointwiseMulAction : MulAction M (AddSubgroup A) where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_mul _ _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] AddSubgroup.pointwiseMulAction

/--
lemma `pointwise_smul_def` / 引理 `pointwise_smul_def`

English:
lemma pointwise_smul_def
  given: (S : AddSubgroup A)
  proof: rfl

@[simp, norm_cast]

中文:
引理 pointwise_smul_def
  条件: (S : AddSubgroup A)
  证明: rfl

@[simp, norm_cast]
-/
lemma pointwise_smul_def (S : AddSubgroup A) :
    a • S = S.map (DistribMulAction.toAddMonoidEnd _ _ a) :=
  rfl

@[simp, norm_cast]
/--
lemma `coe_pointwise_smul` / 引理 `coe_pointwise_smul`

English:
lemma coe_pointwise_smul
  given: (a : M) (S : AddSubgroup A)
  statement: ↑(a • S) = a • (S : Set A)
  proof: rfl

@[simp]

中文:
引理 coe_pointwise_smul
  条件: (a : M) (S : AddSubgroup A)
  结论: ↑(a • S) = a • (S : Set A)
  证明: rfl

@[simp]
-/
lemma coe_pointwise_smul (a : M) (S : AddSubgroup A) : ↑(a • S) = a • (S : Set A) :=
  rfl

@[simp]
/--
lemma `pointwise_smul_toAddSubmonoid` / 引理 `pointwise_smul_toAddSubmonoid`

English:
lemma pointwise_smul_toAddSubmonoid
  given: (a : M) (S : AddSubgroup A)
  proof: rfl

中文:
引理 pointwise_smul_toAddSubmonoid
  条件: (a : M) (S : AddSubgroup A)
  证明: rfl
-/
lemma pointwise_smul_toAddSubmonoid (a : M) (S : AddSubgroup A) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl

/--
lemma `smul_mem_pointwise_smul` / 引理 `smul_mem_pointwise_smul`

English:
lemma smul_mem_pointwise_smul
  given: (m : A) (a : M) (S : AddSubgroup A)
  statement: m in S -> a • m in a • S
  proof: (Set.smul_mem_smul_set : _ -> _ in a • (S : Set A))

中文:
引理 smul_mem_pointwise_smul
  条件: (m : A) (a : M) (S : AddSubgroup A)
  结论: m in S -> a • m in a • S
  证明: (Set.smul_mem_smul_set : _ -> _ in a • (S : Set A))

Depends on / 依赖: Set.smul_mem_smul_set, smul_mem_smul_set
-/
lemma smul_mem_pointwise_smul (m : A) (a : M) (S : AddSubgroup A) : m in S -> a • m in a • S :=
  (Set.smul_mem_smul_set : _ -> _ in a • (S : Set A))

/--
lemma `mem_smul_pointwise_iff_exists` / 引理 `mem_smul_pointwise_iff_exists`

English:
lemma mem_smul_pointwise_iff_exists
  given: (m : A) (a : M) (S : AddSubgroup A)
  proof: (Set.mem_smul_set : m in a • (S : Set A) ↔ _)

中文:
引理 mem_smul_pointwise_iff_exists
  条件: (m : A) (a : M) (S : AddSubgroup A)
  证明: (Set.mem_smul_set : m in a • (S : Set A) ↔ _)

Depends on / 依赖: Set.mem_smul_set, mem_smul_set
-/
lemma mem_smul_pointwise_iff_exists (m : A) (a : M) (S : AddSubgroup A) :
    m in a • S ↔ exists s : A, s in S ∧ a • s = m :=
  (Set.mem_smul_set : m in a • (S : Set A) ↔ _)

/--
Instance `pointwise_isCentralScalar` / 实例 `pointwise_isCentralScalar`

English:
instance pointwise_isCentralScalar
  signature: [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A]
  body: ⟨fun _ S => (congr_arg fun f => S.map f) AddMonoidHom.ext op_smul_eq_smul _⟩

中文:
实例 pointwise_isCentralScalar
  签名: [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A]
  定义体: ⟨fun _ S => (congr_arg fun f => S.map f) AddMonoidHom.ext op_smul_eq_smul _⟩

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, S.map, congr_arg, op_smul_eq_smul
-/
instance pointwise_isCentralScalar [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A] :
    IsCentralScalar M (AddSubgroup A) :=
⟨fun _ S => (congr_arg fun f => S.map f) AddMonoidHom.ext op_smul_eq_smul _⟩

-- TODO: Check that these lemmas are useful and uncomment.
-- @[simp]
-- lemma smul_bot (m : M) : m • (⊥ : AddSubgroup A) = ⊥ := map_bot _

-- lemma smul_sup (m : M) (S T : AddSubgroup A) : m • (S ⊔ T) = m • S ⊔ m • T := map_sup _ _ _

-- @[simp]
-- lemma smul_closure (m : M) (s : Set A) : m • closure s = closure (m • s) :=
-- AddMonoidHom.map_closure ..

scoped[Pointwise] attribute [instance] AddSubgroup.pointwise_isCentralScalar

end Monoid

section Group
variable [Group G] [AddGroup A] [DistribMulAction G A] {S T : AddSubgroup A} {a : G} {x : A}

/--
lemma `smul_mem_pointwise_smul_iff` / 引理 `smul_mem_pointwise_smul_iff`

English:
lemma smul_mem_pointwise_smul_iff
  statement: a • x in a • S ↔ x in S
  proof: smul_mem_smul_set_iff

中文:
引理 smul_mem_pointwise_smul_iff
  结论: a • x in a • S ↔ x in S
  证明: smul_mem_smul_set_iff
-/
@[simp] lemma smul_mem_pointwise_smul_iff : a • x in a • S ↔ x in S := smul_mem_smul_set_iff

/--
lemma `mem_pointwise_smul_iff_inv_smul_mem` / 引理 `mem_pointwise_smul_iff_inv_smul_mem`

English:
lemma mem_pointwise_smul_iff_inv_smul_mem
  statement: x in a • S ↔ a⁻¹ • x in S
  proof: mem_smul_set_iff_inv_smul_mem

中文:
引理 mem_pointwise_smul_iff_inv_smul_mem
  结论: x in a • S ↔ a⁻¹ • x in S
  证明: mem_smul_set_iff_inv_smul_mem

Depends on / 依赖: mem_smul_set_iff_inv_smul_mem
-/
lemma mem_pointwise_smul_iff_inv_smul_mem : x in a • S ↔ a⁻¹ • x in S :=
  mem_smul_set_iff_inv_smul_mem

/--
lemma `mem_inv_pointwise_smul_iff` / 引理 `mem_inv_pointwise_smul_iff`

English:
lemma mem_inv_pointwise_smul_iff
  statement: x in a⁻¹ • S ↔ a • x in S
  proof: mem_inv_smul_set_iff

@[simp]

中文:
引理 mem_inv_pointwise_smul_iff
  结论: x in a⁻¹ • S ↔ a • x in S
  证明: mem_inv_smul_set_iff

@[simp]

Depends on / 依赖: mem_inv_smul_set_iff
-/
lemma mem_inv_pointwise_smul_iff : x in a⁻¹ • S ↔ a • x in S := mem_inv_smul_set_iff

@[simp]
/--
lemma `pointwise_smul_le_pointwise_smul_iff` / 引理 `pointwise_smul_le_pointwise_smul_iff`

English:
lemma pointwise_smul_le_pointwise_smul_iff
  statement: a • S <= a • T ↔ S <= T
  proof: smul_set_subset_smul_set_iff

中文:
引理 pointwise_smul_le_pointwise_smul_iff
  结论: a • S <= a • T ↔ S <= T
  证明: smul_set_subset_smul_set_iff

Depends on / 依赖: smul_set_subset_smul_set_iff
-/
lemma pointwise_smul_le_pointwise_smul_iff : a • S <= a • T ↔ S <= T := smul_set_subset_smul_set_iff

/--
lemma `pointwise_smul_le_iff` / 引理 `pointwise_smul_le_iff`

English:
lemma pointwise_smul_le_iff
  statement: a • S <= T ↔ S <= a⁻¹ • T
  proof: smul_set_subset_iff_subset_inv_smul_set

中文:
引理 pointwise_smul_le_iff
  结论: a • S <= T ↔ S <= a⁻¹ • T
  证明: smul_set_subset_iff_subset_inv_smul_set

Depends on / 依赖: smul_set_subset_iff_subset_inv_smul_set
-/
lemma pointwise_smul_le_iff : a • S <= T ↔ S <= a⁻¹ • T := smul_set_subset_iff_subset_inv_smul_set
/--
lemma `le_pointwise_smul_iff` / 引理 `le_pointwise_smul_iff`

English:
lemma le_pointwise_smul_iff
  statement: S <= a • T ↔ a⁻¹ • S <= T
  proof: subset_smul_set_iff

中文:
引理 le_pointwise_smul_iff
  结论: S <= a • T ↔ a⁻¹ • S <= T
  证明: subset_smul_set_iff

Depends on / 依赖: subset_smul_set_iff
-/
lemma le_pointwise_smul_iff : S <= a • T ↔ a⁻¹ • S <= T := subset_smul_set_iff

end Group

section GroupWithZero
variable [GroupWithZero G₀] [AddGroup A] [DistribMulAction G₀ A] {S T : AddSubgroup A} {a : G₀}

@[simp]
/--
lemma `smul_mem_pointwise_smul_iff₀` / 引理 `smul_mem_pointwise_smul_iff₀`

English:
lemma smul_mem_pointwise_smul_iff₀
  given: (ha : a != 0) (S : AddSubgroup A) (x : A)
  proof: smul_mem_smul_set_iff₀ ha (S : Set A) x

中文:
引理 smul_mem_pointwise_smul_iff₀
  条件: (ha : a != 0) (S : AddSubgroup A) (x : A)
  证明: smul_mem_smul_set_iff₀ ha (S : Set A) x
-/
lemma smul_mem_pointwise_smul_iff₀ (ha : a != 0) (S : AddSubgroup A) (x : A) :
    a • x in a • S ↔ x in S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x

/--
lemma `mem_pointwise_smul_iff_inv_smul_mem₀` / 引理 `mem_pointwise_smul_iff_inv_smul_mem₀`

English:
lemma mem_pointwise_smul_iff_inv_smul_mem₀
  given: (ha : a != 0) (S : AddSubgroup A) (x : A)
  proof: mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x

中文:
引理 mem_pointwise_smul_iff_inv_smul_mem₀
  条件: (ha : a != 0) (S : AddSubgroup A) (x : A)
  证明: mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x
-/
lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a != 0) (S : AddSubgroup A) (x : A) :
    x in a • S ↔ a⁻¹ • x in S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x

/--
lemma `mem_inv_pointwise_smul_iff₀` / 引理 `mem_inv_pointwise_smul_iff₀`

English:
lemma mem_inv_pointwise_smul_iff₀
  given: (ha : a != 0) (S : AddSubgroup A) (x : A)
  proof: mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]

中文:
引理 mem_inv_pointwise_smul_iff₀
  条件: (ha : a != 0) (S : AddSubgroup A) (x : A)
  证明: mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]
-/
lemma mem_inv_pointwise_smul_iff₀ (ha : a != 0) (S : AddSubgroup A) (x : A) :
    x in a⁻¹ • S ↔ a • x in S :=
  mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]
/--
lemma `pointwise_smul_le_pointwise_smul_iff₀` / 引理 `pointwise_smul_le_pointwise_smul_iff₀`

English:
lemma pointwise_smul_le_pointwise_smul_iff₀
  given: (ha : a != 0)
  statement: a • S <= a • T ↔ S <= T
  proof: smul_set_subset_smul_set_iff₀ ha

中文:
引理 pointwise_smul_le_pointwise_smul_iff₀
  条件: (ha : a != 0)
  结论: a • S <= a • T ↔ S <= T
  证明: smul_set_subset_smul_set_iff₀ ha
-/
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a != 0) : a • S <= a • T ↔ S <= T :=
  smul_set_subset_smul_set_iff₀ ha

/--
lemma `pointwise_smul_le_iff₀` / 引理 `pointwise_smul_le_iff₀`

English:
lemma pointwise_smul_le_iff₀
  given: (ha : a != 0)
  statement: a • S <= T ↔ S <= a⁻¹ • T
  proof: smul_set_subset_iff₀ ha

中文:
引理 pointwise_smul_le_iff₀
  条件: (ha : a != 0)
  结论: a • S <= T ↔ S <= a⁻¹ • T
  证明: smul_set_subset_iff₀ ha
-/
lemma pointwise_smul_le_iff₀ (ha : a != 0) : a • S <= T ↔ S <= a⁻¹ • T := smul_set_subset_iff₀ ha
/--
lemma `le_pointwise_smul_iff₀` / 引理 `le_pointwise_smul_iff₀`

English:
lemma le_pointwise_smul_iff₀
  given: (ha : a != 0)
  statement: S <= a • T ↔ a⁻¹ • S <= T
  proof: subset_smul_set_iff₀ ha

中文:
引理 le_pointwise_smul_iff₀
  条件: (ha : a != 0)
  结论: S <= a • T ↔ a⁻¹ • S <= T
  证明: subset_smul_set_iff₀ ha
-/
lemma le_pointwise_smul_iff₀ (ha : a != 0) : S <= a • T ↔ a⁻¹ • S <= T := subset_smul_set_iff₀ ha

end GroupWithZero
end AddSubgroup
