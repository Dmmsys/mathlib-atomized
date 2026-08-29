/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Submonoid.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set

/-!
# Submonoids in a group with zero
-/

@[expose] public section

assert_not_exists Ring

open Set
open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

namespace Submonoid
section GroupWithZero
variable [GroupWithZero G₀] [MulDistribMulAction G₀ M] {a : G₀}

@[simp]
/--
lemma `smul_mem_pointwise_smul_iff₀` / 引理 `smul_mem_pointwise_smul_iff₀`

English:
lemma smul_mem_pointwise_smul_iff₀
  given: (ha : a != 0) (S : Submonoid M) (x : M)
  proof: smul_mem_smul_set_iff₀ ha (S : Set M) x

中文:
引理 smul_mem_pointwise_smul_iff₀
  条件: (ha : a != 0) (S : Submonoid M) (x : M)
  证明: smul_mem_smul_set_iff₀ ha (S : Set M) x
-/
lemma smul_mem_pointwise_smul_iff₀ (ha : a != 0) (S : Submonoid M) (x : M) :
    a • x in a • S ↔ x in S :=
  smul_mem_smul_set_iff₀ ha (S : Set M) x

/--
lemma `mem_pointwise_smul_iff_inv_smul_mem₀` / 引理 `mem_pointwise_smul_iff_inv_smul_mem₀`

English:
lemma mem_pointwise_smul_iff_inv_smul_mem₀
  given: (ha : a != 0) (S : Submonoid M) (x : M)
  proof: mem_smul_set_iff_inv_smul_mem₀ ha (S : Set M) x

中文:
引理 mem_pointwise_smul_iff_inv_smul_mem₀
  条件: (ha : a != 0) (S : Submonoid M) (x : M)
  证明: mem_smul_set_iff_inv_smul_mem₀ ha (S : Set M) x
-/
lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a != 0) (S : Submonoid M) (x : M) :
    x in a • S ↔ a⁻¹ • x in S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set M) x

/--
lemma `mem_inv_pointwise_smul_iff₀` / 引理 `mem_inv_pointwise_smul_iff₀`

English:
lemma mem_inv_pointwise_smul_iff₀
  given: (ha : a != 0) (S : Submonoid M) (x : M)
  proof: mem_inv_smul_set_iff₀ ha (S : Set M) x

@[simp]

中文:
引理 mem_inv_pointwise_smul_iff₀
  条件: (ha : a != 0) (S : Submonoid M) (x : M)
  证明: mem_inv_smul_set_iff₀ ha (S : Set M) x

@[simp]
-/
lemma mem_inv_pointwise_smul_iff₀ (ha : a != 0) (S : Submonoid M) (x : M) :
    x in a⁻¹ • S ↔ a • x in S :=
  mem_inv_smul_set_iff₀ ha (S : Set M) x

@[simp]
/--
lemma `pointwise_smul_le_pointwise_smul_iff₀` / 引理 `pointwise_smul_le_pointwise_smul_iff₀`

English:
lemma pointwise_smul_le_pointwise_smul_iff₀
  given: (ha : a != 0) {S T : Submonoid M}
  proof: smul_set_subset_smul_set_iff₀ ha

中文:
引理 pointwise_smul_le_pointwise_smul_iff₀
  条件: (ha : a != 0) {S T : Submonoid M}
  证明: smul_set_subset_smul_set_iff₀ ha
-/
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a != 0) {S T : Submonoid M} :
    a • S <= a • T ↔ S <= T :=
  smul_set_subset_smul_set_iff₀ ha

/--
lemma `pointwise_smul_le_iff₀` / 引理 `pointwise_smul_le_iff₀`

English:
lemma pointwise_smul_le_iff₀
  given: (ha : a != 0) {S T : Submonoid M}
  statement: a • S <= T ↔ S <= a⁻¹ • T
  proof: smul_set_subset_iff₀ ha

中文:
引理 pointwise_smul_le_iff₀
  条件: (ha : a != 0) {S T : Submonoid M}
  结论: a • S <= T ↔ S <= a⁻¹ • T
  证明: smul_set_subset_iff₀ ha
-/
lemma pointwise_smul_le_iff₀ (ha : a != 0) {S T : Submonoid M} : a • S <= T ↔ S <= a⁻¹ • T :=
  smul_set_subset_iff₀ ha

/--
lemma `le_pointwise_smul_iff₀` / 引理 `le_pointwise_smul_iff₀`

English:
lemma le_pointwise_smul_iff₀
  given: (ha : a != 0) {S T : Submonoid M}
  statement: S <= a • T ↔ a⁻¹ • S <= T
  proof: subset_smul_set_iff₀ ha

中文:
引理 le_pointwise_smul_iff₀
  条件: (ha : a != 0) {S T : Submonoid M}
  结论: S <= a • T ↔ a⁻¹ • S <= T
  证明: subset_smul_set_iff₀ ha
-/
lemma le_pointwise_smul_iff₀ (ha : a != 0) {S T : Submonoid M} : S <= a • T ↔ a⁻¹ • S <= T :=
  subset_smul_set_iff₀ ha

end GroupWithZero
end Submonoid

namespace AddSubmonoid
section Monoid
variable [DistribMulAction M A]

/-- The action on an additive submonoid corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseMulAction` / `pointwiseMulAction` 的定义

English:
definition pointwiseMulAction
  signature: : MulAction M (AddSubmonoid A) where
  body: S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_mul _ _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Ad

中文:
定义 pointwiseMulAction
  签名: : MulAction M (AddSubmonoid A) where
  定义体: S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_mul _ _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Ad
-/
protected def pointwiseMulAction : MulAction M (AddSubmonoid A) where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_mul _ _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwiseMulAction

@[simp, norm_cast]
/--
lemma `coe_pointwise_smul` / 引理 `coe_pointwise_smul`

English:
lemma coe_pointwise_smul
  given: (m : M) (S : AddSubmonoid A)
  statement: ↑(m • S) = m • (S : Set A)
  proof: rfl

中文:
引理 coe_pointwise_smul
  条件: (m : M) (S : AddSubmonoid A)
  结论: ↑(m • S) = m • (S : Set A)
  证明: rfl
-/
lemma coe_pointwise_smul (m : M) (S : AddSubmonoid A) : ↑(m • S) = m • (S : Set A) := rfl

/--
lemma `smul_mem_pointwise_smul` / 引理 `smul_mem_pointwise_smul`

English:
lemma smul_mem_pointwise_smul
  given: (a : A) (m : M) (S : AddSubmonoid A)
  statement: a in S -> m • a in m • S
  proof: (Set.smul_mem_smul_set : _ -> _ in m • (S : Set A))

中文:
引理 smul_mem_pointwise_smul
  条件: (a : A) (m : M) (S : AddSubmonoid A)
  结论: a in S -> m • a in m • S
  证明: (Set.smul_mem_smul_set : _ -> _ in m • (S : Set A))

Depends on / 依赖: Set.smul_mem_smul_set, smul_mem_smul_set
-/
lemma smul_mem_pointwise_smul (a : A) (m : M) (S : AddSubmonoid A) : a in S -> m • a in m • S :=
  (Set.smul_mem_smul_set : _ -> _ in m • (S : Set A))

/--
lemma `mem_smul_pointwise_iff_exists` / 引理 `mem_smul_pointwise_iff_exists`

English:
lemma mem_smul_pointwise_iff_exists
  given: (a : A) (m : M) (S : AddSubmonoid A)
  proof: (Set.mem_smul_set : a in m • (S : Set A) ↔ _)

@[simp]

中文:
引理 mem_smul_pointwise_iff_exists
  条件: (a : A) (m : M) (S : AddSubmonoid A)
  证明: (Set.mem_smul_set : a in m • (S : Set A) ↔ _)

@[simp]

Depends on / 依赖: Set.mem_smul_set, mem_smul_set
-/
lemma mem_smul_pointwise_iff_exists (a : A) (m : M) (S : AddSubmonoid A) :
    a in m • S ↔ exists s : A, s in S ∧ m • s = a :=
  (Set.mem_smul_set : a in m • (S : Set A) ↔ _)

@[simp]
/--
lemma `smul_bot` / 引理 `smul_bot`

English:
lemma smul_bot
  given: (m : M)
  statement: m • (⊥ : AddSubmonoid A) = ⊥
  proof: map_bot _

中文:
引理 smul_bot
  条件: (m : M)
  结论: m • (⊥ : AddSubmonoid A) = ⊥
  证明: map_bot _

Depends on / 依赖: map_bot
-/
lemma smul_bot (m : M) : m • (⊥ : AddSubmonoid A) = ⊥ := map_bot _

/--
lemma `smul_sup` / 引理 `smul_sup`

English:
lemma smul_sup
  given: (m : M) (S T : AddSubmonoid A)
  statement: m • (S ⊔ T) = m • S ⊔ m • T
  proof: map_sup _ _ _

@[simp]

中文:
引理 smul_sup
  条件: (m : M) (S T : AddSubmonoid A)
  结论: m • (S ⊔ T) = m • S ⊔ m • T
  证明: map_sup _ _ _

@[simp]

Depends on / 依赖: map_sup
-/
lemma smul_sup (m : M) (S T : AddSubmonoid A) : m • (S ⊔ T) = m • S ⊔ m • T :=
  map_sup _ _ _

@[simp]
/--
lemma `smul_closure` / 引理 `smul_closure`

English:
lemma smul_closure
  given: (m : M) (s : Set A)
  statement: m • closure s = closure (m • s)
  proof: AddMonoidHom.map_mclosure _ _

中文:
引理 smul_closure
  条件: (m : M) (s : Set A)
  结论: m • closure s = closure (m • s)
  证明: AddMonoidHom.map_mclosure _ _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_mclosure, imageToKernel, infer_instance, map_mclosure
-/
lemma smul_closure (m : M) (s : Set A) : m • closure s = closure (m • s) :=
  AddMonoidHom.map_mclosure _ _

/--
lemma `pointwise_isCentralScalar` / 引理 `pointwise_isCentralScalar`

English:
lemma pointwise_isCentralScalar
  given: [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A]
  proof: ⟨fun _ S =>
(congr_arg fun f : AddMonoid.End A => S.map f) AddMonoidHom.ext op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwise_isCentralScalar

中文:
引理 pointwise_isCentralScalar
  条件: [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A]
  证明: ⟨fun _ S =>
(congr_arg fun f : AddMonoid.End A => S.map f) AddMonoidHom.ext op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwise_isCentralScalar

Depends on / 依赖: AddMonoid, AddMonoid.End, AddMonoidHom, AddMonoidHom.ext, S.map, congr_arg, op_smul_eq_smul
-/
lemma pointwise_isCentralScalar [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A] :
    IsCentralScalar M (AddSubmonoid A) :=
  ⟨fun _ S =>
(congr_arg fun f : AddMonoid.End A => S.map f) AddMonoidHom.ext op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwise_isCentralScalar

end Monoid

section Group
variable [Group G] [DistribMulAction G A] {a : G}

@[simp]
/--
lemma `smul_mem_pointwise_smul_iff` / 引理 `smul_mem_pointwise_smul_iff`

English:
lemma smul_mem_pointwise_smul_iff
  given: {S : AddSubmonoid A} {x : A}
  statement: a • x in a • S ↔ x in S
  proof: smul_mem_smul_set_iff

中文:
引理 smul_mem_pointwise_smul_iff
  条件: {S : AddSubmonoid A} {x : A}
  结论: a • x in a • S ↔ x in S
  证明: smul_mem_smul_set_iff

Depends on / 依赖: smul_mem_smul_set_iff
-/
lemma smul_mem_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : a • x in a • S ↔ x in S :=
  smul_mem_smul_set_iff

/--
lemma `mem_pointwise_smul_iff_inv_smul_mem` / 引理 `mem_pointwise_smul_iff_inv_smul_mem`

English:
lemma mem_pointwise_smul_iff_inv_smul_mem
  given: {S : AddSubmonoid A} {x : A}
  proof: mem_smul_set_iff_inv_smul_mem

中文:
引理 mem_pointwise_smul_iff_inv_smul_mem
  条件: {S : AddSubmonoid A} {x : A}
  证明: mem_smul_set_iff_inv_smul_mem

Depends on / 依赖: mem_smul_set_iff_inv_smul_mem
-/
lemma mem_pointwise_smul_iff_inv_smul_mem {S : AddSubmonoid A} {x : A} :
    x in a • S ↔ a⁻¹ • x in S :=
  mem_smul_set_iff_inv_smul_mem

/--
lemma `mem_inv_pointwise_smul_iff` / 引理 `mem_inv_pointwise_smul_iff`

English:
lemma mem_inv_pointwise_smul_iff
  given: {S : AddSubmonoid A} {x : A}
  statement: x in a⁻¹ • S ↔ a • x in S
  proof: mem_inv_smul_set_iff

@[simp]

中文:
引理 mem_inv_pointwise_smul_iff
  条件: {S : AddSubmonoid A} {x : A}
  结论: x in a⁻¹ • S ↔ a • x in S
  证明: mem_inv_smul_set_iff

@[simp]

Depends on / 依赖: mem_inv_smul_set_iff
-/
lemma mem_inv_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : x in a⁻¹ • S ↔ a • x in S :=
  mem_inv_smul_set_iff

@[simp]
/--
lemma `pointwise_smul_le_pointwise_smul_iff` / 引理 `pointwise_smul_le_pointwise_smul_iff`

English:
lemma pointwise_smul_le_pointwise_smul_iff
  given: {S T : AddSubmonoid A}
  proof: smul_set_subset_smul_set_iff

中文:
引理 pointwise_smul_le_pointwise_smul_iff
  条件: {S T : AddSubmonoid A}
  证明: smul_set_subset_smul_set_iff

Depends on / 依赖: smul_set_subset_smul_set_iff
-/
lemma pointwise_smul_le_pointwise_smul_iff {S T : AddSubmonoid A} :
    a • S <= a • T ↔ S <= T :=
  smul_set_subset_smul_set_iff

/--
lemma `pointwise_smul_le_iff` / 引理 `pointwise_smul_le_iff`

English:
lemma pointwise_smul_le_iff
  given: {S T : AddSubmonoid A}
  statement: a • S <= T ↔ S <= a⁻¹ • T
  proof: smul_set_subset_iff_subset_inv_smul_set

中文:
引理 pointwise_smul_le_iff
  条件: {S T : AddSubmonoid A}
  结论: a • S <= T ↔ S <= a⁻¹ • T
  证明: smul_set_subset_iff_subset_inv_smul_set

Depends on / 依赖: smul_set_subset_iff_subset_inv_smul_set
-/
lemma pointwise_smul_le_iff {S T : AddSubmonoid A} : a • S <= T ↔ S <= a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set

/--
lemma `le_pointwise_smul_iff` / 引理 `le_pointwise_smul_iff`

English:
lemma le_pointwise_smul_iff
  given: {S T : AddSubmonoid A}
  statement: S <= a • T ↔ a⁻¹ • S <= T
  proof: subset_smul_set_iff

中文:
引理 le_pointwise_smul_iff
  条件: {S T : AddSubmonoid A}
  结论: S <= a • T ↔ a⁻¹ • S <= T
  证明: subset_smul_set_iff

Depends on / 依赖: subset_smul_set_iff
-/
lemma le_pointwise_smul_iff {S T : AddSubmonoid A} : S <= a • T ↔ a⁻¹ • S <= T :=
  subset_smul_set_iff

end Group

section GroupWithZero
variable [GroupWithZero G₀] [DistribMulAction G₀ A] {S T : AddSubmonoid A} {a : G₀}

@[simp]
/--
lemma `smul_mem_pointwise_smul_iff₀` / 引理 `smul_mem_pointwise_smul_iff₀`

English:
lemma smul_mem_pointwise_smul_iff₀
  given: (ha : a != 0) (S : AddSubmonoid A) (x : A)
  proof: smul_mem_smul_set_iff₀ ha (S : Set A) x

中文:
引理 smul_mem_pointwise_smul_iff₀
  条件: (ha : a != 0) (S : AddSubmonoid A) (x : A)
  证明: smul_mem_smul_set_iff₀ ha (S : Set A) x
-/
lemma smul_mem_pointwise_smul_iff₀ (ha : a != 0) (S : AddSubmonoid A) (x : A) :
    a • x in a • S ↔ x in S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x

/--
lemma `mem_pointwise_smul_iff_inv_smul_mem₀` / 引理 `mem_pointwise_smul_iff_inv_smul_mem₀`

English:
lemma mem_pointwise_smul_iff_inv_smul_mem₀
  given: (ha : a != 0) (S : AddSubmonoid A) (x : A)
  proof: mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x

中文:
引理 mem_pointwise_smul_iff_inv_smul_mem₀
  条件: (ha : a != 0) (S : AddSubmonoid A) (x : A)
  证明: mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x
-/
lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a != 0) (S : AddSubmonoid A) (x : A) :
    x in a • S ↔ a⁻¹ • x in S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x

/--
lemma `mem_inv_pointwise_smul_iff₀` / 引理 `mem_inv_pointwise_smul_iff₀`

English:
lemma mem_inv_pointwise_smul_iff₀
  given: (ha : a != 0) (S : AddSubmonoid A) (x : A)
  proof: mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]

中文:
引理 mem_inv_pointwise_smul_iff₀
  条件: (ha : a != 0) (S : AddSubmonoid A) (x : A)
  证明: mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]
-/
lemma mem_inv_pointwise_smul_iff₀ (ha : a != 0) (S : AddSubmonoid A) (x : A) :
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
end AddSubmonoid
