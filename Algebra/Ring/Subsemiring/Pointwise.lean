/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise
public import Mathlib.Algebra.Ring.Subsemiring.Basic

/-! # Pointwise instances on `Subsemiring`s

This file provides the action `Subsemiring.PointwiseMulAction` which matches the action of
`MulActionSet`.

This actions is available in the `Pointwise` locale.

## Implementation notes

This file is almost identical to the files `Mathlib/Algebra/GroupWithZero/Submonoid/Pointwise.lean`
and `Mathlib/Algebra/Ring/Submonoid/Pointwise.lean`. Where possible, try to keep them in sync.
-/

@[expose] public section


open Set

variable {M R : Type*}

namespace Subsemiring

section Monoid

variable [Monoid M] [Semiring R] [MulSemiringAction M R]

/-- The action on a subsemiring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseMulAction` / `pointwiseMulAction` 的定义

English:
definition pointwiseMulAction
  signature: : MulAction M (Subsemiring R) where
  body: S.map (MulSemiringAction.toRingHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (RingHom.ext <| one_smul M)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (RingHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subsemiring.pointwiseMulAction

中文:
定义 pointwiseMulAction
  签名: : 乘法作用 M (子半环 R) where
  定义体: S.map (MulSemiringAction.toRingHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (RingHom.ext <| one_smul M)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (RingHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subsemiring.pointwiseMulAction
-/
protected def pointwiseMulAction : MulAction M (Subsemiring R) where
  smul a S := S.map (MulSemiringAction.toRingHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (RingHom.ext <| one_smul M)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (RingHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subsemiring.pointwiseMulAction

open scoped Pointwise

/--
theorem `pointwise_smul_def` / 定理 `pointwise_smul_def`

English:
theorem pointwise_smul_def
  given: {a : M} (S : Subsemiring R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 pointwise_smul_def
  条件: {a : M} (S : 子半环 R)
  证明: rfl

@[simp, norm_cast]
-/
theorem pointwise_smul_def {a : M} (S : Subsemiring R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_pointwise_smul` / 定理 `coe_pointwise_smul`

English:
theorem coe_pointwise_smul
  given: (m : M) (S : Subsemiring R)
  statement: ↑(m • S) = m • (S : Set R)
  proof: rfl

@[simp]

中文:
定理 coe_pointwise_smul
  条件: (m : M) (S : 子半环 R)
  结论: ↑(m • S) = m • (S : 集合 R)
  证明: rfl

@[simp]
-/
theorem coe_pointwise_smul (m : M) (S : Subsemiring R) : ↑(m • S) = m • (S : Set R) :=
  rfl

@[simp]
/--
theorem `pointwise_smul_toAddSubmonoid` / 定理 `pointwise_smul_toAddSubmonoid`

English:
theorem pointwise_smul_toAddSubmonoid
  given: (m : M) (S : Subsemiring R)
  proof: rfl

中文:
定理 pointwise_smul_toAddSubmonoid
  条件: (m : M) (S : 子半环 R)
  证明: rfl
-/
theorem pointwise_smul_toAddSubmonoid (m : M) (S : Subsemiring R) :
    (m • S).toAddSubmonoid = m • S.toAddSubmonoid :=
  rfl

/--
theorem `smul_mem_pointwise_smul` / 定理 `smul_mem_pointwise_smul`

English:
theorem smul_mem_pointwise_smul
  given: (m : M) (r : R) (S : Subsemiring R)
  statement: r in S -> m • r in m • S
  proof: (Set.smul_mem_smul_set : _ -> _ in m • (S : Set R))

中文:
定理 smul_mem_pointwise_smul
  条件: (m : M) (r : R) (S : 子半环 R)
  结论: r in S -> m • r in m • S
  证明: (Set.smul_mem_smul_set : _ -> _ in m • (S : Set R))

Depends on / 依赖: Set.smul_mem_smul_set, map_prop, smul_mem_smul_set
-/
theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Subsemiring R) : r in S -> m • r in m • S :=
  (Set.smul_mem_smul_set : _ -> _ in m • (S : Set R))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CovariantClass M (Subsemiring R) HSMul.hSMul LE.le
  body: ⟨fun _ _ => image_mono⟩

中文:
实例 :
  签名: 协变类 M (子半环 R) 异质标量乘法.hSMul LE.le
  定义体: ⟨fun _ _ => image_mono⟩

Depends on / 依赖: IsOpenImmersion, image_mono, infer_instance, of_comp
-/
instance : CovariantClass M (Subsemiring R) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_mono⟩

/--
theorem `mem_smul_pointwise_iff_exists` / 定理 `mem_smul_pointwise_iff_exists`

English:
theorem mem_smul_pointwise_iff_exists
  given: (m : M) (r : R) (S : Subsemiring R)
  proof: (Set.mem_smul_set : r in m • (S : Set R) ↔ _)

@[simp]

中文:
定理 mem_smul_pointwise_iff_存在
  条件: (m : M) (r : R) (S : 子半环 R)
  证明: (Set.mem_smul_set : r in m • (S : Set R) ↔ _)

@[simp]

Depends on / 依赖: Set.mem_smul_set, mem_smul_set
-/
theorem mem_smul_pointwise_iff_exists (m : M) (r : R) (S : Subsemiring R) :
    r in m • S ↔ exists s : R, s in S ∧ m • s = r :=
  (Set.mem_smul_set : r in m • (S : Set R) ↔ _)

@[simp]
/--
theorem `smul_bot` / 定理 `smul_bot`

English:
theorem smul_bot
  given: (a : M)
  statement: a • (⊥ : Subsemiring R) = ⊥
  proof: map_bot _

中文:
定理 smul_bot
  条件: (a : M)
  结论: a • (⊥ : 子半环 R) = ⊥
  证明: map_bot _

Depends on / 依赖: map_bot
-/
theorem smul_bot (a : M) : a • (⊥ : Subsemiring R) = ⊥ :=
  map_bot _

/--
theorem `smul_sup` / 定理 `smul_sup`

English:
theorem smul_sup
  given: (a : M) (S T : Subsemiring R)
  statement: a • (S ⊔ T) = a • S ⊔ a • T
  proof: map_sup _ _ _

中文:
定理 smul_sup
  条件: (a : M) (S T : 子半环 R)
  结论: a • (S ⊔ T) = a • S ⊔ a • T
  证明: map_sup _ _ _

Depends on / 依赖: map_sup
-/
theorem smul_sup (a : M) (S T : Subsemiring R) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

/--
theorem `smul_closure` / 定理 `smul_closure`

English:
theorem smul_closure
  given: (a : M) (s : Set R)
  statement: a • closure s = closure (a • s)
  proof: RingHom.map_closureS _ _

中文:
定理 smul_closure
  条件: (a : M) (s : 集合 R)
  结论: a • closure s = closure (a • s)
  证明: RingHom.map_closureS _ _

Depends on / 依赖: RingHom, RingHom.map_closureS, map_closureS
-/
theorem smul_closure (a : M) (s : Set R) : a • closure s = closure (a • s) :=
  RingHom.map_closureS _ _

/--
Instance `pointwise_central_scalar` / 实例 `pointwise_central_scalar`

English:
instance pointwise_central_scalar
  signature: [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R]
  body: ⟨fun _a S => (congr_arg fun f => S.map f) RingHom.ext op_smul_eq_smul _⟩

中文:
实例 pointwise_central_scalar
  签名: [MulSemiring作用 Mᵐᵒᵖ R] [中心标量 M R]
  定义体: ⟨fun _a S => (congr_arg fun f => S.map f) RingHom.ext op_smul_eq_smul _⟩

Depends on / 依赖: RingHom, RingHom.ext, S.map, congr_arg, op_smul_eq_smul
-/
instance pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] :
    IsCentralScalar M (Subsemiring R) :=
⟨fun _a S => (congr_arg fun f => S.map f) RingHom.ext op_smul_eq_smul _⟩

end Monoid

section Group

variable [Group M] [Semiring R] [MulSemiringAction M R]

open scoped Pointwise

@[simp]
/--
theorem `smul_mem_pointwise_smul_iff` / 定理 `smul_mem_pointwise_smul_iff`

English:
theorem smul_mem_pointwise_smul_iff
  given: {a : M} {S : Subsemiring R} {x : R}
  statement: a • x in a • S ↔ x in S
  proof: smul_mem_smul_set_iff

中文:
定理 smul_mem_pointwise_smul_iff
  条件: {a : M} {S : 子半环 R} {x : R}
  结论: a • x in a • S ↔ x in S
  证明: smul_mem_smul_set_iff

Depends on / 依赖: smul_mem_smul_set_iff
-/
theorem smul_mem_pointwise_smul_iff {a : M} {S : Subsemiring R} {x : R} : a • x in a • S ↔ x in S :=
  smul_mem_smul_set_iff

/--
theorem `mem_pointwise_smul_iff_inv_smul_mem` / 定理 `mem_pointwise_smul_iff_inv_smul_mem`

English:
theorem mem_pointwise_smul_iff_inv_smul_mem
  given: {a : M} {S : Subsemiring R} {x : R}
  proof: mem_smul_set_iff_inv_smul_mem

中文:
定理 mem_pointwise_smul_iff_inv_smul_mem
  条件: {a : M} {S : 子半环 R} {x : R}
  证明: mem_smul_set_iff_inv_smul_mem

Depends on / 依赖: mem_smul_set_iff_inv_smul_mem
-/
theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Subsemiring R} {x : R} :
    x in a • S ↔ a⁻¹ • x in S :=
  mem_smul_set_iff_inv_smul_mem

/--
theorem `mem_inv_pointwise_smul_iff` / 定理 `mem_inv_pointwise_smul_iff`

English:
theorem mem_inv_pointwise_smul_iff
  given: {a : M} {S : Subsemiring R} {x : R}
  statement: x in a⁻¹ • S ↔ a • x in S
  proof: mem_inv_smul_set_iff

@[simp]

中文:
定理 mem_inv_pointwise_smul_iff
  条件: {a : M} {S : 子半环 R} {x : R}
  结论: x in a⁻¹ • S ↔ a • x in S
  证明: mem_inv_smul_set_iff

@[simp]

Depends on / 依赖: mem_inv_smul_set_iff
-/
theorem mem_inv_pointwise_smul_iff {a : M} {S : Subsemiring R} {x : R} : x in a⁻¹ • S ↔ a • x in S :=
  mem_inv_smul_set_iff

@[simp]
/--
theorem `pointwise_smul_le_pointwise_smul_iff` / 定理 `pointwise_smul_le_pointwise_smul_iff`

English:
theorem pointwise_smul_le_pointwise_smul_iff
  given: {a : M} {S T : Subsemiring R}
  proof: smul_set_subset_smul_set_iff

中文:
定理 pointwise_smul_le_pointwise_smul_iff
  条件: {a : M} {S T : 子半环 R}
  证明: smul_set_subset_smul_set_iff

Depends on / 依赖: map_prop, smul_set_subset_smul_set_iff
-/
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Subsemiring R} :
    a • S <= a • T ↔ S <= T :=
  smul_set_subset_smul_set_iff

/--
theorem `pointwise_smul_subset_iff` / 定理 `pointwise_smul_subset_iff`

English:
theorem pointwise_smul_subset_iff
  given: {a : M} {S T : Subsemiring R}
  statement: a • S <= T ↔ S <= a⁻¹ • T
  proof: smul_set_subset_iff_subset_inv_smul_set

中文:
定理 pointwise_smul_subset_iff
  条件: {a : M} {S T : 子半环 R}
  结论: a • S <= T ↔ S <= a⁻¹ • T
  证明: smul_set_subset_iff_subset_inv_smul_set

Depends on / 依赖: smul_set_subset_iff_subset_inv_smul_set
-/
theorem pointwise_smul_subset_iff {a : M} {S T : Subsemiring R} : a • S <= T ↔ S <= a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set

/--
theorem `subset_pointwise_smul_iff` / 定理 `subset_pointwise_smul_iff`

English:
theorem subset_pointwise_smul_iff
  given: {a : M} {S T : Subsemiring R}
  statement: S <= a • T ↔ a⁻¹ • S <= T
  proof: subset_smul_set_iff

中文:
定理 subset_pointwise_smul_iff
  条件: {a : M} {S T : 子半环 R}
  结论: S <= a • T ↔ a⁻¹ • S <= T
  证明: subset_smul_set_iff

Depends on / 依赖: subset_smul_set_iff
-/
theorem subset_pointwise_smul_iff {a : M} {S T : Subsemiring R} : S <= a • T ↔ a⁻¹ • S <= T :=
  subset_smul_set_iff

/-! TODO: add `equiv_smul` like we have for subgroup. -/


end Group

section GroupWithZero

variable [GroupWithZero M] [Semiring R] [MulSemiringAction M R]

open scoped Pointwise

@[simp]
/--
theorem `smul_mem_pointwise_smul_iff₀` / 定理 `smul_mem_pointwise_smul_iff₀`

English:
theorem smul_mem_pointwise_smul_iff₀
  given: {a : M} (ha : a != 0) (S : Subsemiring R) (x : R)
  proof: smul_mem_smul_set_iff₀ ha (S : Set R) x

中文:
定理 smul_mem_pointwise_smul_iff₀
  条件: {a : M} (ha : a != 0) (S : 子半环 R) (x : R)
  证明: smul_mem_smul_set_iff₀ ha (S : Set R) x
-/
theorem smul_mem_pointwise_smul_iff₀ {a : M} (ha : a != 0) (S : Subsemiring R) (x : R) :
    a • x in a • S ↔ x in S :=
  smul_mem_smul_set_iff₀ ha (S : Set R) x

/--
theorem `mem_pointwise_smul_iff_inv_smul_mem₀` / 定理 `mem_pointwise_smul_iff_inv_smul_mem₀`

English:
theorem mem_pointwise_smul_iff_inv_smul_mem₀
  given: {a : M} (ha : a != 0) (S : Subsemiring R) (x : R)
  proof: mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x

中文:
定理 mem_pointwise_smul_iff_inv_smul_mem₀
  条件: {a : M} (ha : a != 0) (S : 子半环 R) (x : R)
  证明: mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x
-/
theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : M} (ha : a != 0) (S : Subsemiring R) (x : R) :
    x in a • S ↔ a⁻¹ • x in S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x

/--
theorem `mem_inv_pointwise_smul_iff₀` / 定理 `mem_inv_pointwise_smul_iff₀`

English:
theorem mem_inv_pointwise_smul_iff₀
  given: {a : M} (ha : a != 0) (S : Subsemiring R) (x : R)
  proof: mem_inv_smul_set_iff₀ ha (S : Set R) x

@[simp]

中文:
定理 mem_inv_pointwise_smul_iff₀
  条件: {a : M} (ha : a != 0) (S : 子半环 R) (x : R)
  证明: mem_inv_smul_set_iff₀ ha (S : Set R) x

@[simp]
-/
theorem mem_inv_pointwise_smul_iff₀ {a : M} (ha : a != 0) (S : Subsemiring R) (x : R) :
    x in a⁻¹ • S ↔ a • x in S :=
  mem_inv_smul_set_iff₀ ha (S : Set R) x

@[simp]
/--
theorem `pointwise_smul_le_pointwise_smul_iff₀` / 定理 `pointwise_smul_le_pointwise_smul_iff₀`

English:
theorem pointwise_smul_le_pointwise_smul_iff₀
  given: {a : M} (ha : a != 0) {S T : Subsemiring R}
  proof: smul_set_subset_smul_set_iff₀ ha

中文:
定理 pointwise_smul_le_pointwise_smul_iff₀
  条件: {a : M} (ha : a != 0) {S T : 子半环 R}
  证明: smul_set_subset_smul_set_iff₀ ha
-/
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : M} (ha : a != 0) {S T : Subsemiring R} :
    a • S <= a • T ↔ S <= T :=
  smul_set_subset_smul_set_iff₀ ha

/--
theorem `pointwise_smul_le_iff₀` / 定理 `pointwise_smul_le_iff₀`

English:
theorem pointwise_smul_le_iff₀
  given: {a : M} (ha : a != 0) {S T : Subsemiring R}
  proof: smul_set_subset_iff₀ ha

中文:
定理 pointwise_smul_le_iff₀
  条件: {a : M} (ha : a != 0) {S T : 子半环 R}
  证明: smul_set_subset_iff₀ ha
-/
theorem pointwise_smul_le_iff₀ {a : M} (ha : a != 0) {S T : Subsemiring R} :
    a • S <= T ↔ S <= a⁻¹ • T :=
  smul_set_subset_iff₀ ha

/--
theorem `le_pointwise_smul_iff₀` / 定理 `le_pointwise_smul_iff₀`

English:
theorem le_pointwise_smul_iff₀
  given: {a : M} (ha : a != 0) {S T : Subsemiring R}
  proof: subset_smul_set_iff₀ ha

中文:
定理 le_pointwise_smul_iff₀
  条件: {a : M} (ha : a != 0) {S T : 子半环 R}
  证明: subset_smul_set_iff₀ ha
-/
theorem le_pointwise_smul_iff₀ {a : M} (ha : a != 0) {S T : Subsemiring R} :
    S <= a • T ↔ a⁻¹ • S <= T :=
  subset_smul_set_iff₀ ha

end GroupWithZero

end Subsemiring
