/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Submonoid.DistribMulAction
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Actions by `Subgroup`s

These are just copies of the definitions about `Submonoid` starting from `Submonoid.mulAction`.

## Tags
subgroup, subgroups

-/

@[expose] public section


namespace Subgroup
variable {G α β : Type*} [Group G]

section MulAction
variable [MulAction G α] {S : Subgroup G}

/-- The action by a subgroup is the action by the underlying group. -/
@[to_additive
/-- The additive action by an `AddSubgroup` is the action by the underlying `AddGroup`. -/]
/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: : MulAction S α
  body: inferInstanceAs (MulAction S.toSubmonoid α)

中文:
实例 instMulAction
  签名: : 乘法作用 S α
  定义体: inferInstanceAs (MulAction S.toSubmonoid α)

Depends on / 依赖: MulAction, S.toSubmonoid, toSubmonoid
-/
instance instMulAction : MulAction S α := inferInstanceAs (MulAction S.toSubmonoid α)

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (g : S) (m : α)
  statement: g • m = (g : G) • m
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 smul_def
  条件: (g : S) (m : α)
  结论: g • m = (g : G) • m
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive] lemma smul_def (g : S) (m : α) : g • m = (g : G) • m := rfl

@[to_additive (attr := simp)]
/--
lemma `mk_smul` / 引理 `mk_smul`

English:
lemma mk_smul
  given: (g : G) (hg : g in S) (a : α)
  statement: (⟨g, hg⟩ : S) • a = g • a
  proof: rfl

中文:
引理 mk_smul
  条件: (g : G) (hg : g in S) (a : α)
  结论: (⟨g, hg⟩ : S) • a = g • a
  证明: rfl
-/
lemma mk_smul (g : G) (hg : g in S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end MulAction

@[to_additive]
/--
Instance `smulCommClass_left` / 实例 `smulCommClass_left`

English:
instance smulCommClass_left
  signature: [MulAction G β] [SMul α β] [SMulCommClass G α β] (S : Subgroup G)
  body: S.toSubmonoid.smulCommClass_left

@[to_additive]

中文:
实例 smulCommClass_left
  签名: [乘法作用 G β] [标量乘法 α β] [标量交换类 G α β] (S : 子群 G)
  定义体: S.toSubmonoid.smulCommClass_left

@[to_additive]

Depends on / 依赖: S.toSubmonoid.smulCommClass_left, smulCommClass_left, toSubmonoid
-/
instance smulCommClass_left [MulAction G β] [SMul α β] [SMulCommClass G α β] (S : Subgroup G) :
    SMulCommClass S α β :=
  S.toSubmonoid.smulCommClass_left

@[to_additive]
/--
Instance `smulCommClass_right` / 实例 `smulCommClass_right`

English:
instance smulCommClass_right
  signature: [SMul α β] [MulAction G β] [SMulCommClass α G β] (S : Subgroup G)
  body: S.toSubmonoid.smulCommClass_right

中文:
实例 smulCommClass_right
  签名: [标量乘法 α β] [乘法作用 G β] [标量交换类 α G β] (S : 子群 G)
  定义体: S.toSubmonoid.smulCommClass_right

Depends on / 依赖: S.toSubmonoid.smulCommClass_right, smulCommClass_right, toSubmonoid
-/
instance smulCommClass_right [SMul α β] [MulAction G β] [SMulCommClass α G β] (S : Subgroup G) :
    SMulCommClass α S β :=
  S.toSubmonoid.smulCommClass_right

/-- Note that this provides `IsScalarTower S G G` which is needed by `smul_mul_assoc`. -/
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: α β] [MulAction G α] [MulAction G β] [IsScalarTower G α β] (S
  body: inferInstanceAs (IsScalarTower S.toSubmonoid α β)

@[to_additive]

中文:
实例 [标量乘法
  签名: α β] [乘法作用 G α] [乘法作用 G β] [标量塔 G α β] (S
  定义体: inferInstanceAs (IsScalarTower S.toSubmonoid α β)

@[to_additive]

Depends on / 依赖: IsScalarTower, S.toSubmonoid, toSubmonoid
-/
instance [SMul α β] [MulAction G α] [MulAction G β] [IsScalarTower G α β] (S : Subgroup G) :
    IsScalarTower S α β :=
  inferInstanceAs (IsScalarTower S.toSubmonoid α β)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulAction
  signature: G α] [FaithfulSMul G α] (S
  body: inferInstanceAs (FaithfulSMul S.toSubmonoid α)

中文:
实例 [乘法作用
  签名: G α] [忠实标量乘法 G α] (S
  定义体: inferInstanceAs (FaithfulSMul S.toSubmonoid α)

Depends on / 依赖: FaithfulSMul, S.toSubmonoid, toSubmonoid
-/
instance [MulAction G α] [FaithfulSMul G α] (S : Subgroup G) : FaithfulSMul S α :=
  inferInstanceAs (FaithfulSMul S.toSubmonoid α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: α] [DistribMulAction G α] (S
  body: inferInstanceAs (DistribMulAction S.toSubmonoid α)

中文:
实例 [加法幺半群
  签名: α] [分配乘法作用 G α] (S
  定义体: inferInstanceAs (DistribMulAction S.toSubmonoid α)

Depends on / 依赖: DistribMulAction, S.toSubmonoid, toSubmonoid
-/
instance [AddMonoid α] [DistribMulAction G α] (S : Subgroup G) : DistribMulAction S α :=
  inferInstanceAs (DistribMulAction S.toSubmonoid α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [MulDistribMulAction G α] (S
  body: inferInstanceAs (MulDistribMulAction S.toSubmonoid α)

中文:
实例 [幺半群
  签名: α] [MulDistribMul作用 G α] (S
  定义体: inferInstanceAs (MulDistribMulAction S.toSubmonoid α)

Depends on / 依赖: MulDistribMulAction, S.toSubmonoid, toSubmonoid
-/
instance [Monoid α] [MulDistribMulAction G α] (S : Subgroup G) : MulDistribMulAction S α :=
  inferInstanceAs (MulDistribMulAction S.toSubmonoid α)

/--
Instance `center.smulCommClass_left` / 实例 `center.smulCommClass_left`

English:
instance center.smulCommClass_left
  signature: : SMulCommClass (center G) G G
  body: Submonoid.center.smulCommClass_left

中文:
实例 center.smulCommClass_left
  签名: : 标量交换类 (center G) G G
  定义体: Submonoid.center.smulCommClass_left

Depends on / 依赖: Submonoid, Submonoid.center.smulCommClass_left, center, smulCommClass_left
-/
instance center.smulCommClass_left : SMulCommClass (center G) G G :=
  Submonoid.center.smulCommClass_left

/--
Instance `center.smulCommClass_right` / 实例 `center.smulCommClass_right`

English:
instance center.smulCommClass_right
  signature: : SMulCommClass G (center G) G
  body: Submonoid.center.smulCommClass_right

中文:
实例 center.smulCommClass_right
  签名: : 标量交换类 G (center G) G
  定义体: Submonoid.center.smulCommClass_right

Depends on / 依赖: Submonoid, Submonoid.center.smulCommClass_right, center, smulCommClass_right
-/
instance center.smulCommClass_right : SMulCommClass G (center G) G :=
  Submonoid.center.smulCommClass_right

end Subgroup

open MonoidHom in
/--
lemma `MonoidWithZeroHom.comap_mker` / 引理 `MonoidWithZeroHom.comap_mker`

English:
lemma MonoidWithZeroHom.comap_mker
  statement: {M N P : Type*} [MulZeroOneClass M] [MulZeroOneClass N]
  proof: rfl

中文:
引理 带零幺半群态射.comap_mker
  结论: {M N P : 类型} [乘零幺类 M] [乘零幺类 N]
  证明: rfl
-/
lemma MonoidWithZeroHom.comap_mker {M N P : Type*} [MulZeroOneClass M] [MulZeroOneClass N]
    [MulZeroOneClass P] (g : N ->*₀ P) (f : M ->*₀ N) :
    Submonoid.comap f (mker g) = mker (g.comp f) := rfl
