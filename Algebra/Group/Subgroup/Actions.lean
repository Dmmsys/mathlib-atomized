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
/-
**Subgroup.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：instMulAction : MulAction S α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction : MulAction S α := inferInstanceAs (MulAction S.toSubmonoid α)
/-
**Subgroup.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{S : Subgroup G} (g : ↥S) (m : α),   g • m = ↑g • m
参数：g : ↥S；m : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma smul_def (g : S) (m : α) : g • m = (g : G) • m := rfl

@[to_additive (attr := simp)]
/-
**Subgroup.mk_smul** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mk_smul (g : G) (hg : g in S) (a : α) : (⟨g, hg⟩ : S) • a = g • a
参数：g : G；hg : g in S；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end MulAction

@[to_additive]
/-
**Subgroup.smulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：smulCommClass_left [MulAction G β] [SMul α β] [SMulCommClass G α β] (S : S
ubgroup G) : SMulCommClass S α β
参数：S : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass_left [MulAction G β] [SMul α β] [SMulCommClass G α β] (S : Subgroup G) :
    SMulCommClass S α β :=
  S.toSubmonoid.smulCommClass_left

@[to_additive]
/-
**Subgroup.smulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：smulCommClass_right [SMul α β] [MulAction G β] [SMulCommClass α G β] (S : 
Subgroup G) : SMulCommClass α S β
参数：S : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass_right [SMul α β] [MulAction G β] [SMulCommClass α G β] (S : Subgroup G) :
    SMulCommClass α S β :=
  S.toSubmonoid.smulCommClass_right

/-- Note that this provides `IsScalarTower S G G` which is needed by `smul_mul_assoc`. -/
@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this provides `IsScalarTower S G G` which is needed by `smul_mul_assoc
`.
-/
instance [SMul α β] [MulAction G α] [MulAction G β] [IsScalarTower G α β] (S : Subgroup G) :
    IsScalarTower S α β :=
  inferInstanceAs (IsScalarTower S.toSubmonoid α β)

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulAction G α] [FaithfulSMul G α] (S : Subgroup G) : FaithfulSMul S α :=
  inferInstanceAs (FaithfulSMul S.toSubmonoid α)

/-- The action by a subgroup is the action by the underlying group. -/
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subgroup is the action by the underlying group.
-/
instance [AddMonoid α] [DistribMulAction G α] (S : Subgroup G) : DistribMulAction S α :=
  inferInstanceAs (DistribMulAction S.toSubmonoid α)

/-- The action by a subgroup is the action by the underlying group. -/
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subgroup is the action by the underlying group.
-/
instance [Monoid α] [MulDistribMulAction G α] (S : Subgroup G) : MulDistribMulAction S α :=
  inferInstanceAs (MulDistribMulAction S.toSubmonoid α)

/-- The center of a group acts commutatively on that group. -/
/-
**Subgroup.center.smulCommClass_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.center`
。
形式化陈述：∀ {G : Type u_1} [inst : Group G], SMulCommClass (↥(Subgroup.center G)) G 
G
参数：↥(Subgroup.center G)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.center.smulCommClass_left`：∀ {M : Type u_1} [inst : Monoid M],
 SMulCommClass (↥(Submonoid.center M)) M M

--- 原说明 ---
The center of a group acts commutatively on that group.
-/
instance center.smulCommClass_left : SMulCommClass (center G) G G :=
  Submonoid.center.smulCommClass_left

/-- The center of a group acts commutatively on that group. -/
/-
**Subgroup.center.smulCommClass_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.center
`。
形式化陈述：∀ {G : Type u_1} [inst : Group G], SMulCommClass G (↥(Subgroup.center G)) 
G
参数：↥(Subgroup.center G)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.center.smulCommClass_right`：∀ {M : Type u_1} [inst : Monoid M]
, SMulCommClass M (↥(Submonoid.center M)) M

--- 原说明 ---
The center of a group acts commutatively on that group.
-/
instance center.smulCommClass_right : SMulCommClass G (center G) G :=
  Submonoid.center.smulCommClass_right

end Subgroup

open MonoidHom in
/-
**MonoidWithZeroHom.comap_mker** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidWithZeroHom.comap_mker {M N P : Type*} [MulZeroOneClass M] [MulZeroO
neClass N] [MulZeroOneClass P] (g : N ->*₀ P) (f : M ->*₀ N) : Submonoid.comap f
 (mker g) = mker (g.comp f)
参数：g : N ->*₀ P；f : M ->*₀ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
lemma MonoidWithZeroHom.comap_mker {M N P : Type*} [MulZeroOneClass M] [MulZeroOneClass N]
    [MulZeroOneClass P] (g : N →*₀ P) (f : M →*₀ N) :
    Submonoid.comap f (mker g) = mker (g.comp f) := rfl
