/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Simple groups

This file defines `IsSimpleGroup G`, a class indicating that a group has exactly two normal
subgroups.

## Main definitions

- `IsSimpleGroup G`, a class indicating that a group has exactly two normal subgroups.

## Tags
subgroup, subgroups

-/

public section


variable {G : Type*} [Group G]
variable {A : Type*} [AddGroup A]

section

variable (G) (A)

/-- A `Group` is simple when it has exactly two normal `Subgroup`s. -/
@[mk_iff, wikidata Q571124]
/-
**IsSimpleGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Group` is simple when it has exactly two normal `Subgroup`s.
-/
class IsSimpleGroup : Prop extends Nontrivial G where
  /-- Any normal subgroup is either `⊥` or `⊤` -/
  eq_bot_or_eq_top_of_normal : ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤

attribute [instance 100] IsSimpleGroup.toNontrivial

/-- An `AddGroup` is simple when it has exactly two normal `AddSubgroup`s. -/
@[mk_iff]
/-
**IsSimpleAddGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_2) → [AddGroup A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AddGroup` is simple when it has exactly two normal `AddSubgroup`s.
-/
class IsSimpleAddGroup : Prop extends Nontrivial A where
  /-- Any normal additive subgroup is either `⊥` or `⊤` -/
  eq_bot_or_eq_top_of_normal : ∀ H : AddSubgroup A, H.Normal → H = ⊥ ∨ H = ⊤

attribute [instance 100] IsSimpleAddGroup.toNontrivial

attribute [to_additive existing] IsSimpleGroup isSimpleGroup_iff

variable {G} {A}

@[to_additive]
/-
**Subgroup.Normal.eq_bot_or_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.Normal.eq_bot_or_eq_top [IsSimpleGroup G] {H : Subgroup G} (Hn : 
H.Normal) : H = ⊥ ∨ H = ⊤
参数：Hn : H.Normal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleGroup.eq_bot_or_eq_top_of_normal`：∀ {G : Type u_1} {inst : Group
 G} [self : IsSimpleGroup G] (H : Subgroup G), H.Normal → H = ⊥ ∨ H = ⊤
-/
theorem Subgroup.Normal.eq_bot_or_eq_top [IsSimpleGroup G] {H : Subgroup G} (Hn : H.Normal) :
    H = ⊥ ∨ H = ⊤ :=
  IsSimpleGroup.eq_bot_or_eq_top_of_normal H Hn

@[to_additive]
/-
**Subgroup.isSimpleGroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G},   IsSimpleGroup ↥H ↔ H
 ≠ ⊥ ∧ ∀ H' ≤ H, (H'.subgroupOf H).Normal → H' = ⊥ ∨ H' = H
参数：H'.subgroupOf H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSimpleGroup_iff`：∀ (G : Type u_1) [inst : Group G], IsSimpleGroup G ↔ 
Nontrivial G ∧ ∀ (H : Subgroup G), H.Normal → H = ⊥ ∨ H = ⊤
· 使用定理 `Subgroup.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot (H : Subgroup G) :
 Nontrivial H ↔ H != ⊥
· 使用定理 `Subgroup.forall`：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G} {P :
 Subgroup ↥H → Prop},   (∀ (H' : Subgroup ↥H), P H') ↔ ∀ H' ≤ H, P (H'.subgroupO
f H)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma Subgroup.isSimpleGroup_iff {H : Subgroup G} :
    IsSimpleGroup ↥H ↔ H ≠ ⊥ ∧ ∀ H' ≤ H, (H'.subgroupOf H).Normal → H' = ⊥ ∨ H' = H := by
  rw [isSimpleGroup_iff, H.nontrivial_iff_ne_bot, Subgroup.forall]
  simp +contextual [disjoint_of_le_iff_left_eq_bot, LE.le.ge_iff_eq]

namespace IsSimpleGroup

@[to_additive]
/-
**IsSimpleGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsSimpleGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type*} [CommGroup C] [IsSimpleGroup C] : IsSimpleOrder (Subgroup C) :=
  ⟨fun H => H.normal_of_isMulCommutative.eq_bot_or_eq_top⟩

open Subgroup

@[to_additive]
/-
**IsSimpleGroup.isSimpleGroup_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsSimpleG
roup`。
形式化陈述：isSimpleGroup_of_surjective {H : Type*} [Group H] [IsSimpleGroup G] [Nontr
ivial H] (f : G ->* H) (hf : Function.Surjective f) : IsSimpleGroup H
参数：f : G ->* H；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
· 使用定理 `Subgroup.map_comap_eq_self_of_surjective`：map_comap_eq_self_of_surjectiv
e {f : G ->* N} (h : Function.Surjective f) (H : Subgroup N) : map f (comap f H)
 = H
· 使用定理 `Subgroup.comap_injective`：comap_injective {f : G ->* N} (h : Function.Su
rjective f) : Function.Injective (comap f)
· 使用定理 `Subgroup.comap_top`：comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f =
 ⊤
· 使用定理 `Subgroup.Normal.eq_bot_or_eq_top`：Subgroup.Normal.eq_bot_or_eq_top [IsSi
mpleGroup G] {H : Subgroup G} (Hn : H.Normal) : H = ⊥ ∨ H = ⊤
· 使用定理 `Subgroup.Normal.comap`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} 
[inst_1 : Group N] {H : Subgroup N},   H.Normal → ∀ (f : G →* N), (Subgroup.coma
p f H).Norm…
-/
theorem isSimpleGroup_of_surjective {H : Type*} [Group H] [IsSimpleGroup G] [Nontrivial H]
    (f : G →* H) (hf : Function.Surjective f) : IsSimpleGroup H :=
  ⟨fun H iH => by
    refine (iH.comap f).eq_bot_or_eq_top.imp (fun h => ?_) fun h => ?_
    · rw [← map_bot f, ← h, map_comap_eq_self_of_surjective hf]
    · rw [← comap_top f] at h
      exact comap_injective hf h⟩

@[to_additive]
/-
**IsSimpleGroup._root_.MulEquiv.isSimpleGroup** 是 Mathlib 中的一个引理，位于命名空间 `IsSimpl
eGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MulEquiv.isSimpleGroup {H : Type*} [Group H] [IsSimpleGroup H] (e : G ≃* H) :
    IsSimpleGroup G :=
  haveI : Nontrivial G := e.toEquiv.nontrivial
  isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

@[to_additive]
/-
**IsSimpleGroup._root_.MulEquiv.isSimpleGroup_congr** 是 Mathlib 中的一个引理，位于命名空间 `I
sSimpleGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MulEquiv.isSimpleGroup_congr {H : Type*} [Group H] (e : G ≃* H) :
    IsSimpleGroup G ↔ IsSimpleGroup H where
  mp _ := e.symm.isSimpleGroup
  mpr _ := e.isSimpleGroup

end IsSimpleGroup

end

