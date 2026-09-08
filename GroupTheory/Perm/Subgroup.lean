/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Fintype.Perm

/-!
# Lemmas about subgroups within the permutations (self-equivalences) of a type `α`

This file provides extra lemmas about some `Subgroup`s that exist within `Equiv.Perm α`.
`GroupTheory.Subgroup` depends on `GroupTheory.Perm.Basic`, so these need to be in a separate
file.

It also provides decidable instances on membership in these subgroups, since
`MonoidHom.decidableMemRange` cannot be inferred without the help of a lambda.
The presence of these instances induces a `Fintype` instance on the `QuotientGroup.Quotient` of
these subgroups.

In particular, we prove **Cayley's theorem** in `Equiv.Perm.subgroupOfMulAction`:
every group `G` is isomorphic to a subgroup of the symmetric group acting on `G`.
-/

@[expose] public section

assert_not_exists Field

namespace Equiv

namespace Perm

universe u

/-
**Equiv.Perm.sumCongrHom.decidableMemRange** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm
.sumCongrHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [DecidableEq α] →       [Decidable
Eq β] → [Fintype α] → [Fintype β] → DecidablePred fun x => x ∈ (Equiv.Perm.sumCo
ngrHom α β).range
参数：Equiv.Perm.sumCongrHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sumCongrHom.decidableMemRange {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] : DecidablePred (· ∈ (sumCongrHom α β).range) := fun _ => inferInstance

@[simp]
/-
**Equiv.Perm.sumCongrHom.card_range** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.sumCon
grHom`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Fintype ↥(Equiv.Perm.sumCongrHom α
 β).range]   [inst_1 : Fintype (Equiv.Perm α × Equiv.Perm β)],   Fintype.card ↥(
Equiv.Perm.sumCongrHom α β).range = Fintype.card (Equiv.Perm α × Equiv.Perm β)
参数：Equiv.Perm.sumCongrHom α β；Equiv.Perm α × Equiv.Perm β；Equiv.Perm.sumCongrHom
 α β；Equiv.Perm α × Equiv.Perm β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.sumCongrHom_injective`：sumCongrHom_injective {α β : Type*} : 
Function.Injective (sumCongrHom α β)
-/
theorem sumCongrHom.card_range {α β : Type*} [Fintype (sumCongrHom α β).range]
    [Fintype (Perm α × Perm β)] :
    Fintype.card (sumCongrHom α β).range = Fintype.card (Perm α × Perm β) :=
  Fintype.card_eq.mpr ⟨(ofInjective (sumCongrHom α β) sumCongrHom_injective).symm⟩
/-
**Equiv.Perm.sigmaCongrRightHom.decidableMemRange** 是 Mathlib 中的一个定义，位于命名空间 `Equ
iv.Perm.sigmaCongrRightHom`。
形式化陈述：{α : Type u_1} →   {β : α → Type u_2} →     [DecidableEq α] →       [(a : 
α) → DecidableEq (β a)] →         [Fintype α] → [(a : α) → Fintype (β a)] → Deci
dablePred fun x => x ∈ (Equiv.Perm.sigmaCongrRightHom β).range
参数：a : α；β a；a : α；β a；Equiv.Perm.sigmaCongrRightHom β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sigmaCongrRightHom.decidableMemRange {α : Type*} {β : α → Type*} [DecidableEq α]
    [∀ a, DecidableEq (β a)] [Fintype α] [∀ a, Fintype (β a)] :
    DecidablePred (· ∈ (sigmaCongrRightHom β).range) := fun _ => inferInstance

@[simp]
/-
**Equiv.Perm.sigmaCongrRightHom.card_range** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
.sigmaCongrRightHom`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_2} [inst : Fintype ↥(Equiv.Perm.sigmaCong
rRightHom β).range]   [inst_1 : Fintype ((a : α) → Equiv.Perm (β a))],   Fintype
.card ↥(Equiv.Perm.sigmaCongrRightHom β).range = Fintype.card ((a : α) → Equiv.P
erm (β a))
参数：Equiv.Perm.sigmaCongrRightHom β；(a : α) → Equiv.Perm (β a)；Equiv.Perm.sigmaCo
ngrRightHom β；(a : α) → Equiv.Perm (β a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.sigmaCongrRightHom_injective`：sigmaCongrRightHom_injective {α
 : Type*} {β : α -> Type*} : Function.Injective (sigmaCongrRightHom β)
-/
theorem sigmaCongrRightHom.card_range {α : Type*} {β : α → Type*}
    [Fintype (sigmaCongrRightHom β).range] [Fintype (∀ a, Perm (β a))] :
    Fintype.card (sigmaCongrRightHom β).range = Fintype.card (∀ a, Perm (β a)) :=
  Fintype.card_eq.mpr ⟨(ofInjective (sigmaCongrRightHom β) sigmaCongrRightHom_injective).symm⟩
/-
**Equiv.Perm.subtypeCongrHom.decidableMemRange** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.
Perm.subtypeCongrHom`。
形式化陈述：{α : Type u_1} →   (p : α → Prop) →     [inst : DecidablePred p] →       [
Fintype (Equiv.Perm { a // p a } × Equiv.Perm { a // ¬p a })] →         [Decidab
leEq (Equiv.Perm α)] → DecidablePred fun x => x ∈ (Equiv.Perm.subtypeCongrHom p)
.range
参数：p : α → Prop；Equiv.Perm { a // p a } × Equiv.Perm { a // ¬p a }；Equiv.Perm α；
Equiv.Perm.subtypeCongrHom p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance subtypeCongrHom.decidableMemRange {α : Type*} (p : α → Prop) [DecidablePred p]
    [Fintype (Perm { a // p a } × Perm { a // ¬p a })] [DecidableEq (Perm α)] :
    DecidablePred (· ∈ (subtypeCongrHom p).range) := fun _ => inferInstance

@[simp]
/-
**Equiv.Perm.subtypeCongrHom.card_range** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.su
btypeCongrHom`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p] [inst_1 : Fintype
 ↥(Equiv.Perm.subtypeCongrHom p).range]   [inst_2 : Fintype (Equiv.Perm { a // p
 a } × Equiv.Perm { a // ¬p a })],   Fintype.card ↥(Equiv.Perm.subtypeCongrHom p
).range = Fintype.card (Equiv.Perm { a // p a } × Equiv.Perm { a // ¬p a })
参数：p : α → Prop；Equiv.Perm.subtypeCongrHom p；Equiv.Perm { a // p a } × Equiv.Per
m { a // ¬p a }；Equiv.Perm.subtypeCongrHom p；Equiv.Perm { a // p a } × Equiv.Per
m { a // ¬p a }。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.subtypeCongrHom_injective`：subtypeCongrHom_injective (p : α -
> Prop) [DecidablePred p] : Function.Injective (subtypeCongrHom p)
-/
theorem subtypeCongrHom.card_range {α : Type*} (p : α → Prop) [DecidablePred p]
    [Fintype (subtypeCongrHom p).range] [Fintype (Perm { a // p a } × Perm { a // ¬p a })] :
    Fintype.card (subtypeCongrHom p).range =
      Fintype.card (Perm { a // p a } × Perm { a // ¬p a }) :=
  Fintype.card_eq.mpr ⟨(ofInjective (subtypeCongrHom p) (subtypeCongrHom_injective p)).symm⟩

/-- **Cayley's theorem**: Every group G is isomorphic to a subgroup of the symmetric group acting on
`G`. Note that we generalize this to an arbitrary "faithful" group action by `G`. Setting `H = G`
recovers the usual statement of Cayley's theorem via `RightCancelMonoid.faithfulSMul` -/
@[wikidata Q179208]
/-
**Equiv.Perm.subgroupOfMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：subgroupOfMulAction (G H : Type*) [Group G] [MulAction G H] [FaithfulSMul 
G H] : G ≃* (MulAction.toPermHom G H).range
参数：G H : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Cayley's theorem**: Every group G is isomorphic to a subgroup of the symmetric
 group acting on
`G`. Note that we generalize this to an arbitrary "faithful" group action by `G`
. Setting `H = G`
recovers the usual statement of Cayley's theorem via `RightCancelMonoid.faithful
SMul`
-/
noncomputable def subgroupOfMulAction (G H : Type*) [Group G] [MulAction G H] [FaithfulSMul G H] :
    G ≃* (MulAction.toPermHom G H).range :=
  MulEquiv.ofLeftInverse' _ (Classical.choose_spec MulAction.toPerm_injective.hasLeftInverse)

end Perm

end Equiv

