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
/-
**inv_coe_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_coe_set [InvolutiveInv G] [SetLike S G] [InvMemClass S G] {H : S} : (H
 : Set G)⁻¹ = H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `inv_mem_iff`：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvM
emClass S G] {H : S} {x : G} : x⁻¹ in H ↔ x in H
-/
theorem inv_coe_set [InvolutiveInv G] [SetLike S G] [InvMemClass S G] {H : S} : (H : Set G)⁻¹ = H :=
  Set.ext fun _ => inv_mem_iff

@[to_additive (attr := simp)]
/-
**smul_coe_set** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G} (
ha : a in s) : a • (s : Set G) = s
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G} (ha : a ∈ s) :
    a • (s : Set G) = s := by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_left, ha]

@[norm_cast, to_additive]
/-
**coe_set_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_set_eq_one [Group G] {s : Subgroup G} : (s : Set G) = 1 ↔ s = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma coe_set_eq_one [Group G] {s : Subgroup G} : (s : Set G) = 1 ↔ s = ⊥ :=
  (SetLike.ext'_iff.trans (by rfl)).symm

@[to_additive (attr := simp)]
/-
**op_smul_coe_set** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：op_smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G
} (ha : a in s) : MulOpposite.op a • (s : Set G) = s
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma op_smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G} (ha : a ∈ s) :
    MulOpposite.op a • (s : Set G) = s := by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_right, ha]

@[to_additive (attr := simp, norm_cast)]
/-
**coe_div_coe** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_div_coe [SetLike S G] [DivisionMonoid G] [SubgroupClass S G] (H : S) :
 H / H = (H : Set G)
参数：H : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_coe_set`：inv_coe_set [InvolutiveInv G] [SetLike S G] [InvMemClass S 
G] {H : S} : (H : Set G)⁻¹ = H
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用引理 `coe_mul_coe`：coe_mul_coe [SetLike S M] [SubmonoidClass S M] (H : S) : H 
* H = (H : Set M)
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_div_coe [SetLike S G] [DivisionMonoid G] [SubgroupClass S G] (H : S) :
    H / H = (H : Set G) := by simp [div_eq_mul_inv]

variable [Group G] [AddGroup A] {s : Set G}

namespace Set

open Subgroup

@[to_additive (attr := simp)]
/-
**Set.mul_subgroupClosure** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mul_subgroupClosure (hs : s.Nonempty) : s * closure s = closure s
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `Set.iUnion_smul_set`：iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a in s,
 a • t = s • t
· 使用引理 `smul_coe_set`：smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {
s : S} {a : G} (ha : a in s) : a • (s : Set G) = s
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.biUnion_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.Nonemp
ty → ∀ (t : Set β), ⋃ a ∈ s, t = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_subgroupClosure (hs : s.Nonempty) : s * closure s = closure s := by
  rw [← smul_eq_mul, ← Set.iUnion_smul_set]
  have h a (ha : a ∈ s) : a • (closure s : Set G) = closure s :=
    smul_coe_set <| subset_closure ha
  simp +contextual [h, hs]

open scoped RightActions in
@[to_additive (attr := simp)]
/-
**Set.subgroupClosure_mul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subgroupClosure_mul (hs : s.Nonempty) : closure s * s = closure s
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_op_smul_set`：iUnion_op_smul_set (s t : Set α) : ⋃ a in t, Mul
Opposite.op a • s = s * t
· 使用引理 `op_smul_coe_set`：op_smul_coe_set [Group G] [SetLike S G] [SubgroupClass 
S G] {s : S} {a : G} (ha : a in s) : MulOpposite.op a • (s : Set G) = s
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.biUnion_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.Nonemp
ty → ∀ (t : Set β), ⋃ a ∈ s, t = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subgroupClosure_mul (hs : s.Nonempty) : closure s * s = closure s := by
  rw [← Set.iUnion_op_smul_set]
  have h a (ha : a ∈ s) : (closure s : Set G) <• a = closure s :=
    op_smul_coe_set <| subset_closure ha
  simp +contextual [h, hs]

@[to_additive (attr := simp)]
/-
**Set.pow_mul_subgroupClosure** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] {s : Set G},   s.Nonempty → ∀ (n : ℕ), s
 ^ n * ↑(Subgroup.closure s) = ↑(Subgroup.closure s)
参数：n : ℕ；Subgroup.closure s；Subgroup.closure s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_mul_subgroupClosure (hs : s.Nonempty) : ∀ n, s ^ n * closure s = closure s
  | 0 => by simp
  | n + 1 => by rw [pow_succ, mul_assoc, mul_subgroupClosure hs, pow_mul_subgroupClosure hs]

@[to_additive (attr := simp)]
/-
**Set.subgroupClosure_mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] {s : Set G},   s.Nonempty → ∀ (n : ℕ), ↑
(Subgroup.closure s) * s ^ n = ↑(Subgroup.closure s)
参数：n : ℕ；Subgroup.closure s；Subgroup.closure s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subgroupClosure_mul_pow (hs : s.Nonempty) : ∀ n, closure s * s ^ n = closure s
  | 0 => by simp
  | n + 1 => by rw [pow_succ', ← mul_assoc, subgroupClosure_mul hs, subgroupClosure_mul_pow hs]

end Set

namespace Subgroup

@[to_additive (attr := simp)]
/-
**Subgroup.inv_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：inv_subset_closure (S : Set G) : S⁻¹ subseteq closure S
参数：S : Set G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.inv_mem_iff`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G)
 {x : G}, x⁻¹ ∈ H ↔ x ∈ H
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_inv`：mem_inv : a in s⁻¹ ↔ a⁻¹ in s
-/
theorem inv_subset_closure (S : Set G) : S⁻¹ ⊆ closure S := fun s hs => by
  rw [SetLike.mem_coe, ← Subgroup.inv_mem_iff]
  exact subset_closure (mem_inv.mp hs)

@[to_additive]
/-
**Subgroup.closure_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：closure_toSubmonoid (S : Set G) : (closure S).toSubmonoid = Submonoid.clos
ure (S union S⁻¹)
参数：S : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.closure_induction`：closure_induction {p : (g : G) -> g in closu
re k -> Prop} (mem : forall x (hx : x in k), p x (subset_closure hx)) (one : p 1
 (one_mem _)) (m…
· 使用定理 `Submonoid.closure_mono`：closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : 
closure s <= closure t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submonoid.mem_closure_inv`：mem_closure_inv (s : Set G) (x : G) : x in cl
osure s⁻¹ ↔ x⁻¹ in closure s
· 使用定理 `Set.union_inv`：union_inv : (s union t)⁻¹ = s⁻¹ union t⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem closure_toSubmonoid (S : Set G) :
    (closure S).toSubmonoid = Submonoid.closure (S ∪ S⁻¹) := by
  refine le_antisymm (fun x hx => ?_) (Submonoid.closure_le.2 ?_)
  · refine
      closure_induction
        (fun x hx => Submonoid.closure_mono subset_union_left (Submonoid.subset_closure hx))
        (Submonoid.one_mem _) (fun x y _ _ hx hy => Submonoid.mul_mem _ hx hy) (fun x _ hx => ?_) hx
    rwa [← Submonoid.mem_closure_inv, Set.union_inv, inv_inv, Set.union_comm]
  · simp only [true_and, coe_toSubmonoid, union_subset_iff, subset_closure, inv_subset_closure]

@[to_additive]
/-
**Subgroup.toSubmonoid_zpowers** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：toSubmonoid_zpowers (g : G) : (Subgroup.zpowers g).toSubmonoid = Submonoid
.powers g ⊔ Submonoid.powers g⁻¹
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.zpowers_eq_closure`：zpowers_eq_closure (g : G) : zpowers g = cl
osure {g}
· 使用定理 `Subgroup.closure_toSubmonoid`：closure_toSubmonoid (S : Set G) : (closure
 S).toSubmonoid = Submonoid.closure (S union S⁻¹)
· 使用定理 `Submonoid.closure_union`：closure_union (s t : Set M) : closure (s union 
t) = closure s ⊔ closure t
· 使用定理 `Submonoid.powers_eq_closure`：powers_eq_closure (n : M) : powers n = clos
ure {n}
· 使用定理 `Set.inv_singleton`：inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹}
-/
lemma toSubmonoid_zpowers (g : G) :
    (Subgroup.zpowers g).toSubmonoid = Submonoid.powers g ⊔ Submonoid.powers g⁻¹ := by
  rw [zpowers_eq_closure, closure_toSubmonoid, Submonoid.closure_union,
    Submonoid.powers_eq_closure, Submonoid.powers_eq_closure, Set.inv_singleton]

@[to_additive]
/-
**Subgroup._root_.Submonoid.powers_le_zpowers** 是 Mathlib 中的一个引理，位于命名空间 `Subgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Submonoid.powers_le_zpowers (g : G) :
    Submonoid.powers g ≤ (Subgroup.zpowers g).toSubmonoid := by
  rw [toSubmonoid_zpowers]
  exact le_sup_left

/-- For subgroups generated by a single element, see the simpler `zpow_induction_left`. -/
@[to_additive (attr := elab_as_elim)
  /-- For additive subgroups generated by a single element, see the simpler
  `zsmul_induction_left`. -/]
/-
**Subgroup.closure_induction_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：closure_induction_left {p : (x : G) -> x in closure s -> Prop} (one : p 1 
(one_mem _)) (mul_left : forall x (hx : x in s), forall (y) hy, p y hy -> p (x *
 y) (mul_mem (subset_closure hx) hy)) (inv_mul_cancel : forall x (hx : x in s), 
forall (y) hy, p y hy -> p (x⁻¹ * y) (mul_mem (inv_mem (subset_closure hx)) hy))
 {x : G} (h : x in closure s) : p x h
参数：x : G；one : p 1 (one_mem _)；mul_left : forall x (hx : x in s), forall (y) hy,
 p y hy -> p (x * y) (mul_mem (subset_closure hx) hy)；inv_mul_cancel : forall x 
(hx : x in s), forall (y) hy, p y hy -> p (x⁻¹ * y) (mul_mem (inv_mem (subset_cl
osure hx)) hy)；h : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.closure_toSubmonoid`：closure_toSubmonoid (S : Set G) : (closure
 S).toSubmonoid = Submonoid.closure (S union S⁻¹)
· 使用定理 `Submonoid.closure_induction_left`：closure_induction_left {s : Set M} {mo
tive : (m : M) -> m in closure s -> Prop} (one : motive 1 (one_mem _)) (mul_left
 : forall x (hx : x in…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem closure_induction_left {p : (x : G) → x ∈ closure s → Prop} (one : p 1 (one_mem _))
    (mul_left : ∀ x (hx : x ∈ s), ∀ (y) hy, p y hy → p (x * y) (mul_mem (subset_closure hx) hy))
    (inv_mul_cancel : ∀ x (hx : x ∈ s), ∀ (y) hy, p y hy →
      p (x⁻¹ * y) (mul_mem (inv_mem (subset_closure hx)) hy))
    {x : G} (h : x ∈ closure s) : p x h := by
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
/-
**Subgroup.closure_induction_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：closure_induction_right {p : (x : G) -> x in closure s -> Prop} (one : p 1
 (one_mem _)) (mul_right : forall (x) hx, forall y (hy : y in s), p x hx -> p (x
 * y) (mul_mem hx (subset_closure hy))) (mul_inv_cancel : forall (x) hx, forall 
y (hy : y in s), p x hx -> p (x * y⁻¹) (mul_mem hx (inv_mem (subset_closure hy))
)) {x : G} (h : x in closure s) : p x h
参数：x : G；one : p 1 (one_mem _)；mul_right : forall (x) hx, forall y (hy : y in s)
, p x hx -> p (x * y) (mul_mem hx (subset_closure hy))；mul_inv_cancel : forall (
x) hx, forall y (hy : y in s), p x hx -> p (x * y⁻¹) (mul_mem hx (inv_mem (subse
t_closure hy)))；h : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.closure_induction_left`：closure_induction_left {p : (x : G) -> 
x in closure s -> Prop} (one : p 1 (one_mem _)) (mul_left : forall x (hx : x in 
s), forall (y) hy, p …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.op_closure`：op_closure (s : Set G) : (closure s).op = closure (
MulOpposite.unop ⁻¹' s)
-/
theorem closure_induction_right {p : (x : G) → x ∈ closure s → Prop} (one : p 1 (one_mem _))
    (mul_right : ∀ (x) hx, ∀ y (hy : y ∈ s), p x hx → p (x * y) (mul_mem hx (subset_closure hy)))
    (mul_inv_cancel : ∀ (x) hx, ∀ y (hy : y ∈ s), p x hx →
      p (x * y⁻¹) (mul_mem hx (inv_mem (subset_closure hy))))
    {x : G} (h : x ∈ closure s) : p x h :=
  closure_induction_left (s := MulOpposite.unop ⁻¹' s)
    (p := fun m hm => p m.unop <| by rwa [← op_closure] at hm)
    one
    (fun _x hx _y _ => mul_right _ _ _ hx)
    (fun _x hx _y _ => mul_inv_cancel _ _ _ hx)
    (by rwa [← op_closure])

@[to_additive (attr := simp)]
/-
**Subgroup.closure_inv** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：closure_inv (s : Set G) : closure s⁻¹ = closure s
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.closure_toSubmonoid`：closure_toSubmonoid (S : Set G) : (closure
 S).toSubmonoid = Submonoid.closure (S union S⁻¹)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_inv (s : Set G) : closure s⁻¹ = closure s := by
  simp only [← toSubmonoid_inj, closure_toSubmonoid, inv_inv, union_comm]

@[to_additive (attr := simp)]
/-
**Subgroup.closure_singleton_inv** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：closure_singleton_inv (x : G) : closure {x⁻¹} = closure {x}
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inv_singleton`：inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹}
· 使用定理 `Subgroup.closure_inv`：closure_inv (s : Set G) : closure s⁻¹ = closure s
-/
lemma closure_singleton_inv (x : G) : closure {x⁻¹} = closure {x} := by
  rw [← Set.inv_singleton, closure_inv]

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of
`k` and their inverse, and is preserved under multiplication, then `p` holds for all elements of
the closure of `k`. -/
@[to_additive (attr := elab_as_elim)
  /-- An induction principle for additive closure membership. If `p` holds for `0` and all
  elements of `k` and their negation, and is preserved under addition, then `p` holds for all
  elements of the additive closure of `k`. -/]
/-
**Subgroup.closure_induction''** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：closure_induction'' {p : (g : G) -> g in closure s -> Prop} (mem : forall 
x (hx : x in s), p x (subset_closure hx)) (inv_mem : forall x (hx : x in s), p x
⁻¹ (inv_mem (subset_closure hx))) (one : p 1 (one_mem _)) (mul : forall x y hx h
y, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) {x} (h : x in closure s) : p x
 h
参数：g : G；mem : forall x (hx : x in s), p x (subset_closure hx)；inv_mem : forall 
x (hx : x in s), p x⁻¹ (inv_mem (subset_closure hx))；one : p 1 (one_mem _)；mul :
 forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；h : x in closur
e s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Subgroup.closure_induction_left`：closure_induction_left {p : (x : G) -> 
x in closure s -> Prop} (one : p 1 (one_mem _)) (mul_left : forall x (hx : x in 
s), forall (y) hy, p …
-/
theorem closure_induction'' {p : (g : G) → g ∈ closure s → Prop}
    (mem : ∀ x (hx : x ∈ s), p x (subset_closure hx))
    (inv_mem : ∀ x (hx : x ∈ s), p x⁻¹ (inv_mem (subset_closure hx)))
    (one : p 1 (one_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (h : x ∈ closure s) : p x h :=
  closure_induction_left one (fun x hx y _ hy => mul x y _ _ (mem x hx) hy)
    (fun x hx y _ => mul x⁻¹ y _ _ <| inv_mem x hx) h

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `1` and all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[to_additive (attr := elab_as_elim) /-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `0` and all elements of `S i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `S`. -/]
/-
**Subgroup.iSup_induction** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：iSup_induction {ι : Sort*} (S : ι -> Subgroup G) {C : G -> Prop} {x : G} (
hx : x in ⨆ i, S i) (mem : forall (i), forall x in S i, C x) (one : C 1) (mul : 
forall x y, C x -> C y -> C (x * y)) : C x
参数：S : ι -> Subgroup G；hx : x in ⨆ i, S i；mem : forall (i), forall x in S i, C x
；one : C 1；mul : forall x y, C x -> C y -> C (x * y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.closure_induction''`：closure_induction'' {p : (g : G) -> g in c
losure s -> Prop} (mem : forall x (hx : x in s), p x (subset_closure hx)) (inv_m
em : forall x (hx …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.iSup_eq_closure`：iSup_eq_closure {ι : Sort*} (p : ι -> Subgroup
 G) : ⨆ i, p i = closure (⋃ i, (p i : Set G))
-/
theorem iSup_induction {ι : Sort*} (S : ι → Subgroup G) {C : G → Prop} {x : G} (hx : x ∈ ⨆ i, S i)
    (mem : ∀ (i), ∀ x ∈ S i, C x) (one : C 1) (mul : ∀ x y, C x → C y → C (x * y)) : C x := by
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
/-
**Subgroup.iSup_induction'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：iSup_induction' {ι : Sort*} (S : ι -> Subgroup G) {C : forall x, (x in ⨆ i
, S i) -> Prop} (hp : forall (i), forall x (hx : x in S i), C x (mem_iSup_of_mem
 i hx)) (h1 : C 1 (one_mem _)) (hmul : forall x y hx hy, C x hx -> C y hy -> C (
x * y) (mul_mem ‹_› ‹_›)) {x : G} (hx : x in ⨆ i, S i) : C x hx
参数：S : ι -> Subgroup G；x in ⨆ i, S i；hp : forall (i), forall x (hx : x in S i), 
C x (mem_iSup_of_mem i hx)；h1 : C 1 (one_mem _)；hmul : forall x y hx hy, C x hx 
-> C y hy -> C (x * y) (mul_mem ‹_› ‹_›)；hx : x in ⨆ i, S i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {S : ι -> Subgroup
 G} (i : ι) : forall {x : G}, x in S i -> x in iSup S
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Subgroup.iSup_induction`：iSup_induction {ι : Sort*} (S : ι -> Subgroup G
) {C : G -> Prop} {x : G} (hx : x in ⨆ i, S i) (mem : forall (i), forall x in S 
i, C x) (one …
· 使用定理 `Exists.snd`：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯

--- 原说明 ---
A dependent version of `Subgroup.iSup_induction`.
-/
theorem iSup_induction' {ι : Sort*} (S : ι → Subgroup G) {C : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (hp : ∀ (i), ∀ x (hx : x ∈ S i), C x (mem_iSup_of_mem i hx)) (h1 : C 1 (one_mem _))
    (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›)) {x : G}
    (hx : x ∈ ⨆ i, S i) : C x hx := by
  suffices ∃ h, C x h from this.snd
  refine iSup_induction S (C := fun x => ∃ h, C x h) hx (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, hp i _ hx⟩
  · exact ⟨_, h1⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, hmul _ _ _ _ Cx Cy⟩

@[to_additive (attr := simp)]
/-
**Subgroup.mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mul_subset {t : Set G} {H : Subgroup G} (hs : s subseteq H) (ht : t subset
eq H) : s * t subseteq H
参数：hs : s subseteq H；ht : t subseteq H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mul_subset`：mul_subset {S : Submonoid M} (hs : s subseteq S) (
ht : t subseteq S) : s * t subseteq S
-/
theorem mul_subset {t : Set G} {H : Subgroup G} (hs : s ⊆ H) (ht : t ⊆ H) : s * t ⊆ H :=
  Submonoid.mul_subset hs ht

@[to_additive (attr := simp)]
/-
**Subgroup.pow_subset** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：pow_subset {H : Subgroup G} {n : Nat} (hs : s subseteq H) : s ^ n subseteq
 H
参数：hs : s subseteq H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
lemma pow_subset {H : Subgroup G} {n : ℕ} (hs : s ⊆ H) : s ^ n ⊆ H := by
  induction n <;> simp [pow_succ, *]

@[to_additive]
/-
**Subgroup.closure_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：closure_mul_le (S T : Set G) : closure (S * T) <= closure S ⊔ closure T
参数：S T : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem closure_mul_le (S T : Set G) : closure (S * T) ≤ closure S ⊔ closure T :=
  sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)

@[to_additive]
/-
**Subgroup.closure_pow_le** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：closure_pow_le {n : Nat} : closure (s ^ n) <= closure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma closure_pow_le {n : ℕ} : closure (s ^ n) ≤ closure s := by simp

@[to_additive]
/-
**Subgroup.closure_pow_anti** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：closure_pow_anti {m n : Nat} (hmn : m ∣ n) : closure (s ^ n) <= closure (s
 ^ m)
参数：hmn : m ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma closure_pow_anti {m n : ℕ} (hmn : m ∣ n) : closure (s ^ n) ≤ closure (s ^ m) := by
  obtain ⟨k, rfl⟩ := hmn
  simp [pow_mul]

@[to_additive]
/-
**Subgroup.closure_pow** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：closure_pow {n : Nat} (hs : 1 in s) (hn : n != 0) : closure (s ^ n) = clos
ure s
参数：hs : 1 in s；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Subgroup.closure_pow_le`：closure_pow_le {n : Nat} : closure (s ^ n) <= c
losure s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subgroup.closure_mono`：closure_mono ⦃h k : Set G⦄ (h' : h subseteq k) : 
closure h <= closure k
· 使用引理 `Set.subset_pow`：subset_pow (hs : 1 in s) (hn : n != 0) : s subseteq s ^ 
n
-/
lemma closure_pow {n : ℕ} (hs : 1 ∈ s) (hn : n ≠ 0) : closure (s ^ n) = closure s :=
  closure_pow_le.antisymm <| by grw [← subset_pow hs hn]

@[to_additive]
/-
**Subgroup.sup_eq_closure_mul** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：sup_eq_closure_mul (H K : Subgroup G) : H ⊔ K = closure ((H : Set G) * (K 
: Set G))
参数：H K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.closure_mul_le`：closure_mul_le (S T : Set G) : closure (S * T) 
<= closure S ⊔ closure T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.closure_eq`：closure_eq : closure (K : Set G) = K
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem sup_eq_closure_mul (H K : Subgroup G) : H ⊔ K = closure ((H : Set G) * (K : Set G)) :=
  le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

@[to_additive]
/-
**Subgroup.set_mul_normalizer_comm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：set_mul_normalizer_comm (S : Set G) (N : Subgroup G) (hLE : S subseteq nor
malizer (N : Set G)) : S * N = N * S
参数：S : Set G；N : Subgroup G；hLE : S subseteq normalizer (N : Set G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_mul_left_image`：iUnion_mul_left_image : ⋃ a in s, (a * ·) '' 
t = s * t
· 使用定理 `Set.iUnion_mul_right_image`：iUnion_mul_right_image : ⋃ a in t, (· * a) '
' s = s * t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_normalizer_iff'`：mem_normalizer_iff' : g in normalizer H ↔ 
forall n, n * g in H ↔ g * n in H
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem set_mul_normalizer_comm (S : Set G) (N : Subgroup G) (hLE : S ⊆ normalizer (N : Set G)) :
    S * N = N * S := by
  rw [← iUnion_mul_left_image, ← iUnion_mul_right_image]
  simp only [image_mul_left, image_mul_right, Set.preimage]
  congr! 5 with s hs x
  exact (mem_normalizer_iff'.mp (inv_mem (hLE hs)) x).symm

@[to_additive]
/-
**Subgroup.set_mul_normal_comm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：set_mul_normal_comm (S : Set G) (N : Subgroup G) [hN : N.Normal] : S * (N 
: Set G) = (N : Set G) * S
参数：S : Set G；N : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.set_mul_normalizer_comm`：set_mul_normalizer_comm (S : Set G) (N
 : Subgroup G) (hLE : S subseteq normalizer (N : Set G)) : S * N = N * S
· 使用定理 `Subgroup.subset_normalizer_of_normal`：subset_normalizer_of_normal {S : S
et G} [hH : H.Normal] : S subseteq normalizer (H : Set G)
-/
theorem set_mul_normal_comm (S : Set G) (N : Subgroup G) [hN : N.Normal] :
    S * (N : Set G) = (N : Set G) * S := set_mul_normalizer_comm S N subset_normalizer_of_normal

/-- The carrier of `H ⊔ N` is just `↑H * ↑N` (pointwise set product)
when `H` is a subgroup of the normalizer of `N` in `G`. -/
@[to_additive /-- The carrier of `H ⊔ N` is just `↑H + ↑N` (pointwise set addition)
when `H` is a subgroup of the normalizer of `N` in `G`. -/]
/-
**Subgroup.coe_mul_of_left_le_normalizer_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
形式化陈述：coe_mul_of_left_le_normalizer_right (H N : Subgroup G) (hLE : H <= normali
zer N) : (↑(H ⊔ N) : Set G) = H * N
参数：H N : Subgroup G；hLE : H <= normalizer N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.sup_eq_closure_mul`：sup_eq_closure_mul (H K : Subgroup G) : H ⊔
 K = closure ((H : Set G) * (K : Set G))
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Subgroup.closure_induction''`：closure_induction'' {p : (g : G) -> g in c
losure s -> Prop} (mem : forall x (hx : x in s), p x (subset_closure hx)) (inv_m
em : forall x (hx …
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_normalizer_iff`：mem_normalizer_iff : g in normalizer H ↔ fo
rall h, h in H ↔ g * h * g⁻¹ in H
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Subgroup.mem_normalizer_iff''`：mem_normalizer_iff'' : g in normalizer H 
↔ forall h : G, h in H ↔ g⁻¹ * h * g in H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
-/
theorem coe_mul_of_left_le_normalizer_right (H N : Subgroup G) (hLE : H ≤ normalizer N) :
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
/-
**Subgroup.coe_mul_of_right_le_normalizer_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
形式化陈述：coe_mul_of_right_le_normalizer_left (N H : Subgroup G) (hLE : H <= normali
zer N) : (↑(N ⊔ H) : Set G) = N * H
参数：N H : Subgroup G；hLE : H <= normalizer N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.set_mul_normalizer_comm`：set_mul_normalizer_comm (S : Set G) (N
 : Subgroup G) (hLE : S subseteq normalizer (N : Set G)) : S * N = N * S
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Subgroup.coe_mul_of_left_le_normalizer_right`：coe_mul_of_left_le_normali
zer_right (H N : Subgroup G) (hLE : H <= normalizer N) : (↑(H ⊔ N) : Set G) = H 
* N
-/
theorem coe_mul_of_right_le_normalizer_left (N H : Subgroup G) (hLE : H ≤ normalizer N) :
    (↑(N ⊔ H) : Set G) = N * H := by
  rw [← set_mul_normalizer_comm _ _ hLE, sup_comm, coe_mul_of_left_le_normalizer_right _ _ hLE]

/-- The carrier of `H ⊔ N` is just `↑H * ↑N` (pointwise set product) when `N` is normal. -/
@[to_additive /-- The carrier of `H ⊔ N` is just `↑H + ↑N` (pointwise set addition)
when `N` is normal. -/]
/-
**Subgroup.mul_normal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mul_normal (H N : Subgroup G) [hN : N.Normal] : (↑(H ⊔ N) : Set G) = H * N
参数：H N : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.coe_mul_of_left_le_normalizer_right`：coe_mul_of_left_le_normali
zer_right (H N : Subgroup G) (hLE : H <= normalizer N) : (↑(H ⊔ N) : Set G) = H 
* N
· 使用定理 `Subgroup.le_normalizer_of_normal`：le_normalizer_of_normal [H.Normal] : K
 <= normalizer H
-/
theorem mul_normal (H N : Subgroup G) [hN : N.Normal] : (↑(H ⊔ N) : Set G) = H * N :=
  coe_mul_of_left_le_normalizer_right H N le_normalizer_of_normal

/-- The carrier of `N ⊔ H` is just `↑N * ↑H` (pointwise set product) when `N` is normal. -/
@[to_additive /-- The carrier of `N ⊔ H` is just `↑N + ↑H` (pointwise set addition)
when `N` is normal. -/]
/-
**Subgroup.normal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_mul (N H : Subgroup G) [N.Normal] : (↑(N ⊔ H) : Set G) = N * H
参数：N H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.coe_mul_of_right_le_normalizer_left`：coe_mul_of_right_le_normal
izer_left (N H : Subgroup G) (hLE : H <= normalizer N) : (↑(N ⊔ H) : Set G) = N 
* H
· 使用定理 `Subgroup.le_normalizer_of_normal`：le_normalizer_of_normal [H.Normal] : K
 <= normalizer H
-/
theorem normal_mul (N H : Subgroup G) [N.Normal] : (↑(N ⊔ H) : Set G) = N * H :=
  coe_mul_of_right_le_normalizer_left N H le_normalizer_of_normal

@[to_additive]
/-
**Subgroup.mul_inf_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mul_inf_assoc (A B C : Subgroup G) (h : A <= C) : (A : Set G) * ↑(B ⊓ C) =
 (A : Set G) * (B : Set G) inter C
参数：A B C : Subgroup G；h : A <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem mul_inf_assoc (A B C : Subgroup G) (h : A ≤ C) :
    (A : Set G) * ↑(B ⊓ C) = (A : Set G) * (B : Set G) ∩ C := by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, z, ⟨hzB, hzC⟩, rfl⟩
    refine ⟨?_, mul_mem (h hy) hzC⟩
    exact ⟨y, hy, z, hzB, rfl⟩
  rintro ⟨⟨y, hy, z, hz, rfl⟩, hyz⟩
  refine ⟨y, hy, z, ⟨hz, ?_⟩, rfl⟩
  suffices y⁻¹ * (y * z) ∈ C by simpa
  exact mul_mem (inv_mem (h hy)) hyz

@[to_additive]
/-
**Subgroup.inf_mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：inf_mul_assoc (A B C : Subgroup G) (h : C <= A) : ((A ⊓ B : Subgroup G) : 
Set G) * C = (A : Set G) inter (↑B * ↑C)
参数：A B C : Subgroup G；h : C <= A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
theorem inf_mul_assoc (A B C : Subgroup G) (h : C ≤ A) :
    ((A ⊓ B : Subgroup G) : Set G) * C = (A : Set G) ∩ (↑B * ↑C) := by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, z, hz, rfl⟩
    refine ⟨A.mul_mem hyA (h hz), ?_⟩
    exact ⟨y, hyB, z, hz, rfl⟩
  rintro ⟨hyz, y, hy, z, hz, rfl⟩
  refine ⟨y, ⟨?_, hy⟩, z, hz, rfl⟩
  suffices y * z * z⁻¹ ∈ A by simpa
  exact mul_mem hyz (inv_mem (h hz))

@[to_additive]
/-
**Subgroup.normalizer_inf_normalizer_le_normalizer_sup** 是 Mathlib 中的一个引理，位于命名空间
 `Subgroup`。
形式化陈述：normalizer_inf_normalizer_le_normalizer_sup (H K : Subgroup G) : normalize
r H ⊓ normalizer K <= normalizer ((H ⊔ K : Subgroup G) : Set G)
参数：H K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_sup`：map_sup (H K : Subgroup G) (f : G ->* N) : (H ⊔ K).map
 f = H.map f ⊔ K.map f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normalizer_inf_normalizer_le_normalizer_sup (H K : Subgroup G) :
    normalizer H ⊓ normalizer K ≤ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  intro g hg
  simp_rw [mem_inf, mem_normalizer_iff_map_conj_eq, map_sup, hg.1, hg.2] at hg ⊢

@[to_additive]
/-
**Subgroup.iInf_normalizer_le_normalizer_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：iInf_normalizer_le_normalizer_iSup {ι : Sort*} (H : ι -> Subgroup G) : ⨅ i
, normalizer (H i) <= normalizer ((⨆ i, H i : Subgroup G) : Set G)
参数：H : ι -> Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_iSup`：map_iSup {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup
 G) : (iSup s).map f = ⨆ i, (s i).map f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_normalizer_le_normalizer_iSup {ι : Sort*} (H : ι → Subgroup G) :
    ⨅ i, normalizer (H i) ≤ normalizer ((⨆ i, H i : Subgroup G) : Set G) := by
  intro g hg
  simp_rw [mem_iInf, mem_normalizer_iff_map_conj_eq, map_iSup, hg] at hg ⊢

@[to_additive]
/-
**Subgroup.conj_mem_sup_of_mem_inf_normalizer_of_mem_inf** 是 Mathlib 中的一个引理，位于命名
空间 `Subgroup`。
形式化陈述：conj_mem_sup_of_mem_inf_normalizer_of_mem_inf {H K : Subgroup G} {s : G} (
hs : s in normalizer H ⊓ normalizer K) (g : G) (hg : g in H ⊔ K) : s * g * s⁻¹ i
n H ⊔ K
参数：hs : s in normalizer H ⊓ normalizer K；g : G；hg : g in H ⊔ K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subgroup.normalizer_inf_normalizer_le_normalizer_sup`：normalizer_inf_nor
malizer_le_normalizer_sup (H K : Subgroup G) : normalizer H ⊓ normalizer K <= no
rmalizer ((H ⊔ K : Subgroup G) : Set G)
-/
lemma conj_mem_sup_of_mem_inf_normalizer_of_mem_inf
    {H K : Subgroup G} {s : G} (hs : s ∈ normalizer H ⊓ normalizer K) (g : G) (hg : g ∈ H ⊔ K) :
    s * g * s⁻¹ ∈ H ⊔ K :=
  (normalizer_inf_normalizer_le_normalizer_sup H K hs g).mp hg

@[to_additive]
/-
**Subgroup.normalizer_le_normalizer_sup_of_normalizer_le_left** 是 Mathlib 中的一个引理
，位于命名空间 `Subgroup`。
形式化陈述：normalizer_le_normalizer_sup_of_normalizer_le_left {H K : Subgroup G} (hHn
K : normalizer H <= normalizer (K : Set G)) : normalizer H <= normalizer ((H ⊔ K
 : Subgroup G) : Set G)
参数：hHnK : normalizer H <= normalizer (K : Set G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用引理 `Subgroup.normalizer_inf_normalizer_le_normalizer_sup`：normalizer_inf_nor
malizer_le_normalizer_sup (H K : Subgroup G) : normalizer H ⊓ normalizer K <= no
rmalizer ((H ⊔ K : Subgroup G) : Set G)
-/
lemma normalizer_le_normalizer_sup_of_normalizer_le_left
    {H K : Subgroup G} (hHnK : normalizer H ≤ normalizer (K : Set G)) :
    normalizer H ≤ normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  (inf_of_le_left hHnK).symm.trans_le (H.normalizer_inf_normalizer_le_normalizer_sup K)

@[to_additive]
/-
**Subgroup.normalizer_le_normalizer_sup_of_normalizer_le_right** 是 Mathlib 中的一个引
理，位于命名空间 `Subgroup`。
形式化陈述：normalizer_le_normalizer_sup_of_normalizer_le_right {H K : Subgroup G} (hH
nK : normalizer H <= normalizer (K : Set G)) : normalizer H <= normalizer ((K ⊔ 
H : Subgroup G) : Set G)
参数：hHnK : normalizer H <= normalizer (K : Set G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用引理 `Subgroup.normalizer_le_normalizer_sup_of_normalizer_le_left`：normalizer_
le_normalizer_sup_of_normalizer_le_left {H K : Subgroup G} (hHnK : normalizer H 
<= normalizer (K : Set G)) : normalizer H <= norm…
-/
lemma normalizer_le_normalizer_sup_of_normalizer_le_right {H K : Subgroup G}
    (hHnK : normalizer H ≤ normalizer (K : Set G)) :
    normalizer H ≤ normalizer ((K ⊔ H : Subgroup G) : Set G) := by
  rw [sup_comm]
  exact normalizer_le_normalizer_sup_of_normalizer_le_left hHnK

@[to_additive]
/-
**Subgroup.normalizer_le_normalizer_sup_normal** 是 Mathlib 中的一个引理，位于命名空间 `Subgro
up`。
形式化陈述：normalizer_le_normalizer_sup_normal {H K : Subgroup G} [hK : K.Normal] : n
ormalizer H <= normalizer ((H ⊔ K : Subgroup G) : Set G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.normalizer_le_normalizer_sup_of_normalizer_le_left`：normalizer_
le_normalizer_sup_of_normalizer_le_left {H K : Subgroup G} (hHnK : normalizer H 
<= normalizer (K : Set G)) : normalizer H <= norm…
· 使用定理 `Subgroup.le_normalizer_of_normal`：le_normalizer_of_normal [H.Normal] : K
 <= normalizer H
-/
lemma normalizer_le_normalizer_sup_normal {H K : Subgroup G} [hK : K.Normal] :
    normalizer H ≤ normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  normalizer_le_normalizer_sup_of_normalizer_le_left le_normalizer_of_normal

@[to_additive]
/-
**Subgroup.sup_normal** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：sup_normal (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal] : (H ⊔ K).No
rmal where conj_mem n hmem g
参数：H K : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subgroup.normal_mul`：normal_mul (N H : Subgroup G) [N.Normal] : (↑(N ⊔ H
) : Set G) = N * H
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance sup_normal (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal] : (H ⊔ K).Normal where
  conj_mem n hmem g := by
    rw [← SetLike.mem_coe, normal_mul] at hmem ⊢
    rcases hmem with ⟨h, hh, k, hk, rfl⟩
    refine ⟨g * h * g⁻¹, hH.conj_mem h hh g, g * k * g⁻¹, hK.conj_mem k hk g, ?_⟩
    simp only [mul_assoc, inv_mul_cancel_left]

@[to_additive]
/-
**Subgroup.iSup_normal** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：iSup_normal {ι : Sort*} (H : ι -> Subgroup G) [forall i, (H i).Normal] : .
Normal
参数：H : ι -> Subgroup G；H i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subgroup.iInf_normalizer_le_normalizer_iSup`：iInf_normalizer_le_normaliz
er_iSup {ι : Sort*} (H : ι -> Subgroup G) : ⨅ i, normalizer (H i) <= normalizer 
((⨆ i, H i : Subgroup G) : Set G)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.normalizer_eq_top`：normalizer_eq_top [h : H.Normal] : normalize
r (H : Set G) = ⊤
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
-/
instance iSup_normal {ι : Sort*} (H : ι → Subgroup G) [∀ i, (H i).Normal] :
    ⨆ i, H i |>.Normal := by
  grw [← normalizer_eq_top_iff, eq_top_iff, ← iInf_normalizer_le_normalizer_iSup]
  simp [normalizer_eq_top]

@[to_additive]
/-
**Subgroup.biSup_normal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：biSup_normal {ι : Type*} (s : Set ι) (H : ι -> Subgroup G) (h : forall i i
n s, (H i).Normal) : .Normal
参数：s : Set ι；H : ι -> Subgroup G；h : forall i in s, (H i).Normal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem biSup_normal {ι : Type*} (s : Set ι) (H : ι → Subgroup G) (h : ∀ i ∈ s, (H i).Normal) :
    ⨆ i ∈ s, H i |>.Normal := by
  rw [← iSup_subtype'']
  have : ∀ i : s, (H i).Normal := fun i ↦ h i i.property
  apply iSup_normal

@[to_additive]
/-
**Subgroup.sSup_normal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] (Hs : Set (Subgroup G)), (∀ H ∈ Hs, H.No
rmal) → (sSup Hs).Normal
参数：Hs : Set (Subgroup G)；∀ H ∈ Hs, H.Normal；sSup Hs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `Subgroup.biSup_normal`：biSup_normal {ι : Type*} (s : Set ι) (H : ι -> Su
bgroup G) (h : forall i in s, (H i).Normal) : .Normal
-/
theorem sSup_normal (Hs : Set (Subgroup G)) (h : ∀ H ∈ Hs, H.Normal) : sSup Hs |>.Normal := by
  rw [sSup_eq_iSup]
  exact biSup_normal Hs id h

@[to_additive]
/-
**Subgroup.smul_mem_of_mem_closure_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_mem_of_mem_closure_of_mem {X : Type*} [MulAction G X] {s : Set G} {t 
: Set X} (hs : forall g in s, g⁻¹ in s) (hst : forallᵉ (g in s) (x in t), g • x 
in t) {g : G} (hg : g in Subgroup.closure s) {x : X} (hx : x in t) : g • x in t
参数：hs : forall g in s, g⁻¹ in s；hst : forallᵉ (g in s) (x in t), g • x in t；hg :
 g in Subgroup.closure s；hx : x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.closure_induction''`：closure_induction'' {p : (g : G) -> g in c
losure s -> Prop} (mem : forall x (hx : x in s), p x (subset_closure hx)) (inv_m
em : forall x (hx …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem smul_mem_of_mem_closure_of_mem {X : Type*} [MulAction G X] {s : Set G} {t : Set X}
    (hs : ∀ g ∈ s, g⁻¹ ∈ s) (hst : ∀ᵉ (g ∈ s) (x ∈ t), g • x ∈ t) {g : G}
    (hg : g ∈ Subgroup.closure s) {x : X} (hx : x ∈ t) : g • x ∈ t := by
  induction hg using Subgroup.closure_induction'' generalizing x with
  | one => simpa
  | mem g' hg' => exact hst g' hg' x hx
  | inv_mem g' hg' => exact hst g'⁻¹ (hs g' hg') x hx
  | mul _ _ _ _ h₁ h₂ => rw [mul_smul]; exact h₁ (h₂ hx)

@[to_additive]
/-
**Subgroup.smul_opposite_image_mul_preimage'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
`。
形式化陈述：smul_opposite_image_mul_preimage' (g : G) (h : Gᵐᵒᵖ) (s : Set G) : (fun y 
=> h • y) '' (g * ·) ⁻¹' s = (g * ·) ⁻¹' (fun y => h • y) '' s
参数：g : G；h : Gᵐᵒᵖ；s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_opposite_image_mul_preimage' (g : G) (h : Gᵐᵒᵖ) (s : Set G) :
    (fun y => h • y) '' (g * ·) ⁻¹' s = (g * ·) ⁻¹' (fun y => h • y) '' s := by
  simp [preimage_preimage, mul_assoc]

-- TODO: deprecate?
@[to_additive]
/-
**Subgroup.smul_opposite_image_mul_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`
。
形式化陈述：smul_opposite_image_mul_preimage {H : Subgroup G} (g : G) (h : H.op) (s : 
Set G) : (fun y => h • y) '' (g * ·) ⁻¹' s = (g * ·) ⁻¹' (fun y => h • y) '' s
参数：g : G；h : H.op；s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.smul_opposite_image_mul_preimage'`：smul_opposite_image_mul_prei
mage' (g : G) (h : Gᵐᵒᵖ) (s : Set G) : (fun y => h • y) '' (g * ·) ⁻¹' s = (g * 
·) ⁻¹' (fun y => h • y) '' s
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
/-
**Subgroup.pointwiseMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：{α : Type u_1} →   {G : Type u_2} → [inst : Group G] → [inst_1 : Monoid α]
 → [MulDistribMulAction α G] → MulAction α (Subgroup G)
参数：Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on a subgroup corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.
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
/-
**Subgroup.pointwise_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：pointwise_smul_def {a : α} (S : Subgroup G) : a • S = S.map (MulDistribMul
Action.toMonoidEnd _ _ a)
参数：S : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_def {a : α} (S : Subgroup G) :
    a • S = S.map (MulDistribMulAction.toMonoidEnd _ _ a) :=
  rfl

@[simp, norm_cast]
/-
**Subgroup.coe_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_pointwise_smul (a : α) (S : Subgroup G) : ↑(a • S) = a • (S : Set G)
参数：a : α；S : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pointwise_smul (a : α) (S : Subgroup G) : ↑(a • S) = a • (S : Set G) :=
  rfl

@[simp]
/-
**Subgroup.pointwise_smul_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：pointwise_smul_toSubmonoid (a : α) (S : Subgroup G) : (a • S).toSubmonoid 
= a • S.toSubmonoid
参数：a : α；S : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_toSubmonoid (a : α) (S : Subgroup G) :
    (a • S).toSubmonoid = a • S.toSubmonoid :=
  rfl
/-
**Subgroup.smul_mem_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_mem_pointwise_smul (m : G) (a : α) (S : Subgroup G) : m in S -> a • m
 in a • S
参数：m : G；a : α；S : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem smul_mem_pointwise_smul (m : G) (a : α) (S : Subgroup G) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set G))
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CovariantClass α (Subgroup G) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_mono⟩
/-
**Subgroup.mem_smul_pointwise_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_smul_pointwise_iff_exists (m : G) (a : α) (S : Subgroup G) : m in a • 
S ↔ exists s : G, s in S ∧ a • s = m
参数：m : G；a : α；S : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
-/
theorem mem_smul_pointwise_iff_exists (m : G) (a : α) (S : Subgroup G) :
    m ∈ a • S ↔ ∃ s : G, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set G) ↔ _)

@[simp]
/-
**Subgroup.smul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_bot (a : α) : a • (⊥ : Subgroup G) = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
-/
theorem smul_bot (a : α) : a • (⊥ : Subgroup G) = ⊥ :=
  map_bot _
/-
**Subgroup.smul_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_sup (a : α) (S T : Subgroup G) : a • (S ⊔ T) = a • S ⊔ a • T
参数：a : α；S T : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_sup`：map_sup (H K : Subgroup G) (f : G ->* N) : (H ⊔ K).map
 f = H.map f ⊔ K.map f
-/
theorem smul_sup (a : α) (S T : Subgroup G) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
/-
**Subgroup.smul_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_closure (a : α) (s : Set G) : a • closure s = closure (a • s)
参数：a : α；s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_closure`：map_closure (f : G ->* N) (s : Set G) : (closure 
s).map f = closure (f '' s)
-/
theorem smul_closure (a : α) (s : Set G) : a • closure s = closure (a • s) :=
  MonoidHom.map_closure _ _
/-
**Subgroup.pointwise_isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：pointwise_isCentralScalar [MulDistribMulAction αᵐᵒᵖ G] [IsCentralScalar α 
G] : IsCentralScalar α (Subgroup G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance pointwise_isCentralScalar [MulDistribMulAction αᵐᵒᵖ G] [IsCentralScalar α G] :
    IsCentralScalar α (Subgroup G) :=
  ⟨fun _ S => (congr_arg fun f => S.map f) <| MonoidHom.ext <| op_smul_eq_smul _⟩

end Monoid

section Group

variable [Group α] [MulDistribMulAction α G]

@[simp]
/-
**Subgroup.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_mem_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : a • x in a 
• S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
theorem smul_mem_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
/-
**Subgroup.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Subgroup G} {x : G} : x i
n a • S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Subgroup G} {x : G} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
/-
**Subgroup.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_inv_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : x in a⁻¹ • S
 ↔ a • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
theorem mem_inv_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
/-
**Subgroup.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Subgroup G} : a • S <=
 a • T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Subgroup G} : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff
/-
**Subgroup.pointwise_smul_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：pointwise_smul_subset_iff {a : α} {S T : Subgroup G} : a • S <= T ↔ S <= a
⁻¹ • T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_iff_subset_inv_smul_set`：smul_set_subset_iff_subset_
inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B
-/
theorem pointwise_smul_subset_iff {a : α} {S T : Subgroup G} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set
/-
**Subgroup.subset_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subset_pointwise_smul_iff {a : α} {S T : Subgroup G} : S <= a • T ↔ a⁻¹ • 
S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
theorem subset_pointwise_smul_iff {a : α} {S T : Subgroup G} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff
/-
**Subgroup.conj_smul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：conj_smul_le_of_le {P H : Subgroup G} (hP : P <= H) (h : H) : MulAut.conj 
(h : G) • P <= H
参数：hP : P <= H；h : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
-/
theorem conj_smul_le_of_le {P H : Subgroup G} (hP : P ≤ H) (h : H) :
    MulAut.conj (h : G) • P ≤ H := by
  rintro - ⟨g, hg, rfl⟩
  exact H.mul_mem (H.mul_mem h.2 (hP hg)) (H.inv_mem h.2)
/-
**Subgroup.conj_smul_eq_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：conj_smul_eq_self_of_mem {H : Subgroup G} {h : G} (hh : h in H) : MulAut.c
onj h • H = H
参数：hh : h in H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.conj_smul_le_of_le`：conj_smul_le_of_le {P H : Subgroup G} (hP :
 P <= H) (h : H) : MulAut.conj (h : G) • P <= H
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.subset_pointwise_smul_iff`：subset_pointwise_smul_iff {a : α} {S
 T : Subgroup G} : S <= a • T ↔ a⁻¹ • S <= T
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
-/
theorem conj_smul_eq_self_of_mem {H : Subgroup G} {h : G} (hh : h ∈ H) :
    MulAut.conj h • H = H := by
  refine le_antisymm ?_ ?_
  · exact (conj_smul_le_of_le (le_refl H) ⟨h, hh⟩)
  · rw [subset_pointwise_smul_iff, ← map_inv]
    exact conj_smul_le_of_le (le_refl H) ⟨h⁻¹, H.inv_mem hh⟩
/-
**Subgroup.conj_smul_subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：conj_smul_subgroupOf {P H : Subgroup G} (hP : P <= H) (h : H) : MulAut.con
j h • P.subgroupOf H = (MulAut.conj (h : G) • P).subgroupOf H
参数：hP : P <= H；h : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem conj_smul_subgroupOf {P H : Subgroup G} (hP : P ≤ H) (h : H) :
    MulAut.conj h • P.subgroupOf H = (MulAut.conj (h : G) • P).subgroupOf H := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro p ⟨g, hg, hp⟩
    exact ⟨⟨g, hP hg⟩, hg, Subtype.ext hp⟩

@[simp]
/-
**Subgroup.smul_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_inf (a : α) (S T : Subgroup G) : a • (S ⊓ T) = a • S ⊓ a • T
参数：a : α；S T : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem smul_inf (a : α) (S T : Subgroup G) : a • (S ⊓ T) = a • S ⊓ a • T := by
  simp [SetLike.ext_iff, mem_pointwise_smul_iff_inv_smul_mem]

/-- Applying a `MulDistribMulAction` results in an isomorphic subgroup -/
@[simps!]
/-
**Subgroup.equivSMul** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：equivSMul (a : α) (H : Subgroup G) : H ≃* (a • H : Subgroup G)
参数：a : α；H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying a `MulDistribMulAction` results in an isomorphic subgroup
-/
def equivSMul (a : α) (H : Subgroup G) : H ≃* (a • H : Subgroup G) :=
  (MulDistribMulAction.toMulEquiv G a).subgroupMap H
/-
**Subgroup.subgroup_mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subgroup_mul_singleton {H : Subgroup G} {h : G} (hh : h in H) : (H : Set G
) * {h} = H
参数：hh : h in H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mul_singleton`：mul_singleton : s * {b} = (· * b) '' s
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_mem_cancel_right`：mul_mem_cancel_right {x y : G} (h : x in H) : y * 
x in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subgroup_mul_singleton {H : Subgroup G} {h : G} (hh : h ∈ H) : (H : Set G) * {h} = H := by
  simp [preimage, mul_mem_cancel_right (inv_mem hh)]
/-
**Subgroup.singleton_mul_subgroup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：singleton_mul_subgroup {H : Subgroup G} {h : G} (hh : h in H) : {h} * (H :
 Set G) = H
参数：hh : h in H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_mul`：singleton_mul : {a} * t = (a * ·) '' t
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_mem_cancel_left`：mul_mem_cancel_left {x y : G} (h : x in H) : x * y 
in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_mul_subgroup {H : Subgroup G} {h : G} (hh : h ∈ H) : {h} * (H : Set G) = H := by
  simp [preimage, mul_mem_cancel_left (inv_mem hh)]
/-
**Subgroup.Normal.conjAct** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] {H : Subgroup G}, H.Normal → ∀ (g : Conj
Act G), g • H = H
参数：g : ConjAct G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Subgroup.map_mono`：map_mono {f : G ->* N} {K K' : Subgroup G} : K <= K' 
-> map f K <= map f K'
-/
theorem Normal.conjAct {H : Subgroup G} (hH : H.Normal) (g : ConjAct G) : g • H = H :=
  have : ∀ g : ConjAct G, g • H ≤ H :=
    fun _ => map_le_iff_le_comap.2 fun _ h => hH.conj_mem _ h _
  (this g).antisymm <| (smul_inv_smul g H).symm.trans_le (map_mono <| this _)

@[simp]
/-
**Subgroup.Normal.conj_smul_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] (g : G) (H : Subgroup G) [h : H.Normal],
 MulAut.conj g • H = H
参数：g : G；H : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.conjAct`：∀ {G : Type u_2} [inst : Group G] {H : Subgroup
 G}, H.Normal → ∀ (g : ConjAct G), g • H = H
-/
theorem Normal.conj_smul_eq_self (g : G) (H : Subgroup G) [h : Normal H] : MulAut.conj g • H = H :=
  h.conjAct g
/-
**Subgroup.Normal.of_conjugate_fixed** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`
。
形式化陈述：∀ {G : Type u_2} [inst : Group G] {H : Subgroup G}, (∀ (g : G), MulAut.con
j g • H = H) → H.Normal
参数：∀ (g : G), MulAut.conj g • H = H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.mem_pointwise_smul_iff_inv_smul_mem`：mem_pointwise_smul_iff_inv
_smul_mem {a : α} {S : Subgroup G} {x : G} : x in a • S ↔ a⁻¹ • x in S
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `MulAut.smul_def`：∀ {M : Type u_2} [inst : Monoid M] (f : MulAut M) (a : 
M), f • a = f a
· 使用定理 `MulAut.conj_apply`：∀ {G : Type u_3} [inst : Group G] (g h : G), (MulAut.
conj g) h = g * h * g⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem Normal.of_conjugate_fixed {H : Subgroup G} (h : ∀ g : G, (MulAut.conj g) • H = H) :
    H.Normal := by
  constructor
  intro n hn g
  rw [← h g, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one,
    ← mul_assoc, inv_mul_cancel, one_mul]
  exact hn

set_option backward.isDefEq.respectTransparency false in
/-
**Subgroup.normalCore_eq_iInf_conjAct** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalCore_eq_iInf_conjAct (H : Subgroup G) : H.normalCore = ⨅ (g : ConjAc
t G), g • H
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem normalCore_eq_iInf_conjAct (H : Subgroup G) :
    H.normalCore = ⨅ (g : ConjAct G), g • H := by
  ext g
  simp only [Subgroup.normalCore, Subgroup.mem_iInf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  refine ⟨fun h x ↦ h x⁻¹, fun h x ↦ ?_⟩
  simpa only [ConjAct.toConjAct_inv, inv_inv] using! h x⁻¹
/-
**Subgroup.conjAct_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：conjAct_pointwise_smul_iff {H : Subgroup G} {g : G} : ConjAct.toConjAct g 
• H = H ↔ g in normalizer H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.inv_mem_iff`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G)
 {x : G}, x⁻¹ ∈ H ↔ x ∈ H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma conjAct_pointwise_smul_iff {H : Subgroup G} {g : G} :
    ConjAct.toConjAct g • H = H ↔ g ∈ normalizer H := by
  rw [← (normalizer H : Subgroup G).inv_mem_iff]
  simp only [Subgroup.ext_iff, mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, mem_normalizer_iff, inv_inv, Iff.comm]
/-
**Subgroup.conjAct_pointwise_smul_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：conjAct_pointwise_smul_eq_self {H : Subgroup G} {g : G} (hg : g in normali
zer H) : ConjAct.toConjAct g • H = H
参数：hg : g in normalizer H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subgroup.conjAct_pointwise_smul_iff`：conjAct_pointwise_smul_iff {H : Sub
group G} {g : G} : ConjAct.toConjAct g • H = H ↔ g in normalizer H
-/
lemma conjAct_pointwise_smul_eq_self {H : Subgroup G} {g : G} (hg : g ∈ normalizer H) :
    ConjAct.toConjAct g • H = H :=
  conjAct_pointwise_smul_iff.2 hg

end Group
end Subgroup

