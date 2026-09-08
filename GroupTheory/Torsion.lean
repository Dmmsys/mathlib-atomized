/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Rank
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Torsion groups

This file defines torsion groups, i.e. groups where all elements have finite order.

## Main definitions

* `Monoid.IsTorsion` a predicate asserting `G` is torsion, i.e. that all
  elements are of finite order.
* `CommGroup.torsion G`, the torsion subgroup of an abelian group `G`
* `CommMonoid.torsion G`, the above stated for commutative monoids
* `Monoid.IsTorsionFree`, asserting no nontrivial elements have finite order in `G`
* `AddMonoid.IsTorsion` and `AddMonoid.IsTorsionFree` the additive versions of the above

## Implementation

All torsion monoids are really groups (which is proven here as `Monoid.IsTorsion.group`), but since
the definition can be stated on monoids it is implemented on `Monoid` to match other declarations in
the group theory library.

## Tags

periodic group, aperiodic group, torsion subgroup, torsion abelian group

## Future work

* generalize to π-torsion(-free) groups for a set of primes π
* free, free solvable and free abelian groups are torsion free
* complete direct and free products of torsion free groups are torsion free
* groups which are residually finite p-groups with respect to 2 distinct primes are torsion free
-/

@[expose] public section


variable {G H : Type*}

section

variable (G) [Monoid G]

/-- A predicate on a monoid saying that all elements are of finite order. -/
@[to_additive
/-- A predicate on an additive monoid saying that all elements are of finite order. -/]
/-
**IsMulTorsion** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMulTorsion
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsMulTorsion :=
  ∀ g : G, IsOfFinOrder g

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion := IsMulTorsion
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion := IsAddTorsion

/-- A monoid is not a torsion monoid if it has an element of infinite order. -/
@[to_additive (attr := simp)
/-- An additive monoid is not a torsion additive monoid if it has an element of infinite order. -/]
/-
**not_isMulTorsion_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isMulTorsion_iff : ¬IsMulTorsion G ↔ exists g : G, ¬IsOfFinOrder g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
-/
theorem not_isMulTorsion_iff : ¬IsMulTorsion G ↔ ∃ g : G, ¬IsOfFinOrder g :=
  not_forall

@[deprecated (since := "2026-07-01")] alias Monoid.not_isTorsion_iff := not_isMulTorsion_iff
@[deprecated (since := "2026-07-01")] alias AddMonoid.not_isTorsion_iff := not_isAddTorsion_iff

end

open Monoid

/-- Torsion monoids are really groups. -/
@[to_additive (attr := instance_reducible)
/-- Torsion additive monoids are really additive groups. -/]
/-
**IsMulTorsion.group** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMulTorsion.group [Monoid G] (tG : IsMulTorsion G) : Group G
参数：tG : IsMulTorsion G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def IsMulTorsion.group [Monoid G] (tG : IsMulTorsion G) : Group G :=
  { ‹Monoid G› with
    inv g := g ^ (orderOf g - 1)
    inv_mul_cancel g := by
      rw [← pow_succ, tsub_add_cancel_of_le, pow_orderOf_eq_one]
      exact (tG g).orderOf_pos }

@[deprecated (since := "2026-07-01")] alias IsTorsion.group := IsMulTorsion.group
@[deprecated (since := "2026-07-01")] alias IsTorsion.addGroup := IsAddTorsion.addGroup

section Group

variable [Group G] {N : Subgroup G} [Group H]

/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive /-- Additive subgroups of torsion additive groups are torsion additive groups. -/]
/-
**IsMulTorsion.subgroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMulTorsion.subgroup (tG : IsMulTorsion G) (H : Subgroup G) : IsMulTorsio
n H
参数：tG : IsMulTorsion G；H : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.isOfFinOrder_coe`：Submonoid.isOfFinOrder_coe {H : Submonoid G}
 {x : H} : IsOfFinOrder (x : G) ↔ IsOfFinOrder x

--- 原说明 ---
Subgroups of torsion groups are torsion groups.
-/
theorem IsMulTorsion.subgroup (tG : IsMulTorsion G) (H : Subgroup G) : IsMulTorsion H := fun h ↦
  Submonoid.isOfFinOrder_coe.1 <| tG h

@[deprecated (since := "2026-07-01")] alias IsTorsion.subgroup := IsMulTorsion.subgroup
@[deprecated (since := "2026-07-01")] alias IsTorsion.addSubgroup := IsAddTorsion.addSubgroup

/-- The image of a surjective torsion group homomorphism is torsion. -/
@[to_additive
/-- The image of a surjective torsion additive group homomorphism is torsion. -/]
/-
**IsMulTorsion.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMulTorsion.of_surjective {f : G ->* H} (hf : Function.Surjective f) (tG 
: IsMulTorsion G) : IsMulTorsion H
参数：hf : Function.Surjective f；tG : IsMulTorsion G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.isOfFinOrder`：MonoidHom.isOfFinOrder [Monoid H] (f : G ->* H) 
{x : G} (h : IsOfFinOrder x) : IsOfFinOrder f x
-/
theorem IsMulTorsion.of_surjective {f : G →* H} (hf : Function.Surjective f) (tG : IsMulTorsion G) :
    IsMulTorsion H := fun h ↦ by
  obtain ⟨g, rfl⟩ := hf h
  exact f.isOfFinOrder (tG g)

@[deprecated (since := "2026-06-30")] alias IsTorsion.of_surjective := IsMulTorsion.of_surjective
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.of_surjective := IsAddTorsion.of_surjective

/-- Torsion groups are closed under extensions. -/
@[to_additive
/-- Torsion additive groups are closed under extensions. -/]
/-
**IsMulTorsion.extension_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMulTorsion.extension_closed {f : G ->* H} (hN : N = f.ker) (tH : IsMulTo
rsion H) (tN : IsMulTorsion N) : IsMulTorsion G
参数：hN : N = f.ker；tH : IsMulTorsion H；tN : IsMulTorsion N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.exists_pow_eq_one`：∀ {G : Type u_1} [inst : Monoid G] {x : 
G}, IsOfFinOrder x → ∃ n, 0 < n ∧ x ^ n = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Subgroup.coe_pow`：coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G
) ^ n
· 使用定理 `Subgroup.coe_one`：coe_one : ((1 : H) : G) = 1
-/
theorem IsMulTorsion.extension_closed {f : G →* H} (hN : N = f.ker) (tH : IsMulTorsion H)
    (tN : IsMulTorsion N) : IsMulTorsion G := fun g ↦ by
  obtain ⟨ngn, ngnpos, hngn⟩ := (tH <| f g).exists_pow_eq_one
  have hmem := MonoidHom.mem_ker.mpr ((f.map_pow g ngn).trans hngn)
  lift g ^ ngn to N using hN.symm ▸ hmem with gn h
  obtain ⟨nn, nnpos, hnn⟩ := (tN gn).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr <| ⟨ngn * nn, mul_pos ngnpos nnpos, by
    rw [pow_mul, ← h, ← Subgroup.coe_pow, hnn, Subgroup.coe_one]⟩

@[deprecated (since := "2026-06-30")] alias IsTorsion.extension_closed :=
  IsMulTorsion.extension_closed
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.extension_closed :=
  IsAddTorsion.extension_closed

/-- The image of a quotient is torsion iff the group is torsion. -/
@[to_additive
/-- The image of a quotient is torsion iff the additive group is torsion. -/]
/-
**IsMulTorsion.quotient_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMulTorsion.quotient_iff {f : G ->* H} (hf : Function.Surjective f) (hN :
 N = f.ker) (tN : IsMulTorsion N) : IsMulTorsion H ↔ IsMulTorsion G
参数：hf : Function.Surjective f；hN : N = f.ker；tN : IsMulTorsion N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulTorsion.extension_closed`：IsMulTorsion.extension_closed {f : G ->* 
H} (hN : N = f.ker) (tH : IsMulTorsion H) (tN : IsMulTorsion N) : IsMulTorsion G
· 使用定理 `IsMulTorsion.of_surjective`：IsMulTorsion.of_surjective {f : G ->* H} (hf
 : Function.Surjective f) (tG : IsMulTorsion G) : IsMulTorsion H
-/
theorem IsMulTorsion.quotient_iff {f : G →* H} (hf : Function.Surjective f) (hN : N = f.ker)
    (tN : IsMulTorsion N) : IsMulTorsion H ↔ IsMulTorsion G :=
  ⟨fun tH ↦ IsMulTorsion.extension_closed hN tH tN, fun tG ↦ IsMulTorsion.of_surjective hf tG⟩

@[deprecated (since := "2026-06-30")] alias IsTorsion.quotient_iff := IsMulTorsion.quotient_iff
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.quotient_iff := IsAddTorsion.quotient_iff

/-- If a group exponent exists, the group is torsion. -/
@[to_additive
/-- If a group exponent exists, the additive group is torsion. -/]
/-
**ExponentExists.isMulTorsion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExponentExists.isMulTorsion (h : ExponentExists G) : IsMulTorsion G
参数：h : ExponentExists G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
-/
theorem ExponentExists.isMulTorsion (h : ExponentExists G) : IsMulTorsion G := fun g ↦ by
  obtain ⟨n, npos, hn⟩ := h
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, hn g⟩

@[deprecated (since := "2026-06-30")] alias ExponentExists.isTorsion := ExponentExists.isMulTorsion
@[deprecated (since := "2026-06-30")] alias ExponentExists.is_add_torsion :=
  ExponentExists.isAddTorsion

/-- The group exponent exists for any bounded torsion group. -/
@[to_additive
/-- The group exponent exists for any bounded torsion additive group. -/]
/-
**IsMulTorsion.exponentExists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMulTorsion.exponentExists (tG : IsMulTorsion G) (bounded : (Set.range fu
n g : G => orderOf g).Finite) : ExponentExists G
参数：tG : IsMulTorsion G；bounded : (Set.range fun g : G => orderOf g).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Monoid.exponent_ne_zero`：exponent_ne_zero : exponent G != 0 ↔ ExponentEx
ists G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.exponent_ne_zero_iff_range_orderOf_finite`：exponent_ne_zero_iff_r
ange_orderOf_finite (h : forall g : G, 0 < orderOf g) : exponent G != 0 ↔ (Set.r
ange (orderOf : G -> Nat)).Finite
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
-/
theorem IsMulTorsion.exponentExists (tG : IsMulTorsion G)
    (bounded : (Set.range fun g : G ↦ orderOf g).Finite) : ExponentExists G :=
  exponent_ne_zero.mp <|
    (exponent_ne_zero_iff_range_orderOf_finite fun g ↦ (tG g).orderOf_pos).mpr bounded

@[deprecated (since := "2026-07-01")] alias IsTorsion.exponentExists := IsMulTorsion.exponentExists

/-- Finite groups are torsion groups. -/
@[to_additive /-- Finite additive groups are torsion additive groups. -/]
/-
**isMulTorsion_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMulTorsion_of_finite [Finite G] : IsMulTorsion G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExponentExists.isMulTorsion`：ExponentExists.isMulTorsion (h : ExponentEx
ists G) : IsMulTorsion G
· 使用定理 `Monoid.ExponentExists.of_finite`：∀ {G : Type u} [inst : LeftCancelMonoid
 G] [Finite G], Monoid.ExponentExists G

--- 原说明 ---
Finite groups are torsion groups.
-/
theorem isMulTorsion_of_finite [Finite G] : IsMulTorsion G :=
  ExponentExists.isMulTorsion .of_finite

@[deprecated (since := "2026-06-30")] alias isTorsion_of_finite := isMulTorsion_of_finite
@[deprecated (since := "2026-06-30")] alias is_add_torsion_of_finite := isAddTorsion_of_finite

end Group

section CommGroup
variable [CommGroup G]

/-- A nontrivial torsion abelian group is not torsion-free. -/
@[to_additive /-- A nontrivial torsion additive abelian group is not torsion-free. -/]
/-
**not_isMulTorsionFree_of_isMulTorsion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_isMulTorsionFree_of_isMulTorsion [Nontrivial G] (hG : IsMulTorsion G) 
: ¬ IsMulTorsionFree G
参数：hG : IsMulTorsion G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `not_isMulTorsionFree_iff_isOfFinOrder`：not_isMulTorsionFree_iff_isOfFinO
rder : ¬ IsMulTorsionFree G ↔ exists a != (1 : G), IsOfFinOrder a
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x

--- 原说明 ---
A nontrivial torsion abelian group is not torsion-free.
-/
lemma not_isMulTorsionFree_of_isMulTorsion [Nontrivial G] (hG : IsMulTorsion G) :
    ¬ IsMulTorsionFree G :=
  not_isMulTorsionFree_iff_isOfFinOrder.2 <| let ⟨x, hx⟩ := exists_ne (1 : G); ⟨x, hx, hG x⟩

@[deprecated (since := "2026-07-01")] alias not_isMulTorsionFree_of_isTorsion :=
  not_isMulTorsionFree_of_isMulTorsion
@[deprecated (since := "2026-07-01")] alias not_isAddTorsionFree_of_isTorsion :=
  not_isAddTorsionFree_of_isAddTorsion

/-- A nontrivial torsion-free abelian group is not torsion. -/
@[to_additive /-- A nontrivial torsion-free additive abelian group is not torsion. -/]
/-
**not_isMulTorsion_of_isMulTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_isMulTorsion_of_isMulTorsionFree [Nontrivial G] [IsMulTorsionFree G] :
 ¬ IsMulTorsion G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_isMulTorsionFree_of_isMulTorsion`：not_isMulTorsionFree_of_isMulTorsi
on [Nontrivial G] (hG : IsMulTorsion G) : ¬ IsMulTorsionFree G

--- 原说明 ---
A nontrivial torsion-free abelian group is not torsion.
-/
lemma not_isMulTorsion_of_isMulTorsionFree [Nontrivial G] [IsMulTorsionFree G] : ¬ IsMulTorsion G :=
  (not_isMulTorsionFree_of_isMulTorsion · ‹_›)

@[deprecated (since := "2026-07-01")] alias not_isTorsion_of_isMulTorsionFree :=
  not_isMulTorsion_of_isMulTorsionFree
@[deprecated (since := "2026-07-01")] alias not_isTorsion_of_isAddTorsionFree :=
  not_isAddTorsion_of_isAddTorsionFree

end CommGroup

section Module

-- A (semi/)ring of scalars and a commutative monoid of elements
variable (R M : Type*) [AddCommMonoid M]

/-- A module whose scalars are torsion is torsion. -/
/-
**IsAddTorsion.module_of_torsion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAddTorsion.module_of_torsion [Semiring R] [Module R M] (tR : IsAddTorsio
n R) : IsAddTorsion M
参数：tR : IsAddTorsion R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinAddOrder_iff_nsmul_eq_zero`：∀ {G : Type u_1} [inst : AddMonoid G]
 {x : G}, IsOfFinAddOrder x ↔ ∃ n, 0 < n ∧ n • x = 0
· 使用定理 `IsOfFinAddOrder.exists_nsmul_eq_zero`：∀ {G : Type u_1} [inst : AddMonoid
 G] {x : G}, IsOfFinAddOrder x → ∃ n, 0 < n ∧ n • x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A module whose scalars are torsion is torsion.
-/
theorem IsAddTorsion.module_of_torsion [Semiring R] [Module R M] (tR : IsAddTorsion R) :
    IsAddTorsion M :=
  fun f ↦ isOfFinAddOrder_iff_nsmul_eq_zero.mpr <| by
    obtain ⟨n, npos, hn⟩ := (tR 1).exists_nsmul_eq_zero
    exact ⟨n, npos, by simp only [← Nat.cast_smul_eq_nsmul R _ f, ← nsmul_one, hn, zero_smul]⟩

@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.module_of_torsion :=
  IsAddTorsion.module_of_torsion

/-- A module with a finite ring of scalars is torsion. -/
/-
**IsAddTorsion.module_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAddTorsion.module_of_finite [Ring R] [Finite R] [Module R M] : IsAddTors
ion M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddTorsion.module_of_torsion`：IsAddTorsion.module_of_torsion [Semiring
 R] [Module R M] (tR : IsAddTorsion R) : IsAddTorsion M
· 使用定理 `isAddTorsion_of_finite`：∀ {G : Type u_1} [inst : AddGroup G] [Finite G],
 IsAddTorsion G

--- 原说明 ---
A module with a finite ring of scalars is torsion.
-/
theorem IsAddTorsion.module_of_finite [Ring R] [Finite R] [Module R M] : IsAddTorsion M :=
  (isAddTorsion_of_finite : IsAddTorsion R).module_of_torsion _ _

@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.module_of_finite :=
  IsAddTorsion.module_of_finite

end Module

section CommMonoid

variable (G) [CommMonoid G] [CommMonoid H]

namespace CommMonoid

/-- The torsion submonoid of a commutative monoid.

(Note that by `IsMulTorsion.group` torsion monoids are truthfully groups.)
-/
@[to_additive addTorsion /-- The torsion additive submonoid of an additive commutative monoid. -/]
/-
**CommMonoid.torsion** 是 Mathlib 中的一个定义，位于命名空间 `CommMonoid`。
形式化陈述：torsion : Submonoid G where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.mul`：IsOfFinOrder.mul (hx : IsOfFinOrder x) (hy : IsOfFinOr
der y) : IsOfFinOrder (x * y)

--- 原说明 ---
The torsion submonoid of a commutative monoid.

(Note that by `IsMulTorsion.group` torsion monoids are truthfully groups.)
-/
def torsion : Submonoid G where
  carrier := { x | IsOfFinOrder x }
  one_mem' := IsOfFinOrder.one
  mul_mem' hx hy := hx.mul hy

@[to_additive]
/-
**CommMonoid.mem_torsion** 是 Mathlib 中的一个定理，位于命名空间 `CommMonoid`。
形式化陈述：mem_torsion (g : G) : g in torsion G ↔ IsOfFinOrder g
参数：g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_torsion (g : G) : g ∈ torsion G ↔ IsOfFinOrder g := Iff.rfl

@[to_additive]
/-
**CommMonoid.torsion_prod** 是 Mathlib 中的一个引理，位于命名空间 `CommMonoid`。
形式化陈述：torsion_prod : torsion (G × H) = (torsion G).prod (torsion H)
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
lemma torsion_prod : torsion (G × H) = (torsion G).prod (torsion H) := by
  simp [Submonoid.ext_iff, Submonoid.mem_prod, mem_torsion, IsOfFinOrder.prod_iff]

variable {G}

set_option backward.isDefEq.respectTransparency false in
/-- Torsion submonoids are torsion. -/
@[to_additive /-- Torsion additive submonoids are torsion. -/]
/-
**CommMonoid.torsion.isMulTorsion** 是 Mathlib 中的一个定理，位于命名空间 `CommMonoid.torsion`
。
形式化陈述：∀ {G : Type u_1} [inst : CommMonoid G], IsMulTorsion ↥(CommMonoid.torsion 
G)
参数：CommMonoid.torsion G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `SubmonoidClass.coe_pow`：coe_pow {M} [Monoid M] {A : Type*} [SetLike A M]
 [SubmonoidClass A M] {S : A} (x : S) (n : Nat) : ↑(x ^ n) = (x : M) ^ n
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPeriodicPt_mul_iff_pow_eq_one`：isPeriodicPt_mul_iff_pow_eq_one (x : G)
 : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1

--- 原说明 ---
Torsion submonoids are torsion.
-/
theorem torsion.isMulTorsion : IsMulTorsion <| torsion G := fun ⟨x, n, npos, hn⟩ ↦
  ⟨n, npos,
    Subtype.ext <| by
      dsimp
      rw [mul_left_iterate]
      change _ * 1 = 1
      rw [_root_.mul_one, SubmonoidClass.coe_pow, Subtype.coe_mk,
        (isPeriodicPt_mul_iff_pow_eq_one _).mp hn]⟩

@[deprecated (since := "2026-07-01")] alias torsion.isTorsion := torsion.isMulTorsion
@[deprecated (since := "2026-07-01")] alias _root_.AddCommMonoid.addTorsion.isTorsion :=
  AddCommMonoid.addTorsion.isAddTorsion

variable (G) (p : ℕ)

/-- The `p`-primary component is the submonoid of elements `g` such that `g ^ p ^ k = 1`
for some `k`. For prime `p`, these are exactly the elements of `p`-power order. -/
@[to_additive
/-- The additive `p`-primary component is the submonoid of elements `g` such that
`p ^ k • g = 0` for some `k`. For prime `p`, these are exactly the elements of additive
`p`-power order. -/]
/-
**CommMonoid.primaryComponent** 是 Mathlib 中的一个定义，位于命名空间 `CommMonoid`。
形式化陈述：primaryComponent : Submonoid G where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def primaryComponent : Submonoid G where
  carrier := { g | ∃ k : ℕ, g ^ p ^ k = 1 }
  one_mem' := ⟨0, by simp⟩
  mul_mem' := fun {a b} ⟨m, hm⟩ ⟨n, hn⟩ ↦ ⟨m + n, by
    rw [mul_pow, pow_add, pow_mul, hm, one_pow, one_mul, mul_comm, pow_mul, hn, one_pow]⟩

variable {G} {p}

/-- `g` lies in the `p`-primary component iff `g ^ p ^ k = 1` for some `k`. -/
@[to_additive (attr := simp)
/-- `g` lies in the additive `p`-primary component iff `p ^ k • g = 0` for some `k`. -/]
/-
**CommMonoid.mem_primaryComponent** 是 Mathlib 中的一个定理，位于命名空间 `CommMonoid`。
形式化陈述：mem_primaryComponent {g : G} : g in primaryComponent G p ↔ exists k : Nat,
 g ^ p ^ k = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_primaryComponent {g : G} : g ∈ primaryComponent G p ↔ ∃ k : ℕ, g ^ p ^ k = 1 :=
  .rfl

/-- For prime `p`, `g` lies in the `p`-primary component iff its order is a power of `p`. -/
@[to_additive
/-- For prime `p`, `g` lies in the additive `p`-primary component iff its additive
order is a power of `p`. -/]
/-
**CommMonoid.mem_primaryComponent_iff_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `CommMon
oid`。
形式化陈述：mem_primaryComponent_iff_orderOf [Fact p.Prime] {g : G} : g in primaryComp
onent G p ↔ exists n : Nat, orderOf g = p ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `exists_orderOf_eq_prime_pow_iff`：exists_orderOf_eq_prime_pow_iff : (exis
ts k : Nat, orderOf x = p ^ k) ↔ exists m : Nat, x ^ (p : Nat) ^ m = 1
-/
theorem mem_primaryComponent_iff_orderOf [Fact p.Prime] {g : G} :
    g ∈ primaryComponent G p ↔ ∃ n : ℕ, orderOf g = p ^ n :=
  exists_orderOf_eq_prime_pow_iff.symm

variable [hp : Fact p.Prime]

/-- Elements of the `p`-primary component have order `p^n` for some `n`. -/
@[to_additive primaryComponent.exists_orderOf_eq_prime_nsmul
/-- Elements of the `p`-primary component have additive order `p^n` for some `n`. -/]
/-
**CommMonoid.primaryComponent.exists_orderOf_eq_prime_pow** 是 Mathlib 中的一个定理，位于命
名空间 `CommMonoid.primaryComponent`。
形式化陈述：∀ {G : Type u_1} [inst : CommMonoid G] {p : ℕ} [hp : Fact (Nat.Prime p)] (
g : ↥(CommMonoid.primaryComponent G p)),   ∃ n, orderOf g = p ^ n
参数：Nat.Prime p；g : ↥(CommMonoid.primaryComponent G p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_submonoid`：orderOf_submonoid {H : Submonoid G} (y : H) : orderOf
 (y : G) = orderOf y
· 使用定理 `CommMonoid.mem_primaryComponent_iff_orderOf`：mem_primaryComponent_iff_or
derOf [Fact p.Prime] {g : G} : g in primaryComponent G p ↔ exists n : Nat, order
Of g = p ^ n
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem primaryComponent.exists_orderOf_eq_prime_pow (g : CommMonoid.primaryComponent G p) :
    ∃ n : ℕ, orderOf g = p ^ n := by
  rw [← orderOf_submonoid, ← mem_primaryComponent_iff_orderOf]
  exact g.property

/-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/
@[to_additive /-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/]
/-
**CommMonoid.primaryComponent.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `CommMonoid.pri
maryComponent`。
形式化陈述：∀ {G : Type u_1} [inst : CommMonoid G] {p : ℕ} [hp : Fact (Nat.Prime p)] {
p' : ℕ} [hp' : Fact (Nat.Prime p')],   p ≠ p' → Disjoint (CommMonoid.primaryComp
onent G p) (CommMonoid.primaryComponent G p')
参数：Nat.Prime p；Nat.Prime p'；CommMonoid.primaryComponent G p；CommMonoid.primaryCo
mponent G p'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.disjoint_def`：disjoint_def {p₁ p₂ : Submonoid M} : Disjoint p₁
 p₂ ↔ forall {x : M}, x in p₁ -> x in p₂ -> x = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommMonoid.mem_primaryComponent_iff_orderOf`：mem_primaryComponent_iff_or
derOf [Fact p.Prime] {g : G} : g in primaryComponent G p ↔ exists n : Nat, order
Of g = p ^ n
· 使用定理 `orderOf_eq_one_iff`：orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_of_prime_pow_eq`：eq_of_prime_pow_eq (hp₁ : Prime p₁) (hp₂ : Prime p₂)
 (hk₁ : 0 < k₁) (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
The `p`- and `q`-primary components are disjoint for `p ≠ q`.
-/
theorem primaryComponent.disjoint {p' : ℕ} [hp' : Fact p'.Prime] (hne : p ≠ p') :
    Disjoint (CommMonoid.primaryComponent G p) (CommMonoid.primaryComponent G p') :=
  Submonoid.disjoint_def.mpr fun {g} hg hg' ↦ by
    rw [mem_primaryComponent_iff_orderOf] at hg hg'
    obtain ⟨_ | n, hn⟩ := hg
    · rwa [pow_zero, orderOf_eq_one_iff] at hn
    · obtain ⟨_, hn'⟩ := hg'
      exact absurd (eq_of_prime_pow_eq hp.out.prime hp'.out.prime n.succ_pos (hn ▸ hn')) hne

end CommMonoid

open CommMonoid (torsion)

namespace IsMulTorsion

variable {G}

/-- The torsion submonoid of a torsion monoid is `⊤`. -/
@[to_additive (attr := simp)
/-- The torsion additive submonoid of a torsion additive monoid is `⊤`. -/]
/-
**IsMulTorsion.torsion_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `IsMulTorsion`。
形式化陈述：torsion_eq_top (tG : IsMulTorsion G) : torsion G = ⊤
参数：tG : IsMulTorsion G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `trivial`：True
-/
theorem torsion_eq_top (tG : IsMulTorsion G) : torsion G = ⊤ := by ext; tauto

/-- A torsion monoid is isomorphic to its torsion submonoid. -/
@[to_additive (attr := simps!)
/-- A torsion additive monoid is isomorphic to its torsion additive submonoid. -/]
/-
**IsMulTorsion.torsionMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsMulTorsion`。
形式化陈述：torsionMulEquiv (tG : IsMulTorsion G) : torsion G ≃* G
参数：tG : IsMulTorsion G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsMulTorsion.torsion_eq_top`：torsion_eq_top (tG : IsMulTorsion G) : tors
ion G = ⊤
-/
def torsionMulEquiv (tG : IsMulTorsion G) : torsion G ≃* G :=
  (MulEquiv.submonoidCongr tG.torsion_eq_top).trans Submonoid.topEquiv

end IsMulTorsion

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsion_eq_top :=
  IsMulTorsion.torsion_eq_top
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsion_eq_top :=
  IsAddTorsion.torsion_eq_top

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsionMulEquiv :=
  IsMulTorsion.torsionMulEquiv
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsionAddEquiv :=
  IsAddTorsion.torsionAddEquiv

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsionMulEquiv_apply :=
  IsMulTorsion.torsionMulEquiv_apply
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsionAddEquiv_apply :=
  IsAddTorsion.torsionAddEquiv_apply

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsionMulEquiv_symm_apply_coe :=
  IsMulTorsion.torsionMulEquiv_symm_apply_coe
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsionAddEquiv_symm_apply_coe :=
  IsAddTorsion.torsionAddEquiv_symm_apply_coe

/-- Torsion submonoids of a torsion submonoid are isomorphic to the submonoid. -/
@[to_additive (attr := simp)
/-- Torsion additive submonoids of a torsion additive submonoid are
isomorphic to the additive submonoid. -/]
/-
**CommMonoid.Torsion.ofTorsion** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommMonoid.Torsion.ofTorsion : torsion (torsion G) ≃* torsion G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommMonoid.torsion.isMulTorsion`：∀ {G : Type u_1} [inst : CommMonoid G],
 IsMulTorsion ↥(CommMonoid.torsion G)
-/
def CommMonoid.Torsion.ofTorsion : torsion (torsion G) ≃* torsion G :=
  IsMulTorsion.torsionMulEquiv CommMonoid.torsion.isMulTorsion

@[deprecated (since := "2026-07-01")] alias Torsion.ofTorsion := CommMonoid.Torsion.ofTorsion

end CommMonoid

section CommGroup

variable (G) [CommGroup G] [CommGroup H]

namespace CommGroup

/-- The torsion subgroup of an abelian group. -/
@[to_additive /-- The torsion additive subgroup of an additive abelian group. -/]
/-
**CommGroup.torsion** 是 Mathlib 中的一个定义，位于命名空间 `CommGroup`。
形式化陈述：torsion : Subgroup G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The torsion subgroup of an abelian group.
-/
def torsion : Subgroup G :=
  { CommMonoid.torsion G with inv_mem' := fun hx ↦ IsOfFinOrder.inv hx }

/-- The torsion submonoid of an abelian group equals the torsion subgroup as a submonoid. -/
@[to_additive
/-- The torsion additive submonoid of an abelian group equals the torsion
additive subgroup as an additive submonoid. -/]
/-
**CommGroup.torsion_eq_torsion_submonoid** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：torsion_eq_torsion_submonoid : CommMonoid.torsion G = (torsion G).toSubmon
oid
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem torsion_eq_torsion_submonoid : CommMonoid.torsion G = (torsion G).toSubmonoid :=
  rfl

@[deprecated (since := "2026-07-01")] alias
    _root_.AddCommGroup.add_torsion_eq_add_torsion_submonoid :=
  AddCommGroup.torsion_eq_torsion_addSubmonoid

variable {G}

@[to_additive]
/-
**CommGroup.mem_torsion** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：mem_torsion (g : G) : g in torsion G ↔ IsOfFinOrder g
参数：g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_torsion (g : G) : g ∈ torsion G ↔ IsOfFinOrder g := Iff.rfl

@[to_additive]
/-
**CommGroup.torsion_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `CommGroup`。
形式化陈述：torsion_eq_top_iff : torsion G = ⊤ ↔ IsMulTorsion G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.eq_top_iff'`：eq_top_iff' : H = ⊤ ↔ forall x : G, x in H
-/
lemma torsion_eq_top_iff : torsion G = ⊤ ↔ IsMulTorsion G :=
  (torsion G).eq_top_iff'

@[to_additive]
/-
**CommGroup.isMulTorsionFree_iff_torsion_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `CommG
roup`。
形式化陈述：isMulTorsionFree_iff_torsion_eq_bot : IsMulTorsionFree G ↔ CommGroup.torsi
on G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isMulTorsionFree_iff_not_isOfFinOrder`：isMulTorsionFree_iff_not_isOfFinO
rder : IsMulTorsionFree G ↔ forall ⦃a : G⦄, a != 1 -> ¬ IsOfFinOrder a where mp 
_ _
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isMulTorsionFree_iff_torsion_eq_bot : IsMulTorsionFree G ↔ CommGroup.torsion G = ⊥ := by
  rw [isMulTorsionFree_iff_not_isOfFinOrder, eq_bot_iff, SetLike.le_def]
  simp [not_imp_not, CommGroup.mem_torsion]

@[to_additive]
/-
**CommGroup.le_comap_torsion** 是 Mathlib 中的一个引理，位于命名空间 `CommGroup`。
形式化陈述：le_comap_torsion (f : G ->* H) : torsion G <= (torsion H).comap f
参数：f : G ->* H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.isOfFinOrder`：MonoidHom.isOfFinOrder [Monoid H] (f : G ->* H) 
{x : G} (h : IsOfFinOrder x) : IsOfFinOrder f x
-/
lemma le_comap_torsion (f : G →* H) : torsion G ≤ (torsion H).comap f := by
  intro x
  exact f.isOfFinOrder

@[to_additive]
/-
**CommGroup.map_torsion_le** 是 Mathlib 中的一个引理，位于命名空间 `CommGroup`。
形式化陈述：map_torsion_le (f : G ->* H) : (torsion G).map f <= torsion H
参数：f : G ->* H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
· 使用引理 `CommGroup.le_comap_torsion`：le_comap_torsion (f : G ->* H) : torsion G <
= (torsion H).comap f
-/
lemma map_torsion_le (f : G →* H) : (torsion G).map f ≤ torsion H :=
  Subgroup.map_le_iff_le_comap.mpr (le_comap_torsion f)

@[to_additive]
/-
**CommGroup.comap_torsion_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `CommGroup`。
形式化陈述：comap_torsion_of_injective {f : G ->* H} (hf : Function.Injective f) : (to
rsion H).comap f = torsion G
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Function.Injective.isOfFinOrder_iff`：Function.Injective.isOfFinOrder_iff
 [Monoid H] {f : G ->* H} (hf : Injective f) : IsOfFinOrder (f x) ↔ IsOfFinOrder
 x
-/
lemma comap_torsion_of_injective {f : G →* H} (hf : Function.Injective f) :
    (torsion H).comap f = torsion G := by
  ext x
  exact hf.isOfFinOrder_iff

@[to_additive]
/-
**CommGroup._root_.MulEquiv.comap_torsion** 是 Mathlib 中的一个引理，位于命名空间 `CommGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MulEquiv.comap_torsion (e : G ≃* H) : (torsion H).comap e = torsion G :=
  comap_torsion_of_injective e.injective

@[to_additive]
/-
**CommGroup._root_.MulEquiv.map_torsion** 是 Mathlib 中的一个引理，位于命名空间 `CommGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MulEquiv.map_torsion (e : G ≃* H) : (torsion G).map e = torsion H := by
  rw [Subgroup.map_equiv_eq_comap_symm, e.symm.comap_torsion]

@[to_additive]
/-
**CommGroup.torsion_prod** 是 Mathlib 中的一个引理，位于命名空间 `CommGroup`。
形式化陈述：torsion_prod : torsion (G × H) = (torsion G).prod (torsion H)
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
lemma torsion_prod : torsion (G × H) = (torsion G).prod (torsion H) := by
  simp [Subgroup.ext_iff, Subgroup.mem_prod, mem_torsion, IsOfFinOrder.prod_iff]

variable (G)

@[to_additive]
/-
**CommGroup.isMulTorsion_quotient_range_powMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `
CommGroup`。
形式化陈述：isMulTorsion_quotient_range_powMonoidHom {n : Nat} (hn : n != 0) : IsMulTo
rsion (G ⧸ (powMonoidHom (α
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.mk_pow`：mk_pow (a : G) (n : Nat) : ((a ^ n : G) : Q) = (a 
: Q) ^ n
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `powMonoidHom_apply`：∀ {α : Type u_1} [inst : CommMonoid α] (n : ℕ) (x : 
α), (powMonoidHom n) x = x ^ n
-/
lemma isMulTorsion_quotient_range_powMonoidHom {n : ℕ} (hn : n ≠ 0) :
    IsMulTorsion (G ⧸ (powMonoidHom (α := G) n).range) := by
  simp only [IsMulTorsion, isOfFinOrder_iff_pow_eq_one]
  refine fun g ↦ QuotientGroup.induction_on g fun a ↦ ⟨n, hn.pos, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  simp

@[deprecated (since := "2026-07-01")] alias isTorsion_quotient_range_powMonoidHom :=
  isMulTorsion_quotient_range_powMonoidHom
@[deprecated (since := "2026-07-01")] alias
    _root_.AddCommGroup.isTorsion_quotient_range_nsmulAddMonoidHom :=
  AddCommGroup.isAddTorsion_quotient_range_nsmulAddMonoidHom

variable (p : ℕ)

/-- The `p`-primary component is the subgroup of elements `g` such that `g ^ p ^ k = 1`
for some `k`. For prime `p`, these are exactly the elements of `p`-power order. -/
@[to_additive
/-- The additive `p`-primary component is the subgroup of elements `g` such that
`p ^ k • g = 0` for some `k`. For prime `p`, these are exactly the elements of additive
`p`-power order. -/]
/-
**CommGroup.primaryComponent** 是 Mathlib 中的一个定义，位于命名空间 `CommGroup`。
形式化陈述：primaryComponent : Subgroup G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def primaryComponent : Subgroup G :=
  { CommMonoid.primaryComponent G p with
    inv_mem' := fun {g} ⟨k, hk⟩ ↦ ⟨k, by rw [inv_pow, hk, inv_one]⟩ }

variable {G} {p}

/-- `g` lies in the `p`-primary component iff `g ^ p ^ k = 1` for some `k`. -/
@[to_additive (attr := simp)
/-- `g` lies in the additive `p`-primary component iff `p ^ k • g = 0` for some `k`. -/]
/-
**CommGroup.mem_primaryComponent** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：mem_primaryComponent {g : G} : g in primaryComponent G p ↔ exists k : Nat,
 g ^ p ^ k = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_primaryComponent {g : G} : g ∈ primaryComponent G p ↔ ∃ k : ℕ, g ^ p ^ k = 1 :=
  .rfl

/-- For prime `p`, `g` lies in the `p`-primary component iff its order is a power of `p`. -/
@[to_additive
/-- For prime `p`, `g` lies in the additive `p`-primary component iff its additive
order is a power of `p`. -/]
/-
**CommGroup.mem_primaryComponent_iff_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `CommGrou
p`。
形式化陈述：mem_primaryComponent_iff_orderOf [Fact p.Prime] {g : G} : g in primaryComp
onent G p ↔ exists n : Nat, orderOf g = p ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `exists_orderOf_eq_prime_pow_iff`：exists_orderOf_eq_prime_pow_iff : (exis
ts k : Nat, orderOf x = p ^ k) ↔ exists m : Nat, x ^ (p : Nat) ^ m = 1
-/
theorem mem_primaryComponent_iff_orderOf [Fact p.Prime] {g : G} :
    g ∈ primaryComponent G p ↔ ∃ n : ℕ, orderOf g = p ^ n :=
  exists_orderOf_eq_prime_pow_iff.symm

/-- The `p`-primary component is a `p`-group. -/
/-
**CommGroup.primaryComponent.isPGroup** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup.prima
ryComponent`。
形式化陈述：∀ {G : Type u_1} [inst : CommGroup G] {p : ℕ}, IsPGroup p ↥(CommGroup.prim
aryComponent G p)
参数：CommGroup.primaryComponent G p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The `p`-primary component is a `p`-group.
-/
theorem primaryComponent.isPGroup : IsPGroup p (primaryComponent G p) := fun g ↦
  g.property.imp fun _ hk ↦ Subtype.ext <| by simpa using hk

variable (G H)

/-- The free rank of a finitely generated abelian group is the rank of its free part. -/
@[to_additive
/-- The free rank of a finitely generated abelian group is the rank of its free part. -/]
/-
**CommGroup.freeRank** 是 Mathlib 中的一个定义，位于命名空间 `CommGroup`。
形式化陈述：freeRank [Group.FG G] : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def freeRank [Group.FG G] : ℕ := Group.rank (G ⧸ torsion G)

@[to_additive]
/-
**CommGroup.freeRank_def** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：freeRank_def [Group.FG G] : freeRank G = Group.rank (G ⧸ torsion G)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem freeRank_def [Group.FG G] : freeRank G = Group.rank (G ⧸ torsion G) := rfl

variable {G H}

@[to_additive]
/-
**CommGroup.freeRank_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：freeRank_eq_zero_iff [Group.FG G] : freeRank G = 0 ↔ IsMulTorsion G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommGroup.freeRank.eq_1`：∀ (G : Type u_1) [inst : CommGroup G] [inst_1 :
 Group.FG G], CommGroup.freeRank G = Group.rank (G ⧸ CommGroup.torsion G)
· 使用定理 `Group.rank_eq_zero_iff`：rank_eq_zero_iff [FG G] : rank G = 0 ↔ Subsingle
ton G
· 使用定理 `QuotientGroup.subsingleton_iff`：∀ {G : Type u_1} [inst : Group G] {N : S
ubgroup G}, Subsingleton (G ⧸ N) ↔ N = ⊤
· 使用引理 `CommGroup.torsion_eq_top_iff`：torsion_eq_top_iff : torsion G = ⊤ ↔ IsMul
Torsion G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem freeRank_eq_zero_iff [Group.FG G] : freeRank G = 0 ↔ IsMulTorsion G := by
  rw [freeRank, Group.rank_eq_zero_iff, QuotientGroup.subsingleton_iff, torsion_eq_top_iff]

@[to_additive]
/-
**CommGroup.freeRank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：freeRank_eq_zero (hG : IsMulTorsion G) [Group.FG G] : freeRank G = 0
参数：hG : IsMulTorsion G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CommGroup.freeRank_eq_zero_iff`：freeRank_eq_zero_iff [Group.FG G] : free
Rank G = 0 ↔ IsMulTorsion G
-/
theorem freeRank_eq_zero (hG : IsMulTorsion G) [Group.FG G] : freeRank G = 0 :=
  freeRank_eq_zero_iff.mpr hG

@[to_additive]
/-
**CommGroup.freeRank_eq_zero_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：freeRank_eq_zero_of_finite [Finite G] : freeRank G = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommGroup.freeRank_eq_zero`：freeRank_eq_zero (hG : IsMulTorsion G) [Grou
p.FG G] : freeRank G = 0
· 使用定理 `isMulTorsion_of_finite`：isMulTorsion_of_finite [Finite G] : IsMulTorsion
 G
· 使用定理 `Group.fg_of_finite`：∀ {G : Type u_3} [inst : Group G] [Finite G], Group.
FG G
-/
theorem freeRank_eq_zero_of_finite [Finite G] : freeRank G = 0 :=
  freeRank_eq_zero isMulTorsion_of_finite

@[to_additive]
/-
**CommGroup.freeRank_congr** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：freeRank_congr [Group.FG G] [Group.FG H] (e : G ≃* H) : freeRank G = freeR
ank H
参数：e : G ≃* H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.rank_congr`：rank_congr [FG G] [FG H] (e : G ≃* H) : rank G = rank 
H
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `MulEquiv.map_torsion`：∀ {G : Type u_1} {H : Type u_2} [inst : CommGroup 
G] [inst_1 : CommGroup H] (e : G ≃* H),   Subgroup.map (↑e) (CommGroup.torsion G
) = CommGr…
-/
theorem freeRank_congr [Group.FG G] [Group.FG H] (e : G ≃* H) : freeRank G = freeRank H :=
  Group.rank_congr (QuotientGroup.congr (torsion G) (torsion H) e e.map_torsion)

-- TODO: Prove monotonicity of `freeRank` along injective homomorphisms. This would require proving
-- monotonicity of `rank` along injective homomorphism of abelian groups.
@[to_additive]
/-
**CommGroup.freeRank_ge_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：freeRank_ge_of_surjective [Group.FG G] [Group.FG H] (e : G ->* H) (he : Fu
nction.Surjective e) : freeRank H <= freeRank G
参数：e : G ->* H；he : Function.Surjective e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.rank_le_of_surjective`：rank_le_of_surjective [FG G] [FG H] (f : G 
->* H) (hf : Surjective f) : rank H <= rank G
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用引理 `CommGroup.le_comap_torsion`：le_comap_torsion (f : G ->* H) : torsion G <
= (torsion H).comap f
· 使用定理 `QuotientGroup.map_surjective_of_surjective`：map_surjective_of_surjective
 (M : Subgroup H) [M.Normal] (f : G ->* H) (hf : Function.Surjective (mk ∘ f : G
 -> H ⧸ M)) (h : N <= M.comap f)…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
-/
theorem freeRank_ge_of_surjective [Group.FG G] [Group.FG H] (e : G →* H)
    (he : Function.Surjective e) : freeRank H ≤ freeRank G :=
  Group.rank_le_of_surjective _ <| QuotientGroup.map_surjective_of_surjective
    (torsion G) (torsion H) e (QuotientGroup.mk_surjective.comp he) (le_comap_torsion e)

end CommGroup

open CommGroup (torsion)

/-- Quotienting a group by its torsion subgroup yields a torsion-free group. -/
@[to_additive
/-- Quotienting an additive group by its torsion additive subgroup yields a torsion-free additive
group. -/]
/-
**_root_.QuotientGroup.instIsMulTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：_root_.QuotientGroup.instIsMulTorsionFree : IsMulTorsionFree G ⧸ torsion G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.QuotientGroup.instIsMulTorsionFree : IsMulTorsionFree <| G ⧸ torsion G := by
  refine .of_not_isOfFinOrder fun g hne hfin ↦ hne ?_
  obtain ⟨g⟩ := g
  obtain ⟨m, mpos, hm⟩ := hfin.exists_pow_eq_one
  obtain ⟨n, npos, hn⟩ := ((QuotientGroup.eq_one_iff _).mp hm).exists_pow_eq_one
  exact (QuotientGroup.eq_one_iff g).mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m * n, mul_pos mpos npos, (pow_mul g m n).symm ▸ hn⟩)

end CommGroup

section AddCommGroup

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] :
    Module R (M ⧸ AddCommGroup.torsion M) :=
  -- Upgrade the torsion subgroup to a submodule.
  letI S : Submodule R M := { AddCommGroup.torsion M with smul_mem' := fun r m ⟨n, hn, hn'⟩ ↦
    ⟨n, hn, by { simp only [Function.IsPeriodicPt, Function.IsFixedPt, add_left_iterate, add_zero,
      smul_comm n] at hn' ⊢; simp only [hn', smul_zero] }⟩ }
  -- The quotients are the same.
  let e : (M ⧸ AddCommGroup.torsion M) ≃+ (M ⧸ S) := QuotientAddGroup.congr _ _ (.refl _)
    (by simp [S])
  -- So we can copy over scalar multiplication.
  letI : SMul R (M ⧸ AddCommGroup.torsion M) := ⟨fun r m ↦ e.symm (r • e m)⟩
  Function.Injective.module R e.toAddMonoidHom e.injective (fun _ _ ↦
    e.symm.injective (e.symm_apply_apply _))

end AddCommGroup

section

variable {M : Type*} [CommMonoid M] [HasDistribNeg M]

/-
**neg_one_mem_torsion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_one_mem_torsion : -1 in CommMonoid.torsion M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPeriodicPt_mul_iff_pow_eq_one`：isPeriodicPt_mul_iff_pow_eq_one (x : G)
 : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_one_mem_torsion : -1 ∈ CommMonoid.torsion M :=
  ⟨2, zero_lt_two, (isPeriodicPt_mul_iff_pow_eq_one _).mpr (by simp)⟩

end

