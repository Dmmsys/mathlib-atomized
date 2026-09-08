/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.GroupTheory.Archimedean
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Topology on archimedean groups and fields

In this file we prove the following theorems:

- `Rat.denseRange_cast`: the coercion from `ℚ` to a linear ordered archimedean field has dense
  range;

- `AddSubgroup.dense_of_not_isolated_zero`, `AddSubgroup.dense_of_no_min`: two sufficient conditions
  for a subgroup of an archimedean linear ordered additive commutative group to be dense;

- `AddSubgroup.dense_or_cyclic`: an additive subgroup of an archimedean linear ordered additive
  commutative group `G` with order topology either is dense in `G` or is a cyclic subgroup.
-/

public section

open Set

/-- Rational numbers are dense in a linear ordered archimedean field. -/
/-
**Rat.denseRange_cast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] 
[TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜] : DenseRange ((↑) : Rat -
> 𝕜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dense_of_exists_between`：dense_of_exists_between [Nontrivial α] {s : Set
 α} (h : forall ⦃a b⦄, a < b -> exists c in s, c in Ioo a b) : Dense s
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y

--- 原说明 ---
Rational numbers are dense in a linear ordered archimedean field.
-/
theorem Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [Archimedean 𝕜] : DenseRange ((↑) : ℚ → 𝕜) :=
  dense_of_exists_between fun _ _ h => Set.exists_range_iff.2 <| exists_rat_btwn h

namespace Subgroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
  [TopologicalSpace G] [OrderTopology G]
  [MulArchimedean G]

/-- A subgroup of an archimedean linear ordered multiplicative commutative group with order
topology is dense provided that for all `ε > 1` there exists an element of the subgroup
that belongs to `(1, ε)`. -/
@[to_additive /-- An additive subgroup of an archimedean linear ordered additive commutative group
with order topology is dense provided that for all positive `ε` there exists a positive element of
the subgroup that is less than `ε`. -/]
/-
**Subgroup.dense_of_not_isolated_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：dense_of_not_isolated_one (S : Subgroup G) (hS : forall ε > 1, exists g in
 S, g in Ioo 1 ε) : Dense (S : Set G)
参数：S : Subgroup G；hS : forall ε > 1, exists g in S, g in Ioo 1 ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
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
· 使用定理 `dense_of_exists_between`：dense_of_exists_between [Nontrivial α] {s : Set
 α} (h : forall ⦃a b⦄, a < b -> exists c in s, c in Ioo a b) : Dense s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_lt_div'`：one_lt_div' : 1 < a / b ↔ b < a
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用定理 `existsUnique_add_zpow_mem_Ioc`：existsUnique_add_zpow_mem_Ioc {a : G} (ha
 : 1 < a) (b c : G) : exists! m : Int, b * a ^ m in Set.Ioc c (c * a)
· 使用定理 `zpow_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : DivInvMonoid M] [inst_
1 : SetLike S M] [hSM : SubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n : ℤ…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `lt_div_iff_mul_lt'`：lt_div_iff_mul_lt' : b < c / a ↔ a * b < c
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
-/
theorem dense_of_not_isolated_one (S : Subgroup G) (hS : ∀ ε > 1, ∃ g ∈ S, g ∈ Ioo 1 ε) :
    Dense (S : Set G) := by
  cases subsingleton_or_nontrivial G
  · refine fun x => _root_.subset_closure ?_
    rw [Subsingleton.elim x 1]
    exact one_mem S
  refine dense_of_exists_between fun a b hlt => ?_
  rcases hS (b / a) (one_lt_div'.2 hlt) with ⟨g, hgS, hg0, hg⟩
  rcases (existsUnique_add_zpow_mem_Ioc hg0 1 a).exists with ⟨m, hm⟩
  rw [one_mul] at hm
  refine ⟨g ^ m, zpow_mem hgS _, hm.1, hm.2.trans_lt ?_⟩
  rwa [lt_div_iff_mul_lt'] at hg

/-- Let `S` be a nontrivial subgroup in an archimedean linear ordered multiplicative commutative
group `G` with order topology. If the set of elements of `S` that are greater than one
does not have a minimal element, then `S` is dense `G`. -/
@[to_additive /-- Let `S` be a nontrivial additive subgroup in an archimedean linear ordered
additive commutative group `G` with order topology. If the set of positive elements of `S` does not
have a minimal element, then `S` is dense `G`. -/]
/-
**Subgroup.dense_of_no_min** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：dense_of_no_min (S : Subgroup G) (hbot : S != ⊥) (H : ¬exists a : G, IsLea
st { g : G | g in S ∧ 1 < g } a) : Dense (S : Set G)
参数：S : Subgroup G；hbot : S != ⊥；H : ¬exists a : G, IsLeast { g : G | g in S ∧ 1 
< g } a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.dense_of_not_isolated_one`：dense_of_not_isolated_one (S : Subgr
oup G) (hS : forall ε > 1, exists g in S, g in Ioo 1 ε) : Dense (S : Set G)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Subgroup.exists_isLeast_one_lt`：Subgroup.exists_isLeast_one_lt {H : Subg
roup G} (hbot : H != ⊥) {a : G} (h₀ : 1 < a) (hd : Disjoint (H : Set G) (Ioo 1 a
)) : exists b, IsLea…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
-/
theorem dense_of_no_min (S : Subgroup G) (hbot : S ≠ ⊥)
    (H : ¬∃ a : G, IsLeast { g : G | g ∈ S ∧ 1 < g } a) : Dense (S : Set G) := by
  refine S.dense_of_not_isolated_one fun ε ε1 => ?_
  contrapose! H
  exact exists_isLeast_one_lt hbot ε1 (disjoint_left.2 H)

/-- A subgroup of an archimedean linear ordered multiplicative commutative group `G` with order
topology either is dense in `G` or is a cyclic subgroup. -/
@[to_additive dense_or_cyclic
/-- An additive subgroup of an archimedean linear ordered additive commutative group `G`
with order topology either is dense in `G` or is a cyclic subgroup. -/]
/-
**Subgroup.dense_or_cyclic** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：dense_or_cyclic (S : Subgroup G) : Dense (S : Set G) ∨ exists a : G, S = c
losure {a}
参数：S : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Subgroup.dense_of_not_isolated_one`：dense_of_not_isolated_one (S : Subgr
oup G) (hS : forall ε > 1, exists g in S, g in Ioo 1 ε) : Dense (S : Set G)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Subgroup.cyclic_of_isolated_one`：Subgroup.cyclic_of_isolated_one {H : Su
bgroup G} {a : G} (h₀ : 1 < a) (hd : Disjoint (H : Set G) (Ioo 1 a)) : exists b,
 H = closure {b}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem dense_or_cyclic (S : Subgroup G) : Dense (S : Set G) ∨ ∃ a : G, S = closure {a} := by
  refine (em _).imp (dense_of_not_isolated_one S) fun h => ?_
  push Not at h
  rcases h with ⟨ε, ε1, hε⟩
  exact cyclic_of_isolated_one ε1 (disjoint_left.2 hε)

variable [Nontrivial G] [DenselyOrdered G]

/-- In a nontrivial densely linear ordered archimedean topological multiplicative group,
a subgroup is either dense or is cyclic, but not both.

For a non-exclusive `Or` version with weaker assumptions, see `Subgroup.dense_or_cyclic` above. -/
@[to_additive dense_xor_cyclic
/-- In a nontrivial densely linear ordered archimedean topological additive group,
a subgroup is either dense or is cyclic, but not both.

For a non-exclusive `Or` version with weaker assumptions, see `AddSubgroup.dense_or_cyclic` above.
-/]
/-
**Subgroup.dense_xor_cyclic** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：dense_xor_cyclic (s : Subgroup G) : Xor (Dense (s : Set G)) (exists a, s =
 .zpowers a)
参数：s : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `xor_true`：Xor True = Not
· 使用定理 `not_denseRange_zpow`：not_denseRange_zpow [Nontrivial G] [DenselyOrdered 
G] {a : G} : ¬DenseRange (a ^ · : Int -> G)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.zpowers_eq_closure`：zpowers_eq_closure (g : G) : zpowers g = cl
osure {g}
· 使用定理 `xor_false`：Xor False = id
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Subgroup.dense_or_cyclic`：dense_or_cyclic (S : Subgroup G) : Dense (S : 
Set G) ∨ exists a : G, S = closure {a}
-/
theorem dense_xor_cyclic (s : Subgroup G) :
    Xor (Dense (s : Set G)) (∃ a, s = .zpowers a) := by
  if hd : Dense (s : Set G) then
    simp only [hd, xor_true]
    rintro ⟨a, rfl⟩
    exact not_denseRange_zpow hd
  else
    simp only [hd, xor_false, id, zpowers_eq_closure]
    exact s.dense_or_cyclic.resolve_left hd

@[to_additive (attr := deprecated dense_xor_cyclic (since := "2026-04-27"))]
alias dense_xor'_cyclic := dense_xor_cyclic

@[to_additive]
/-
**Subgroup.dense_iff_ne_zpowers** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：dense_iff_ne_zpowers {s : Subgroup G} : Dense (s : Set G) ↔ forall a, s !=
 .zpowers a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `xor_iff_iff_not`：xor_iff_iff_not : Xor a b ↔ (a ↔ ¬b)
· 使用定理 `Subgroup.dense_xor_cyclic`：dense_xor_cyclic (s : Subgroup G) : Xor (Dens
e (s : Set G)) (exists a, s = .zpowers a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dense_iff_ne_zpowers {s : Subgroup G} :
    Dense (s : Set G) ↔ ∀ a, s ≠ .zpowers a := by
  simp [xor_iff_iff_not.1 s.dense_xor_cyclic]

end Subgroup

