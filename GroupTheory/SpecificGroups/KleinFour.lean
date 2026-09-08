/-
Copyright (c) 2023 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Klein Four Group

The Klein (Vierergruppe) four-group is a non-cyclic abelian group with four elements, in which
each element is self-inverse and in which composing any two of the three non-identity elements
produces the third one.

## Main definitions

* `IsKleinFour` : A mixin class which states that the group has order four and exponent two.
* `mulEquiv'` : An equivalence between a Klein four-group and a group of exponent two which
  preserves the identity is in fact an isomorphism.
* `mulEquiv`: Any two Klein four-groups are isomorphic via any identity-preserving equivalence.

## References

* https://en.wikipedia.org/wiki/Klein_four-group
* https://en.wikipedia.org/wiki/Alternating_group

## TODO

* Prove an `IsKleinFour` group is isomorphic to the normal subgroup of `alternatingGroup (Fin 4)`
  with the permutation cycles `V = {(), (1 2)(3 4), (1 3)(2 4), (1 4)(2 3)}`.  This is the kernel
  of the surjection of `alternatingGroup (Fin 4)` onto `alternatingGroup (Fin 3) ≃ (ZMod 3)`.
  In other words, we have the exact sequence `V → A₄ → A₃`.

* The outer automorphism group of `A₆` is the Klein four-group `V = (ZMod 2) × (ZMod 2)`,
  and is related to the outer automorphism of `S₆`. The extra outer automorphism in `A₆`
  swaps the 3-cycles (like `(1 2 3)`) with elements of shape `3²` (like `(1 2 3)(4 5 6)`).

## Tags
non-cyclic abelian group
-/

@[expose] public section

/-! ### Klein four-groups as a mixin class -/

/-- An (additive) Klein four-group is an (additive) group of cardinality four and exponent two. -/
/-
**IsAddKleinFour** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [AddGroup G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An (additive) Klein four-group is an (additive) group of cardinality four and ex
ponent two.
-/
class IsAddKleinFour (G : Type*) [AddGroup G] : Prop where
  card_four : Nat.card G = 4
  exponent_two : AddMonoid.exponent G = 2

/-- A Klein four-group is a group of cardinality four and exponent two. -/
@[to_additive existing IsAddKleinFour]
/-
**IsKleinFour** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Klein four-group is a group of cardinality four and exponent two.
-/
class IsKleinFour (G : Type*) [Group G] : Prop where
  card_four : Nat.card G = 4
  exponent_two : Monoid.exponent G = 2

attribute [simp] IsKleinFour.card_four IsKleinFour.exponent_two
  IsAddKleinFour.card_four IsAddKleinFour.exponent_two
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddKleinFour (ZMod 2 × ZMod 2) where
  card_four := by simp
  exponent_two := by simp [AddMonoid.exponent_prod]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type*} [Group G] [IsKleinFour G] : IsAddKleinFour (Additive G) where
  card_four := by rw [← IsKleinFour.card_four (G := G)]; congr!
  exponent_two := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type*} [AddGroup G] [IsAddKleinFour G] : IsKleinFour (Multiplicative G) where
  card_four := by rw [← IsAddKleinFour.card_four (G := G)]; congr!
  exponent_two := by simp

namespace IsKleinFour

@[to_additive]
/-
**IsKleinFour.isMulCommutative** 是 Mathlib 中的一个定理，位于命名空间 `IsKleinFour`。
形式化陈述：isMulCommutative {G : Type*} [Group G] [IsKleinFour G] : IsMulCommutative 
G where is_comm.comm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_comm_of_exponent_two`：mul_comm_of_exponent_two [IsCancelMul G] (hG :
 Monoid.exponent G = 2) (a b : G) : a * b = b * a
· 使用定理 `CancelMonoid.toIsCancelMul`：∀ (M : Type u) [inst : CancelMonoid M], IsCa
ncelMul M
· 使用定理 `IsKleinFour.exponent_two`：∀ {G : Type u_1} {inst : Group G} [self : IsKl
einFour G], Monoid.exponent G = 2
-/
theorem isMulCommutative {G : Type*} [Group G] [IsKleinFour G] :
    IsMulCommutative G where
  is_comm.comm := mul_comm_of_exponent_two exponent_two

/-- This instance is scoped, because it always applies (which makes linting and typeclass inference
potentially *a lot* slower). -/
@[to_additive]
/-
**IsKleinFour.instFinite** 是 Mathlib 中的一个定理，位于命名空间 `IsKleinFour`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] [IsKleinFour G], Finite G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsKleinFour.card_four`：∀ {G : Type u_1} {inst : Group G} [self : IsKlein
Four G], Nat.card G = 4
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
This instance is scoped, because it always applies (which makes linting and type
class inference
potentially *a lot* slower).
-/
scoped instance instFinite {G : Type*} [Group G] [IsKleinFour G] : Finite G :=
  Nat.finite_of_card_ne_zero <| by simp [IsKleinFour.card_four]

@[to_additive (attr := simp)]
/-
**IsKleinFour.card_four'** 是 Mathlib 中的一个引理，位于命名空间 `IsKleinFour`。
形式化陈述：card_four' {G : Type*} [Group G] [Fintype G] [IsKleinFour G] : Fintype.car
d G = 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsKleinFour.card_four`：∀ {G : Type u_1} {inst : Group G} [self : IsKlein
Four G], Nat.card G = 4
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
-/
lemma card_four' {G : Type*} [Group G] [Fintype G] [IsKleinFour G] :
    Fintype.card G = 4 :=
  Nat.card_eq_fintype_card (α := G).symm ▸ IsKleinFour.card_four

open Finset

variable {G : Type*} [Group G] [IsKleinFour G]

@[to_additive]
/-
**IsKleinFour.not_isCyclic** 是 Mathlib 中的一个引理，位于命名空间 `IsKleinFour`。
形式化陈述：not_isCyclic : ¬IsCyclic G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsKleinFour.exponent_two`：∀ {G : Type u_1} {inst : Group G} [self : IsKl
einFour G], Monoid.exponent G = 2
· 使用定理 `IsKleinFour.card_four`：∀ {G : Type u_1} {inst : Group G} [self : IsKlein
Four G], Nat.card G = 4
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `IsCyclic.exponent_eq_card`：IsCyclic.exponent_eq_card [Group α] [IsCyclic
 α] : exponent α = Nat.card α
-/
lemma not_isCyclic : ¬IsCyclic G :=
  fun h ↦ by simpa using h.exponent_eq_card

@[to_additive]
/-
**IsKleinFour.inv_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `IsKleinFour`。
形式化陈述：inv_eq_self (x : G) : x⁻¹ = x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inv_eq_self_of_exponent_two`：inv_eq_self_of_exponent_two (hG : Monoid.ex
ponent G = 2) (x : G) : x⁻¹ = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsKleinFour.exponent_two`：∀ {G : Type u_1} {inst : Group G} [self : IsKl
einFour G], Monoid.exponent G = 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_eq_self (x : G) : x⁻¹ = x := inv_eq_self_of_exponent_two (by simp) x

/- this is not an appropriate global `simp` lemma for a `Prop`-mixin class. Indeed, if it were
then every time Lean sees `·⁻¹` it would try to apply `inv_eq_self` which would trigger
type class inference to try and synthesize an `IsKleinFour` instance. -/
scoped[IsKleinFour] attribute [simp] inv_eq_self
scoped[IsAddKleinFour] attribute [simp] neg_eq_self

@[to_additive]
/-
**IsKleinFour.mul_self** 是 Mathlib 中的一个引理，位于命名空间 `IsKleinFour`。
形式化陈述：mul_self (x : G) : x * x = 1
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
· 使用引理 `IsKleinFour.inv_eq_self`：inv_eq_self (x : G) : x⁻¹ = x
-/
lemma mul_self (x : G) : x * x = 1 := by
  rw [mul_eq_one_iff_eq_inv, inv_eq_self]

@[to_additive]
/-
**IsKleinFour.eq_finset_univ** 是 Mathlib 中的一个引理，位于命名空间 `IsKleinFour`。
形式化陈述：eq_finset_univ [Fintype G] [DecidableEq G] {x y : G} (hx : x != 1) (hy : y
 != 1) (hxy : x != y) : {x * y, x, y, (1 : G)} = Finset.univ
参数：hx : x != 1；hy : y != 1；hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_univ_of_card`：Finset.eq_univ_of_card [Fintype α] (s : Finset α
) (hs : #s = Fintype.card α) : s = univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsKleinFour.card_four'`：card_four' {G : Type*} [Group G] [Fintype G] [Is
KleinFour G] : Fintype.card G = 4
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用引理 `mul_notMem_of_exponent_two`：mul_notMem_of_exponent_two (h : Monoid.expon
ent G = 2) {x y : G} (hx : x != 1) (hy : y != 1) (hxy : x != y) : x * y ∉ ({x, y
, 1} : Set G)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsKleinFour.exponent_two`：∀ {G : Type u_1} {inst : Group G} [self : IsKl
einFour G], Monoid.exponent G = 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
-/
lemma eq_finset_univ [Fintype G] [DecidableEq G]
    {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) : {x * y, x, y, (1 : G)} = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [card_four']
  repeat rw [card_insert_of_notMem]
  on_goal 4 => simpa using mul_notMem_of_exponent_two (by simp) hx hy hxy
  all_goals simp_all

@[to_additive]
/-
**IsKleinFour.eq_mul_of_ne_all** 是 Mathlib 中的一个引理，位于命名空间 `IsKleinFour`。
形式化陈述：eq_mul_of_ne_all {x y z : G} (hx : x != 1) (hy : y != 1) (hxy : x != y) (h
z : z != 1) (hzx : z != x) (hzy : z != y) : z = x * y
参数：hx : x != 1；hy : y != 1；hxy : x != y；hz : z != 1；hzx : z != x；hzy : z != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsKleinFour.instFinite`：∀ {G : Type u_1} [inst : Group G] [IsKleinFour G
], Finite G
· 使用定理 `Finset.eq_of_mem_insert_of_notMem`：eq_of_mem_insert_of_notMem (ha : b in
 insert a s) (hb : b ∉ s) : b = a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsKleinFour.eq_finset_univ`：eq_finset_univ [Fintype G] [DecidableEq G] {
x y : G} (hx : x != 1) (hy : y != 1) (hxy : x != y) : {x * y, x, y, (1 : G)} = F
inset.univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma eq_mul_of_ne_all {x y z : G} (hx : x ≠ 1)
    (hy : y ≠ 1) (hxy : x ≠ y) (hz : z ≠ 1) (hzx : z ≠ x) (hzy : z ≠ y) : z = x * y := by
  classical
  let _ := Fintype.ofFinite G
  apply eq_of_mem_insert_of_notMem <| (eq_finset_univ hx hy hxy).symm ▸ mem_univ _
  simpa only [mem_singleton, mem_insert, not_or] using ⟨hzx, hzy, hz⟩

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] [IsKleinFour G₁]

/-- An equivalence between an `IsKleinFour` group `G₁` and a group `G₂` of exponent two which sends
`1 : G₁` to `1 : G₂` is in fact an isomorphism. -/
@[to_additive /-- An equivalence between an `IsAddKleinFour` group `G₁` and a group `G₂` of exponent
two which sends `0 : G₁` to `0 : G₂` is in fact an isomorphism. -/]
/-
**IsKleinFour.mulEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `IsKleinFour`。
形式化陈述：mulEquiv' (e : G₁ ≃ G₂) (he : e 1 = 1) (h : Monoid.exponent G₂ = 2) : G₁ ≃
* G₂ where toEquiv
参数：e : G₁ ≃ G₂；he : e 1 = 1；h : Monoid.exponent G₂ = 2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulEquiv' (e : G₁ ≃ G₂) (he : e 1 = 1) (h : Monoid.exponent G₂ = 2) : G₁ ≃* G₂ where
  toEquiv := e
  map_mul' := by
    let _inst₁ := Fintype.ofFinite G₁
    let _inst₂ := Fintype.ofEquiv G₁ e
    intro x y
    by_cases hx : x = 1 <;> by_cases hy : y = 1
    all_goals try simp only [hx, hy, mul_one, one_mul, Equiv.toFun_as_coe, he]
    by_cases hxy : x = y
    · simp [hxy, mul_self, ← pow_two (e y), h ▸ Monoid.pow_exponent_eq_one (e y), he]
    · classical
      have univ₂ : {e (x * y), e x, e y, (1 : G₂)} = Finset.univ := by
        simpa [map_univ_equiv e, map_insert, he]
          using congr(Finset.map e.toEmbedding $(eq_finset_univ hx hy hxy))
      rw [← Ne, ← e.injective.ne_iff] at hx hy hxy
      rw [he] at hx hy
      symm
      apply eq_of_mem_insert_of_notMem <| univ₂.symm ▸ mem_univ _
      simpa using mul_notMem_of_exponent_two h hx hy hxy

/-- Any two `IsKleinFour` groups are isomorphic via any equivalence which sends the identity of one
group to the identity of the other. -/
@[to_additive /-- Any two `IsAddKleinFour` groups are isomorphic via any
equivalence which sends the identity of one group to the identity of the other. -/]
/-
**IsKleinFour.mulEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsKleinFour`。
形式化陈述：mulEquiv [IsKleinFour G₂] (e : G₁ ≃ G₂) (he : e 1 = 1) : G₁ ≃* G₂
参数：e : G₁ ≃ G₂；he : e 1 = 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsKleinFour.exponent_two`：∀ {G : Type u_1} {inst : Group G} [self : IsKl
einFour G], Monoid.exponent G = 2
-/
abbrev mulEquiv [IsKleinFour G₂] (e : G₁ ≃ G₂) (he : e 1 = 1) : G₁ ≃* G₂ :=
  mulEquiv' e he exponent_two

/-- Any two `IsKleinFour` groups are isomorphic. -/
@[to_additive /-- Any two `IsAddKleinFour` groups are isomorphic. -/]
/-
**IsKleinFour.nonempty_mulEquiv** 是 Mathlib 中的一个引理，位于命名空间 `IsKleinFour`。
形式化陈述：nonempty_mulEquiv [IsKleinFour G₂] : Nonempty (G₁ ≃* G₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsKleinFour.instFinite`：∀ {G : Type u_1} [inst : Group G] [IsKleinFour G
], Finite G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsKleinFour.card_four'`：card_four' {G : Type*} [Group G] [Fintype G] [Is
KleinFour G] : Fintype.card G = 4
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.setValue_eq`：setValue_eq (f : α ≃ β) (a : α) (b : β) : setValue f 
a b a = b

--- 原说明 ---
Any two `IsKleinFour` groups are isomorphic.
-/
lemma nonempty_mulEquiv [IsKleinFour G₂] : Nonempty (G₁ ≃* G₂) := by
  classical
  let _inst₁ := Fintype.ofFinite G₁
  let _inst₁ := Fintype.ofFinite G₂
  exact ⟨mulEquiv ((Fintype.equivOfCardEq <| by simp).setValue 1 1) <| by simp⟩

end IsKleinFour

