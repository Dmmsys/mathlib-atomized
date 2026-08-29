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
  with the permutation cycles `V = {(), (1 2)(3 4), (1 3)(2 4), (1 4)(2 3)}`. This is the kernel
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

/--
Definition of `IsAddKleinFour` / `IsAddKleinFour` 的定义

English:
class IsAddKleinFour
  parameters: (G : Type*) [AddGroup G]
  axioms and operations (2):
    - card_four : Nat.card G = 4
    - exponent_two : AddMonoid.exponent G = 2

中文:
类 是加法KleinFour
  参数: (G : 类型) [加法群 G]
  公理与运算 (2 个):
    - card_four : 自然数.card G = 4
    - exponent_two : 加法幺半群.exponent G = 2
-/
class IsAddKleinFour (G : Type*) [AddGroup G] : Prop where
  card_four : Nat.card G = 4
  exponent_two : AddMonoid.exponent G = 2

/-- A Klein four-group is a group of cardinality four and exponent two. -/
@[to_additive existing IsAddKleinFour]
/--
Definition of `IsKleinFour` / `IsKleinFour` 的定义

English:
class IsKleinFour
  parameters: (G : Type*) [Group G]
  axioms and operations (2):
    - card_four : Nat.card G = 4
    - exponent_two : Monoid.exponent G = 2

中文:
类 是KleinFour
  参数: (G : 类型) [群 G]
  公理与运算 (2 个):
    - card_four : 自然数.card G = 4
    - exponent_two : 幺半群.exponent G = 2
-/
class IsKleinFour (G : Type*) [Group G] : Prop where
  card_four : Nat.card G = 4
  exponent_two : Monoid.exponent G = 2

attribute [simp] IsKleinFour.card_four IsKleinFour.exponent_two
  IsAddKleinFour.card_four IsAddKleinFour.exponent_two

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddKleinFour (ZMod 2 × ZMod 2)
  body: by simp
  exponent_two := by simp [AddMonoid.exponent_prod]

中文:
实例 :
  签名: 是加法KleinFour (ZMod 2 × ZMod 2)
  定义体: by simp
  exponent_two := by simp [AddMonoid.exponent_prod]

Depends on / 依赖: AddMonoid, AddMonoid.exponent_prod, exponent_prod, exponent_two
-/
instance : IsAddKleinFour (ZMod 2 × ZMod 2) where
  card_four := by simp
  exponent_two := by simp [AddMonoid.exponent_prod]

instance {G : Type*} [Group G] [IsKleinFour G] : IsAddKleinFour (Additive G) where
  card_four := by rw [← IsKleinFour.card_four (G := G)]; congr!
  exponent_two := by simp

instance {G : Type*} [AddGroup G] [IsAddKleinFour G] : IsKleinFour (Multiplicative G) where
  card_four := by rw [← IsAddKleinFour.card_four (G := G)]; congr!
  exponent_two := by simp

namespace IsKleinFour

@[to_additive]
/--
theorem `isMulCommutative` / 定理 `isMulCommutative`

English:
theorem isMulCommutative
  given: {G : Type*} [Group G] [IsKleinFour G]
  proof: mul_comm_of_exponent_two exponent_two

中文:
定理 isMulCommutative
  条件: {G : 类型} [群 G] [是KleinFour G]
  证明: mul_comm_of_exponent_two exponent_two

Depends on / 依赖: exponent_two, mul_comm_of_exponent_two
-/
theorem isMulCommutative {G : Type*} [Group G] [IsKleinFour G] :
    IsMulCommutative G where
  is_comm.comm := mul_comm_of_exponent_two exponent_two

/-- This instance is scoped, because it always applies (which makes linting and typeclass inference
potentially *a lot* slower). -/
@[to_additive]
scoped instance instFinite {G : Type*} [Group G] [IsKleinFour G] : Finite G :=
Nat.finite_of_card_ne_zero by simp [IsKleinFour.card_four]

@[to_additive (attr := simp)]
/--
lemma `card_four'` / 引理 `card_four'`

English:
lemma card_four'
  given: {G : Type*} [Group G] [Fintype G] [IsKleinFour G]
  proof: Nat.card_eq_fintype_card (α := G).symm ▸ IsKleinFour.card_four

中文:
引理 card_four'
  条件: {G : 类型} [群 G] [有限类型 G] [是KleinFour G]
  证明: Nat.card_eq_fintype_card (α := G).symm ▸ IsKleinFour.card_four

Depends on / 依赖: IsKleinFour, IsKleinFour.card_four, Nat.card_eq_fintype_card, card_eq_fintype_card, card_four
-/
lemma card_four' {G : Type*} [Group G] [Fintype G] [IsKleinFour G] :
    Fintype.card G = 4 :=
  Nat.card_eq_fintype_card (α := G).symm ▸ IsKleinFour.card_four

open Finset

variable {G : Type*} [Group G] [IsKleinFour G]

@[to_additive]
/--
lemma `not_isCyclic` / 引理 `not_isCyclic`

English:
lemma not_isCyclic
  statement: ¬IsCyclic G
  proof: fun h => by simpa using h.exponent_eq_card

@[to_additive]

中文:
引理 not_isCyclic
  结论: ¬是循环 G
  证明: fun h => by simpa using h.exponent_eq_card

@[to_additive]

Depends on / 依赖: Encodable, IsEmpty, _root_, _root_.IsEmpty.toEncodable, exponent_eq_card, h.exponent_eq_card, toEncodable
-/
lemma not_isCyclic : ¬IsCyclic G :=
  fun h => by simpa using h.exponent_eq_card

@[to_additive]
/--
lemma `inv_eq_self` / 引理 `inv_eq_self`

English:
lemma inv_eq_self
  given: (x : G)
  statement: x⁻¹ = x
  proof: inv_eq_self_of_exponent_two (by simp) x

中文:
引理 inv_eq_self
  条件: (x : G)
  结论: x⁻¹ = x
  证明: inv_eq_self_of_exponent_two (by simp) x

Depends on / 依赖: inv_eq_self_of_exponent_two
-/
lemma inv_eq_self (x : G) : x⁻¹ = x := inv_eq_self_of_exponent_two (by simp) x

/- this is not an appropriate global `simp` lemma for a `Prop`-mixin class. Indeed, if it were
then every time Lean sees `·⁻¹` it would try to apply `inv_eq_self` which would trigger
type class inference to try and synthesize an `IsKleinFour` instance. -/
scoped[IsKleinFour] attribute [simp] inv_eq_self
scoped[IsAddKleinFour] attribute [simp] neg_eq_self

@[to_additive]
/--
lemma `mul_self` / 引理 `mul_self`

English:
lemma mul_self
  given: (x : G)
  statement: x * x = 1
  proof: by
  rw [mul_eq_one_iff_eq_inv]; rw [inv_eq_self]

@[to_additive]

中文:
引理 mul_self
  条件: (x : G)
  结论: x * x = 1
  证明: by
  rw [mul_eq_one_iff_eq_inv]; rw [inv_eq_self]

@[to_additive]

Depends on / 依赖: inv_eq_self, mul_eq_one_iff_eq_inv
-/
lemma mul_self (x : G) : x * x = 1 := by
  rw [mul_eq_one_iff_eq_inv]; rw [inv_eq_self]

@[to_additive]
/--
lemma `eq_finset_univ` / 引理 `eq_finset_univ`

English:
lemma eq_finset_univ
  statement: [Fintype G] [DecidableEq G]
  proof: by
  apply Finset.eq_univ_of_card
  rw [card_four']
  repeat rw [card_insert_of_notMem]
  on_goal 4 => simpa using mul_notMem_of_exponent_two (by simp) hx hy hxy
  all_goals simp_all

@[to_additive]

中文:
引理 eq_finset_univ
  结论: [有限类型 G] [DecidableEq G]
  证明: by
  apply Finset.eq_univ_of_card
  rw [card_four']
  repeat rw [card_insert_of_notMem]
  on_goal 4 => simpa using mul_notMem_of_exponent_two (by simp) hx hy hxy
  all_goals simp_all

@[to_additive]

Depends on / 依赖: Finset, Finset.eq_univ_of_card, all_goals, card_four, card_insert_of_notMem, eq_univ_of_card, mul_notMem_of_exponent_two, on_goal, repeat
-/
lemma eq_finset_univ [Fintype G] [DecidableEq G]
    {x y : G} (hx : x != 1) (hy : y != 1) (hxy : x != y) : {x * y, x, y, (1 : G)} = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [card_four']
  repeat rw [card_insert_of_notMem]
  on_goal 4 => simpa using mul_notMem_of_exponent_two (by simp) hx hy hxy
  all_goals simp_all

@[to_additive]
/--
lemma `eq_mul_of_ne_all` / 引理 `eq_mul_of_ne_all`

English:
lemma eq_mul_of_ne_all
  statement: {x y z : G} (hx : x != 1)
  proof: by
  classical
  let _ := Fintype.ofFinite G
apply eq_of_mem_insert_of_notMem (eq_finset_univ hx hy hxy).symm ▸ mem_univ _
  simpa only [mem_singleton, mem_insert, not_or] using ⟨hzx, hzy, hz⟩

中文:
引理 eq_mul_of_ne_all
  结论: {x y z : G} (hx : x != 1)
  证明: by
  classical
  let _ := Fintype.ofFinite G
apply eq_of_mem_insert_of_notMem (eq_finset_univ hx hy hxy).symm ▸ mem_univ _
  simpa only [mem_singleton, mem_insert, not_or] using ⟨hzx, hzy, hz⟩

Depends on / 依赖: Fintype, Fintype.ofFinite, classical, eq_finset_univ, eq_of_mem_insert_of_notMem, mem_insert, mem_singleton, mem_univ, not_or, ofFinite
-/
lemma eq_mul_of_ne_all {x y z : G} (hx : x != 1)
    (hy : y != 1) (hxy : x != y) (hz : z != 1) (hzx : z != x) (hzy : z != y) : z = x * y := by
  classical
  let _ := Fintype.ofFinite G
apply eq_of_mem_insert_of_notMem (eq_finset_univ hx hy hxy).symm ▸ mem_univ _
  simpa only [mem_singleton, mem_insert, not_or] using ⟨hzx, hzy, hz⟩

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] [IsKleinFour G₁]

/-- An equivalence between an `IsKleinFour` group `G₁` and a group `G₂` of exponent two which sends
`1 : G₁` to `1 : G₂` is in fact an isomorphism. -/
@[to_additive /-- An equivalence between an `IsAddKleinFour` group `G₁` and a group `G₂` of exponent
two which sends `0 : G₁` to `0 : G₂` is in fact an isomorphism. -/]
/--
Definition of `mulEquiv'` / `mulEquiv'` 的定义

English:
definition mulEquiv'
  signature: (e : G₁ ≃ G₂) (he : e 1 = 1) (h : Monoid.exponent G₂ = 2)
  body: e
  map_mul' := by
    let _inst₁ := Fintype.ofFinite G₁
    let _inst₂ := Fintype.ofEquiv G₁ e
    intro x y
    by_cases hx : x = 1 <;> by_cases hy : y = 1
    all_goals try simp only [hx, hy, mul_one, one_mul, Equiv.toFun_as_coe, he]
    by_cases hxy : x = y
    · simp [hxy, mul_self, ← pow_two (

中文:
定义 mulEquiv'
  签名: (e : G₁ ≃ G₂) (he : e 1 = 1) (h : 幺半群.exponent G₂ = 2)
  定义体: e
  map_mul' := by
    let _inst₁ := Fintype.ofFinite G₁
    let _inst₂ := Fintype.ofEquiv G₁ e
    intro x y
    by_cases hx : x = 1 <;> by_cases hy : y = 1
    all_goals try simp only [hx, hy, mul_one, one_mul, Equiv.toFun_as_coe, he]
    by_cases hxy : x = y
    · simp [hxy, mul_self, ← pow_two (
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
      rw [← Ne]; rw [← e.injective.ne_iff] at hx hy hxy
      rw [he] at hx hy
      symm
apply eq_of_mem_insert_of_notMem univ₂.symm ▸ mem_univ _
      simpa using mul_notMem_of_exponent_two h hx hy hxy

/-- Any two `IsKleinFour` groups are isomorphic via any equivalence which sends the identity of one
group to the identity of the other. -/
@[to_additive /-- Any two `IsAddKleinFour` groups are isomorphic via any
equivalence which sends the identity of one group to the identity of the other. -/]
/--
Definition of `mulEquiv` / `mulEquiv` 的定义

English:
abbreviation mulEquiv
  signature: [IsKleinFour G₂] (e : G₁ ≃ G₂) (he : e 1 = 1)
  body: mulEquiv' e he exponent_two

中文:
缩写 mulEquiv
  签名: [是KleinFour G₂] (e : G₁ ≃ G₂) (he : e 1 = 1)
  定义体: mulEquiv' e he exponent_two

Depends on / 依赖: exponent_two, mulEquiv
-/
abbrev mulEquiv [IsKleinFour G₂] (e : G₁ ≃ G₂) (he : e 1 = 1) : G₁ ≃* G₂ :=
  mulEquiv' e he exponent_two

/-- Any two `IsKleinFour` groups are isomorphic. -/
@[to_additive /-- Any two `IsAddKleinFour` groups are isomorphic. -/]
/--
lemma `nonempty_mulEquiv` / 引理 `nonempty_mulEquiv`

English:
lemma nonempty_mulEquiv
  given: [IsKleinFour G₂]
  statement: Nonempty (G₁ ≃* G₂)
  proof: by
  classical
  let _inst₁ := Fintype.ofFinite G₁
  let _inst₁ := Fintype.ofFinite G₂
exact ⟨mulEquiv ((Fintype.equivOfCardEq <| by simp).setValue 1 1) by simp⟩

中文:
引理 nonempty_mulEquiv
  条件: [是KleinFour G₂]
  结论: 非空 (G₁ ≃* G₂)
  证明: by
  classical
  let _inst₁ := Fintype.ofFinite G₁
  let _inst₁ := Fintype.ofFinite G₂
exact ⟨mulEquiv ((Fintype.equivOfCardEq <| by simp).setValue 1 1) by simp⟩

Depends on / 依赖: Fintype, Fintype.equivOfCardEq, Fintype.ofFinite, classical, equivOfCardEq, mulEquiv, ofFinite, setValue
-/
lemma nonempty_mulEquiv [IsKleinFour G₂] : Nonempty (G₁ ≃* G₂) := by
  classical
  let _inst₁ := Fintype.ofFinite G₁
  let _inst₁ := Fintype.ofFinite G₂
exact ⟨mulEquiv ((Fintype.equivOfCardEq <| by simp).setValue 1 1) by simp⟩

end IsKleinFour
