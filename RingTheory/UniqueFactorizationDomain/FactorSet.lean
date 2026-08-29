/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.Tactic.Ring

/-!
# Set of factors

## Main definitions
* `Associates.FactorSet`: multiset of factors of an element, unique up to propositional equality.
* `Associates.factors`: determine the `FactorSet` for a given element.

## TODO
* set up the complete lattice structure on `FactorSet`.

-/

@[expose] public section

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace Associates

open UniqueFactorizationMonoid Associated Multiset

variable [CommMonoidWithZero α]

/--
Definition of `FactorSet.` / `FactorSet.` 的定义

English:
abbreviation FactorSet.{u}
  signature: (α : Type u) [CommMonoidWithZero α]
  body: WithTop (Multiset { a : Associates α // Irreducible a })

中文:
缩写 FactorSet.{u}
  签名: (α : 类型u) [带零交换幺半群 α]
  定义体: WithTop (Multiset { a : Associates α // Irreducible a })

Depends on / 依赖: Associates, Irreducible, Multiset, WithTop
-/
abbrev FactorSet.{u} (α : Type u) [CommMonoidWithZero α] : Type u :=
  WithTop (Multiset { a : Associates α // Irreducible a })

attribute [local instance] Associated.setoid

/--
theorem `FactorSet.coe_add` / 定理 `FactorSet.coe_add`

English:
theorem FactorSet.coe_add
  given: {a b : Multiset { a : Associates α // Irreducible a }}
  proof: by norm_cast

中文:
定理 FactorSet.coe_add
  条件: {a b : Multiset { a : Associates α // 不可约 a }}
  证明: by norm_cast
-/
theorem FactorSet.coe_add {a b : Multiset { a : Associates α // Irreducible a }} :
    (↑(a + b) : FactorSet α) = a + b := by norm_cast

/--
theorem `FactorSet.sup_add_inf_eq_add` / 定理 `FactorSet.sup_add_inf_eq_add`

English:
theorem FactorSet.sup_add_inf_eq_add
  given: [DecidableEq (Associates α)]

中文:
定理 FactorSet.sup_add_inf_eq_add
  条件: [DecidableEq (Associates α)]
-/
theorem FactorSet.sup_add_inf_eq_add [DecidableEq (Associates α)] :
    forall a b : FactorSet α, a ⊔ b + a ⊓ b = a + b
  | ⊤, b => show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b by simp
  | a, ⊤ => show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤ by simp
  | WithTop.some a, WithTop.some b =>
    show (a : FactorSet α) ⊔ b + (a : FactorSet α) ⊓ b = a + b by
      rw [← WithTop.coe_sup]; rw [← WithTop.coe_inf]; rw [← WithTop.coe_add]; rw [← WithTop.coe_add]; rw [WithTop.coe_eq_coe]
      exact Multiset.union_add_inter _ _

/--
Definition of `FactorSet.prod` / `FactorSet.prod` 的定义

English:
definition FactorSet.prod
  signature: : FactorSet α -> Associates α

中文:
定义 FactorSet.乘积
  签名: : FactorSet α -> Associates α
-/
def FactorSet.prod : FactorSet α -> Associates α
  | ⊤ => 0
  | WithTop.some s => (s.map (↑)).prod

@[simp]
/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  statement: (⊤ : FactorSet α).prod = 0
  proof: rfl

@[simp]

中文:
定理 prod_top
  结论: (⊤ : FactorSet α).乘积 = 0
  证明: rfl

@[simp]
-/
theorem prod_top : (⊤ : FactorSet α).prod = 0 :=
  rfl

@[simp]
/--
theorem `prod_coe` / 定理 `prod_coe`

English:
theorem prod_coe
  given: {s : Multiset { a : Associates α // Irreducible a }}
  proof: rfl

@[simp]

中文:
定理 prod_coe
  条件: {s : Multiset { a : Associates α // 不可约 a }}
  证明: rfl

@[simp]
-/
theorem prod_coe {s : Multiset { a : Associates α // Irreducible a }} :
    FactorSet.prod (s : FactorSet α) = (s.map (↑)).prod :=
  rfl

@[simp]
/--
theorem `prod_add` / 定理 `prod_add`

English:
theorem prod_add
  statement: forall a b : FactorSet α, (a + b).prod = a.prod * b.prod

中文:
定理 prod_add
  结论: 对任意 a b : FactorSet α, (a + b).乘积 = a.乘积 * b.乘积
-/
theorem prod_add : forall a b : FactorSet α, (a + b).prod = a.prod * b.prod
  | ⊤, b => show (⊤ + b).prod = (⊤ : FactorSet α).prod * b.prod by simp
  | a, ⊤ => show (a + ⊤).prod = a.prod * (⊤ : FactorSet α).prod by simp
  | WithTop.some a, WithTop.some b => by
    rw [← FactorSet.coe_add]; rw [prod_coe]; rw [prod_coe]; rw [prod_coe]; rw [Multiset.map_add]; rw [Multiset.prod_add]

@[gcongr]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  statement: forall {a b : FactorSet α}, a <= b -> a.prod <= b.prod
  proof: top_unique h
    rw [this]; rw [prod_top]
  | a, ⊤, _ => show a.prod <= (⊤ : FactorSet α).prod by simp
  | WithTop.some _, WithTop.some _, h =>
prod_le_prod Multiset.map_le_map WithTop.coe_le_coe.1 h

中文:
定理 prod_mono
  结论: 对任意 {a b : FactorSet α}, a <= b -> a.乘积 <= b.乘积
  证明: top_unique h
    rw [this]; rw [prod_top]
  | a, ⊤, _ => show a.prod <= (⊤ : FactorSet α).prod by simp
  | WithTop.some _, WithTop.some _, h =>
prod_le_prod Multiset.map_le_map WithTop.coe_le_coe.1 h

Depends on / 依赖: top_unique
-/
theorem prod_mono : forall {a b : FactorSet α}, a <= b -> a.prod <= b.prod
  | ⊤, b, h => by
    have : b = ⊤ := top_unique h
    rw [this]; rw [prod_top]
  | a, ⊤, _ => show a.prod <= (⊤ : FactorSet α).prod by simp
  | WithTop.some _, WithTop.some _, h =>
prod_le_prod Multiset.map_le_map WithTop.coe_le_coe.1 h

/--
theorem `FactorSet.prod_eq_zero_iff` / 定理 `FactorSet.prod_eq_zero_iff`

English:
theorem FactorSet.prod_eq_zero_iff
  given: [IsCancelMulZero α] [Nontrivial α] (p : FactorSet α)
  proof: by
  unfold FactorSet at p
  induction p -- TODO: `induction_eliminator` doesn't work with `abbrev`
  · simp only [Associates.prod_top]
  · rw [prod_coe, Multiset.prod_eq_zero_iff, Multiset.mem_map, eq_false WithTop.coe_ne_top,
      iff_false, not_exists]
    exact fun a => not_and_of_not_right _ a.prop.ne_zero

中文:
定理 FactorSet.prod_eq_zero_iff
  条件: [是乘零消去 α] [非平凡 α] (p : FactorSet α)
  证明: by
  unfold FactorSet at p
  induction p -- TODO: `induction_eliminator` doesn't work with `abbrev`
  · simp only [Associates.prod_top]
  · rw [prod_coe, Multiset.prod_eq_zero_iff, Multiset.mem_map, eq_false WithTop.coe_ne_top,
      iff_false, not_exists]
    exact fun a => not_and_of_not_right _ a.prop.ne_zero

Depends on / 依赖: Associates, Associates.prod_top, FactorSet, Multiset, Multiset.mem_map, Multiset.prod_eq_zero_iff, WithTop, WithTop.coe_ne_top, a.prop.ne_zero, abbrev, coe_ne_top, eq_false, iff_false, induction_eliminator, mem_map, ne_zero, not_and_of_not_right, not_exists, prod_coe, prod_eq_zero_iff
-/
theorem FactorSet.prod_eq_zero_iff [IsCancelMulZero α] [Nontrivial α] (p : FactorSet α) :
    p.prod = 0 ↔ p = ⊤ := by
  unfold FactorSet at p
  induction p -- TODO: `induction_eliminator` doesn't work with `abbrev`
  · simp only [Associates.prod_top]
  · rw [prod_coe, Multiset.prod_eq_zero_iff, Multiset.mem_map, eq_false WithTop.coe_ne_top,
      iff_false, not_exists]
    exact fun a => not_and_of_not_right _ a.prop.ne_zero

section count

variable [DecidableEq (Associates α)]

/--
Definition of `bcount` / `bcount` 的定义

English:
definition bcount
  signature: (p : { a : Associates α // Irreducible a })

中文:
定义 bcount
  签名: (p : { a : Associates α // 不可约 a })
-/
def bcount (p : { a : Associates α // Irreducible a }) :
    FactorSet α -> Nat
  | ⊤ => 0
  | WithTop.some s => s.count p

variable [forall p : Associates α, Decidable (Irreducible p)] {p : Associates α}

/--
Definition of `count` / `count` 的定义

English:
definition count
  signature: (p : Associates α)
  body: if hp : Irreducible p then bcount ⟨p, hp⟩ else 0

@[simp]

中文:
定义 count
  签名: (p : Associates α)
  定义体: if hp : Irreducible p then bcount ⟨p, hp⟩ else 0

@[simp]

Depends on / 依赖: Irreducible, bcount
-/
def count (p : Associates α) : FactorSet α -> Nat :=
  if hp : Irreducible p then bcount ⟨p, hp⟩ else 0

@[simp]
/--
theorem `count_some` / 定理 `count_some`

English:
theorem count_some
  given: (hp : Irreducible p) (s : Multiset _)
  proof: by
  simp only [count, dif_pos hp, bcount]

@[simp]

中文:
定理 count_some
  条件: (hp : 不可约 p) (s : Multiset _)
  证明: by
  simp only [count, dif_pos hp, bcount]

@[simp]

Depends on / 依赖: bcount, dif_pos
-/
theorem count_some (hp : Irreducible p) (s : Multiset _) :
    count p (WithTop.some s) = s.count ⟨p, hp⟩ := by
  simp only [count, dif_pos hp, bcount]

@[simp]
/--
theorem `count_zero` / 定理 `count_zero`

English:
theorem count_zero
  given: (hp : Irreducible p)
  statement: count p (0 : FactorSet α) = 0
  proof: by
  simp only [count, dif_pos hp, bcount, Multiset.count_zero]

中文:
定理 count_zero
  条件: (hp : 不可约 p)
  结论: count p (0 : FactorSet α) = 0
  证明: by
  simp only [count, dif_pos hp, bcount, Multiset.count_zero]

Depends on / 依赖: Multiset, Multiset.count_zero, bcount, count_zero, dif_pos
-/
theorem count_zero (hp : Irreducible p) : count p (0 : FactorSet α) = 0 := by
  simp only [count, dif_pos hp, bcount, Multiset.count_zero]

/--
theorem `count_reducible` / 定理 `count_reducible`

English:
theorem count_reducible
  given: (hp : ¬Irreducible p)
  statement: count p = 0
  proof: dif_neg hp

中文:
定理 count_reducible
  条件: (hp : ¬不可约 p)
  结论: count p = 0
  证明: dif_neg hp

Depends on / 依赖: dif_neg
-/
theorem count_reducible (hp : ¬Irreducible p) : count p = 0 := dif_neg hp

end count

section Mem

/--
Definition of `BfactorSetMem` / `BfactorSetMem` 的定义

English:
definition BfactorSetMem
  signature: : { a : Associates α // Irreducible a } -> FactorSet α -> Prop

中文:
定义 BfactorSetMem
  签名: : { a : Associates α // 不可约 a } -> FactorSet α -> 命题
-/
def BfactorSetMem : { a : Associates α // Irreducible a } -> FactorSet α -> Prop
  | _, ⊤ => True
  | p, some l => p in l

/--
Definition of `FactorSetMem` / `FactorSetMem` 的定义

English:
definition FactorSetMem
  signature: (s : FactorSet α) (p : Associates α)
  body: letI : Decidable (Irreducible p) := Classical.dec _
  if hp : Irreducible p then BfactorSetMem ⟨p, hp⟩ s else False

中文:
定义 FactorSetMem
  签名: (s : FactorSet α) (p : Associates α)
  定义体: letI : Decidable (Irreducible p) := Classical.dec _
  if hp : Irreducible p then BfactorSetMem ⟨p, hp⟩ s else False

Depends on / 依赖: BfactorSetMem, Classical, Classical.dec, Decidable, Irreducible
-/
def FactorSetMem (s : FactorSet α) (p : Associates α) : Prop :=
  letI : Decidable (Irreducible p) := Classical.dec _
  if hp : Irreducible p then BfactorSetMem ⟨p, hp⟩ s else False

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (Associates α) (FactorSet α)
  body: ⟨FactorSetMem⟩

@[simp]

中文:
实例 :
  签名: Membership (Associates α) (FactorSet α)
  定义体: ⟨FactorSetMem⟩

@[simp]

Depends on / 依赖: FactorSetMem
-/
instance : Membership (Associates α) (FactorSet α) :=
  ⟨FactorSetMem⟩

@[simp]
/--
theorem `factorSetMem_eq_mem` / 定理 `factorSetMem_eq_mem`

English:
theorem factorSetMem_eq_mem
  given: (p : Associates α) (s : FactorSet α)
  statement: FactorSetMem s p = (p in s)
  proof: rfl

中文:
定理 factorSetMem_eq_mem
  条件: (p : Associates α) (s : FactorSet α)
  结论: FactorSetMem s p = (p in s)
  证明: rfl
-/
theorem factorSetMem_eq_mem (p : Associates α) (s : FactorSet α) : FactorSetMem s p = (p in s) :=
  rfl

/--
theorem `mem_factorSet_top` / 定理 `mem_factorSet_top`

English:
theorem mem_factorSet_top
  given: {p : Associates α} {hp : Irreducible p}
  statement: p in (⊤ : FactorSet α)
  proof: by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; exact trivial

中文:
定理 mem_factorSet_top
  条件: {p : Associates α} {hp : 不可约 p}
  结论: p in (⊤ : FactorSet α)
  证明: by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; exact trivial

Depends on / 依赖: FactorSetMem, Membership, Membership.mem, split_ifs
-/
theorem mem_factorSet_top {p : Associates α} {hp : Irreducible p} : p in (⊤ : FactorSet α) := by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; exact trivial

/--
theorem `mem_factorSet_some` / 定理 `mem_factorSet_some`

English:
theorem mem_factorSet_some
  statement: {p : Associates α} {hp : Irreducible p}
  proof: by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; rfl

中文:
定理 mem_factorSet_some
  结论: {p : Associates α} {hp : 不可约 p}
  证明: by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; rfl

Depends on / 依赖: FactorSetMem, Membership, Membership.mem, split_ifs
-/
theorem mem_factorSet_some {p : Associates α} {hp : Irreducible p}
    {l : Multiset { a : Associates α // Irreducible a }} :
    p in (l : FactorSet α) ↔ Subtype.mk p hp in l := by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; rfl

/--
theorem `reducible_notMem_factorSet` / 定理 `reducible_notMem_factorSet`

English:
theorem reducible_notMem_factorSet
  given: {p : Associates α} (hp : ¬Irreducible p) (s : FactorSet α)
  proof: fun h => by
  rwa [← factorSetMem_eq_mem, FactorSetMem, dif_neg hp] at h

中文:
定理 reducible_notMem_factorSet
  条件: {p : Associates α} (hp : ¬不可约 p) (s : FactorSet α)
  证明: fun h => by
  rwa [← factorSetMem_eq_mem, FactorSetMem, dif_neg hp] at h

Depends on / 依赖: FactorSetMem, dif_neg, factorSetMem_eq_mem
-/
theorem reducible_notMem_factorSet {p : Associates α} (hp : ¬Irreducible p) (s : FactorSet α) :
    p ∉ s := fun h => by
  rwa [← factorSetMem_eq_mem, FactorSetMem, dif_neg hp] at h

/--
theorem `irreducible_of_mem_factorSet` / 定理 `irreducible_of_mem_factorSet`

English:
theorem irreducible_of_mem_factorSet
  given: {p : Associates α} {s : FactorSet α} (h : p in s)
  proof: by_contra fun hp => reducible_notMem_factorSet hp s h

中文:
定理 irreducible_of_mem_factorSet
  条件: {p : Associates α} {s : FactorSet α} (h : p in s)
  证明: by_contra fun hp => reducible_notMem_factorSet hp s h

Depends on / 依赖: reducible_notMem_factorSet
-/
theorem irreducible_of_mem_factorSet {p : Associates α} {s : FactorSet α} (h : p in s) :
    Irreducible p :=
  by_contra fun hp => reducible_notMem_factorSet hp s h

end Mem

variable [UniqueFactorizationMonoid α]

/--
theorem `FactorSet.unique` / 定理 `FactorSet.unique`

English:
theorem FactorSet.unique
  given: [Nontrivial α] {p q : FactorSet α} (h : p.prod = q.prod)
  statement: p = q
  proof: by
  -- TODO: `induction_eliminator` doesn't work with `abbrev`
  unfold FactorSet at p q
  induction p <;> induction q
  · rfl
  · rw [eq_comm, ← FactorSet.prod_eq_zero_iff, ← h, Associates.prod_top]
  · rw [← FactorSet.prod_eq_zero_iff, h, Associates.prod_top]
  · congr 1
    rw [← Multiset.map_eq_map Subtype.coe_injective]
    apply unique' _ _ h <;>
      · intro a ha
        obtain ⟨⟨a', irred⟩, -, rfl⟩ := Multiset.mem_map.mp ha
        rwa [Subtype.coe_mk]

中文:
定理 FactorSet.unique
  条件: [非平凡 α] {p q : FactorSet α} (h : p.乘积 = q.乘积)
  结论: p = q
  证明: by
  -- TODO: `induction_eliminator` doesn't work with `abbrev`
  unfold FactorSet at p q
  induction p <;> induction q
  · rfl
  · rw [eq_comm, ← FactorSet.prod_eq_zero_iff, ← h, Associates.prod_top]
  · rw [← FactorSet.prod_eq_zero_iff, h, Associates.prod_top]
  · congr 1
    rw [← Multiset.map_eq_map Subtype.coe_injective]
    apply unique' _ _ h <;>
      · intro a ha
        obtain ⟨⟨a', irred⟩, -, rfl⟩ := Multiset.mem_map.mp ha
        rwa [Subtype.coe_mk]
-/
theorem FactorSet.unique [Nontrivial α] {p q : FactorSet α} (h : p.prod = q.prod) : p = q := by
  -- TODO: `induction_eliminator` doesn't work with `abbrev`
  unfold FactorSet at p q
  induction p <;> induction q
  · rfl
  · rw [eq_comm, ← FactorSet.prod_eq_zero_iff, ← h, Associates.prod_top]
  · rw [← FactorSet.prod_eq_zero_iff, h, Associates.prod_top]
  · congr 1
    rw [← Multiset.map_eq_map Subtype.coe_injective]
    apply unique' _ _ h <;>
      · intro a ha
        obtain ⟨⟨a', irred⟩, -, rfl⟩ := Multiset.mem_map.mp ha
        rwa [Subtype.coe_mk]

/--
Definition of `factors'` / `factors'` 的定义

English:
definition factors'
  signature: (a : α)
  body: (factors a).pmap (fun a ha => ⟨Associates.mk a, irreducible_mk.2 ha⟩) irreducible_of_factor

@[simp]

中文:
定义 factors'
  签名: (a : α)
  定义体: (factors a).pmap (fun a ha => ⟨Associates.mk a, irreducible_mk.2 ha⟩) irreducible_of_factor

@[simp]

Depends on / 依赖: Associates, Associates.mk, factors, irreducible_mk, irreducible_of_factor
-/
noncomputable def factors' (a : α) : Multiset { a : Associates α // Irreducible a } :=
  (factors a).pmap (fun a ha => ⟨Associates.mk a, irreducible_mk.2 ha⟩) irreducible_of_factor

@[simp]
/--
theorem `map_subtype_coe_factors'` / 定理 `map_subtype_coe_factors'`

English:
theorem map_subtype_coe_factors'
  given: {a : α}
  proof: by
  simp [factors', Multiset.map_pmap, Multiset.pmap_eq_map]

中文:
定理 map_subtype_coe_factors'
  条件: {a : α}
  证明: by
  simp [factors', Multiset.map_pmap, Multiset.pmap_eq_map]

Depends on / 依赖: Multiset, Multiset.map_pmap, Multiset.pmap_eq_map, factors, map_pmap, pmap_eq_map
-/
theorem map_subtype_coe_factors' {a : α} :
    (factors' a).map (↑) = (factors a).map Associates.mk := by
  simp [factors', Multiset.map_pmap, Multiset.pmap_eq_map]

/--
theorem `factors'_cong` / 定理 `factors'_cong`

English:
theorem factors'_cong
  given: {a b : α} (h : a ~ᵤ b)
  statement: factors' a = factors' b
  proof: by
  obtain rfl | hb := eq_or_ne b 0
  · rw [associated_zero_iff_eq_zero] at h
    rw [h]
  have ha : a != 0 := by
    contrapose hb with ha
    rw [← associated_zero_iff_eq_zero]; rw [← ha]
    exact h.symm
  rw [← Multiset.map_eq_map Subtype.coe_injective]; rw [map_subtype_coe_factors']; rw [map_subtype_coe_factors']; rw [← rel_associated_iff_map_eq_map]
  exact
    factors_unique irreducible_of_factor irreducible_of_factor
      ((factors_prod ha).trans <| h.trans <| (factors_prod hb).symm)

中文:
定理 factors'_cong
  条件: {a b : α} (h : a ~ᵤ b)
  结论: factors' a = factors' b
  证明: by
  obtain rfl | hb := eq_or_ne b 0
  · rw [associated_zero_iff_eq_zero] at h
    rw [h]
  have ha : a != 0 := by
    contrapose hb with ha
    rw [← associated_zero_iff_eq_zero]; rw [← ha]
    exact h.symm
  rw [← Multiset.map_eq_map Subtype.coe_injective]; rw [map_subtype_coe_factors']; rw [map_subtype_coe_factors']; rw [← rel_associated_iff_map_eq_map]
  exact
    factors_unique irreducible_of_factor irreducible_of_factor
      ((factors_prod ha).trans <| h.trans <| (factors_prod hb).symm)
-/
theorem factors'_cong {a b : α} (h : a ~ᵤ b) : factors' a = factors' b := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [associated_zero_iff_eq_zero] at h
    rw [h]
  have ha : a != 0 := by
    contrapose hb with ha
    rw [← associated_zero_iff_eq_zero]; rw [← ha]
    exact h.symm
  rw [← Multiset.map_eq_map Subtype.coe_injective]; rw [map_subtype_coe_factors']; rw [map_subtype_coe_factors']; rw [← rel_associated_iff_map_eq_map]
  exact
    factors_unique irreducible_of_factor irreducible_of_factor
      ((factors_prod ha).trans <| h.trans <| (factors_prod hb).symm)

/--
Definition of `factors` / `factors` 的定义

English:
definition factors
  signature: (a : Associates α)
  body: by
  classical refine if h : a = 0 then ⊤ else Quotient.hrecOn a (fun x _ => factors' x) ?_ h
  intro a b hab
  apply Function.hfunext
  · have : a ~ᵤ 0 ↔ b ~ᵤ 0 := Iff.intro (fun ha0 => hab.symm.trans ha0) fun hb0 => hab.trans hb0
    simp only [associated_zero_iff_eq_zero] at this
    simp only [quotient_mk_eq_mk, this, mk_eq_zero]
exact fun ha hb _ => heq_of_eq congr_arg some factors'_cong hab

@[simp]

中文:
定义 factors
  签名: (a : Associates α)
  定义体: by
  classical refine if h : a = 0 then ⊤ else Quotient.hrecOn a (fun x _ => factors' x) ?_ h
  intro a b hab
  apply Function.hfunext
  · have : a ~ᵤ 0 ↔ b ~ᵤ 0 := Iff.intro (fun ha0 => hab.symm.trans ha0) fun hb0 => hab.trans hb0
    simp only [associated_zero_iff_eq_zero] at this
    simp only [quotient_mk_eq_mk, this, mk_eq_zero]
exact fun ha hb _ => heq_of_eq congr_arg some factors'_cong hab

@[simp]

Depends on / 依赖: Function, Function.hfunext, Iff.intro, Quotient, Quotient.hrecOn, _cong, associated_zero_iff_eq_zero, classical, congr_arg, factors, hab.symm.trans, hab.trans, heq_of_eq, hfunext, hrecOn, mk_eq_zero, quotient_mk_eq_mk
-/
noncomputable def factors (a : Associates α) : FactorSet α := by
  classical refine if h : a = 0 then ⊤ else Quotient.hrecOn a (fun x _ => factors' x) ?_ h
  intro a b hab
  apply Function.hfunext
  · have : a ~ᵤ 0 ↔ b ~ᵤ 0 := Iff.intro (fun ha0 => hab.symm.trans ha0) fun hb0 => hab.trans hb0
    simp only [associated_zero_iff_eq_zero] at this
    simp only [quotient_mk_eq_mk, this, mk_eq_zero]
exact fun ha hb _ => heq_of_eq congr_arg some factors'_cong hab

@[simp]
/--
theorem `factors_zero` / 定理 `factors_zero`

English:
theorem factors_zero
  statement: (0 : Associates α).factors = ⊤
  proof: dif_pos rfl


@[simp]

中文:
定理 factors_zero
  结论: (0 : Associates α).factors = ⊤
  证明: dif_pos rfl


@[simp]

Depends on / 依赖: dif_pos
-/
theorem factors_zero : (0 : Associates α).factors = ⊤ :=
  dif_pos rfl


@[simp]
/--
theorem `factors_mk` / 定理 `factors_mk`

English:
theorem factors_mk
  given: (a : α) (h : a != 0)
  statement: (Associates.mk a).factors = factors' a
  proof: by
  apply dif_neg
  apply mt mk_eq_zero.1 h

@[simp]

中文:
定理 factors_mk
  条件: (a : α) (h : a != 0)
  结论: (Associates.mk a).factors = factors' a
  证明: by
  apply dif_neg
  apply mt mk_eq_zero.1 h

@[simp]

Depends on / 依赖: dif_neg, mk_eq_zero
-/
theorem factors_mk (a : α) (h : a != 0) : (Associates.mk a).factors = factors' a := by
  apply dif_neg
  apply mt mk_eq_zero.1 h

@[simp]
/--
theorem `factors_prod` / 定理 `factors_prod`

English:
theorem factors_prod
  given: (a : Associates α)
  statement: a.factors.prod = a
  proof: by
  rcases Associates.mk_surjective a with ⟨a, rfl⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · simp [ha, prod_mk, mk_eq_mk_iff_associated, UniqueFactorizationMonoid.factors_prod]

@[simp]

中文:
定理 factors_prod
  条件: (a : Associates α)
  结论: a.factors.乘积 = a
  证明: by
  rcases Associates.mk_surjective a with ⟨a, rfl⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · simp [ha, prod_mk, mk_eq_mk_iff_associated, UniqueFactorizationMonoid.factors_prod]

@[simp]

Depends on / 依赖: Associates, Associates.mk_surjective, UniqueFactorizationMonoid, UniqueFactorizationMonoid.factors_prod, eq_or_ne, factors_prod, mk_eq_mk_iff_associated, mk_surjective, prod_mk
-/
theorem factors_prod (a : Associates α) : a.factors.prod = a := by
  rcases Associates.mk_surjective a with ⟨a, rfl⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · simp [ha, prod_mk, mk_eq_mk_iff_associated, UniqueFactorizationMonoid.factors_prod]

@[simp]
/--
theorem `prod_factors` / 定理 `prod_factors`

English:
theorem prod_factors
  given: [Nontrivial α] (s : FactorSet α)
  statement: s.prod.factors = s
  proof: FactorSet.unique factors_prod _

@[nontriviality]

中文:
定理 prod_factors
  条件: [非平凡 α] (s : FactorSet α)
  结论: s.乘积.factors = s
  证明: FactorSet.unique factors_prod _

@[nontriviality]

Depends on / 依赖: FactorSet, FactorSet.unique, factors_prod, unique
-/
theorem prod_factors [Nontrivial α] (s : FactorSet α) : s.prod.factors = s :=
FactorSet.unique factors_prod _

@[nontriviality]
/--
theorem `factors_subsingleton` / 定理 `factors_subsingleton`

English:
theorem factors_subsingleton
  given: [Subsingleton α] {a : Associates α}
  statement: a.factors = ⊤
  proof: by
  have : Subsingleton (Associates α) := inferInstance
  convert! factors_zero

中文:
定理 factors_subsingleton
  条件: [子单例 α] {a : Associates α}
  结论: a.factors = ⊤
  证明: by
  have : Subsingleton (Associates α) := inferInstance
  convert! factors_zero

Depends on / 依赖: Associates, Subsingleton, convert, factors_zero
-/
theorem factors_subsingleton [Subsingleton α] {a : Associates α} : a.factors = ⊤ := by
  have : Subsingleton (Associates α) := inferInstance
  convert! factors_zero

/--
theorem `factors_eq_top_iff_zero` / 定理 `factors_eq_top_iff_zero`

English:
theorem factors_eq_top_iff_zero
  given: {a : Associates α}
  statement: a.factors = ⊤ ↔ a = 0
  proof: by
  nontriviality α
  exact ⟨fun h => by rwa [← factors_prod a, FactorSet.prod_eq_zero_iff], fun h => h ▸ factors_zero⟩

中文:
定理 factors_eq_top_iff_zero
  条件: {a : Associates α}
  结论: a.factors = ⊤ ↔ a = 0
  证明: by
  nontriviality α
  exact ⟨fun h => by rwa [← factors_prod a, FactorSet.prod_eq_zero_iff], fun h => h ▸ factors_zero⟩

Depends on / 依赖: FactorSet, FactorSet.prod_eq_zero_iff, factors_prod, factors_zero, nontriviality, prod_eq_zero_iff
-/
theorem factors_eq_top_iff_zero {a : Associates α} : a.factors = ⊤ ↔ a = 0 := by
  nontriviality α
  exact ⟨fun h => by rwa [← factors_prod a, FactorSet.prod_eq_zero_iff], fun h => h ▸ factors_zero⟩

/--
theorem `factors_eq_some_iff_ne_zero` / 定理 `factors_eq_some_iff_ne_zero`

English:
theorem factors_eq_some_iff_ne_zero
  given: {a : Associates α}
  proof: by
  simp_rw [@eq_comm _ a.factors, ← WithTop.ne_top_iff_exists]
  exact factors_eq_top_iff_zero.not

中文:
定理 factors_eq_some_iff_ne_zero
  条件: {a : Associates α}
  证明: by
  simp_rw [@eq_comm _ a.factors, ← WithTop.ne_top_iff_exists]
  exact factors_eq_top_iff_zero.not

Depends on / 依赖: WithTop, WithTop.ne_top_iff_exists, a.factors, eq_comm, factors, factors_eq_top_iff_zero, factors_eq_top_iff_zero.not, ne_top_iff_exists, simp_rw
-/
theorem factors_eq_some_iff_ne_zero {a : Associates α} :
    (exists s : Multiset { p : Associates α // Irreducible p }, a.factors = s) ↔ a != 0 := by
  simp_rw [@eq_comm _ a.factors, ← WithTop.ne_top_iff_exists]
  exact factors_eq_top_iff_zero.not

/--
theorem `eq_of_factors_eq_factors` / 定理 `eq_of_factors_eq_factors`

English:
theorem eq_of_factors_eq_factors
  given: {a b : Associates α} (h : a.factors = b.factors)
  statement: a = b
  proof: by
  have : a.factors.prod = b.factors.prod := by rw [h]
  rwa [factors_prod, factors_prod] at this

@[simp]

中文:
定理 eq_of_factors_eq_factors
  条件: {a b : Associates α} (h : a.factors = b.factors)
  结论: a = b
  证明: by
  have : a.factors.prod = b.factors.prod := by rw [h]
  rwa [factors_prod, factors_prod] at this

@[simp]

Depends on / 依赖: a.factors.prod, b.factors.prod, factors, factors_prod
-/
theorem eq_of_factors_eq_factors {a b : Associates α} (h : a.factors = b.factors) : a = b := by
  have : a.factors.prod = b.factors.prod := by rw [h]
  rwa [factors_prod, factors_prod] at this

@[simp]
/--
theorem `factors_mul` / 定理 `factors_mul`

English:
theorem factors_mul
  given: (a b : Associates α)
  statement: (a * b).factors = a.factors + b.factors
  proof: by
  nontriviality α
refine FactorSet.unique eq_of_factors_eq_factors ?_
  rw [prod_add]; rw [factors_prod]; rw [factors_prod]; rw [factors_prod]

@[gcongr]

中文:
定理 factors_mul
  条件: (a b : Associates α)
  结论: (a * b).factors = a.factors + b.factors
  证明: by
  nontriviality α
refine FactorSet.unique eq_of_factors_eq_factors ?_
  rw [prod_add]; rw [factors_prod]; rw [factors_prod]; rw [factors_prod]

@[gcongr]

Depends on / 依赖: FactorSet, FactorSet.unique, eq_of_factors_eq_factors, factors_prod, nontriviality, prod_add, unique
-/
theorem factors_mul (a b : Associates α) : (a * b).factors = a.factors + b.factors := by
  nontriviality α
refine FactorSet.unique eq_of_factors_eq_factors ?_
  rw [prod_add]; rw [factors_prod]; rw [factors_prod]; rw [factors_prod]

@[gcongr]
/--
theorem `factors_mono` / 定理 `factors_mono`

English:
theorem factors_mono
  statement: forall {a b : Associates α}, a <= b -> a.factors <= b.factors

中文:
定理 factors_mono
  结论: 对任意 {a b : Associates α}, a <= b -> a.factors <= b.factors
-/
theorem factors_mono : forall {a b : Associates α}, a <= b -> a.factors <= b.factors
  | s, t, ⟨d, eq⟩ => by rw [eq, factors_mul]; exact le_add_of_nonneg_right bot_le

@[simp]
/--
theorem `factors_le` / 定理 `factors_le`

English:
theorem factors_le
  given: {a b : Associates α}
  statement: a.factors <= b.factors ↔ a <= b
  proof: by
  refine ⟨fun h => ?_, factors_mono⟩
  have : a.factors.prod <= b.factors.prod := prod_mono h
  rwa [factors_prod, factors_prod] at this

中文:
定理 factors_le
  条件: {a b : Associates α}
  结论: a.factors <= b.factors ↔ a <= b
  证明: by
  refine ⟨fun h => ?_, factors_mono⟩
  have : a.factors.prod <= b.factors.prod := prod_mono h
  rwa [factors_prod, factors_prod] at this

Depends on / 依赖: a.factors.prod, b.factors.prod, factors, factors_mono, factors_prod, prod_mono
-/
theorem factors_le {a b : Associates α} : a.factors <= b.factors ↔ a <= b := by
  refine ⟨fun h => ?_, factors_mono⟩
  have : a.factors.prod <= b.factors.prod := prod_mono h
  rwa [factors_prod, factors_prod] at this

section count

variable [DecidableEq (Associates α)] [forall p : Associates α, Decidable (Irreducible p)]

/--
theorem `eq_factors_of_eq_counts` / 定理 `eq_factors_of_eq_counts`

English:
theorem eq_factors_of_eq_counts
  statement: {a b : Associates α} (ha : a != 0) (hb : b != 0)
  proof: by
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  simp_all only [count_some, WithTop.coe_eq_coe]
  ext
  grind

中文:
定理 eq_factors_of_eq_counts
  结论: {a b : Associates α} (ha : a != 0) (hb : b != 0)
  证明: by
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  simp_all only [count_some, WithTop.coe_eq_coe]
  ext
  grind

Depends on / 依赖: WithTop, WithTop.coe_eq_coe, coe_eq_coe, count_some, factors_eq_some_iff_ne_zero, factors_eq_some_iff_ne_zero.mpr, h_sa, h_sb
-/
theorem eq_factors_of_eq_counts {a b : Associates α} (ha : a != 0) (hb : b != 0)
    (h : forall p : Associates α, Irreducible p -> p.count a.factors = p.count b.factors) :
    a.factors = b.factors := by
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  simp_all only [count_some, WithTop.coe_eq_coe]
  ext
  grind

/--
theorem `eq_of_eq_counts` / 定理 `eq_of_eq_counts`

English:
theorem eq_of_eq_counts
  statement: {a b : Associates α} (ha : a != 0) (hb : b != 0)
  proof: eq_of_factors_eq_factors (eq_factors_of_eq_counts ha hb h)

中文:
定理 eq_of_eq_counts
  结论: {a b : Associates α} (ha : a != 0) (hb : b != 0)
  证明: eq_of_factors_eq_factors (eq_factors_of_eq_counts ha hb h)

Depends on / 依赖: eq_factors_of_eq_counts, eq_of_factors_eq_factors
-/
theorem eq_of_eq_counts {a b : Associates α} (ha : a != 0) (hb : b != 0)
    (h : forall p : Associates α, Irreducible p -> p.count a.factors = p.count b.factors) : a = b :=
  eq_of_factors_eq_factors (eq_factors_of_eq_counts ha hb h)

/--
theorem `count_le_count_of_factors_le` / 定理 `count_le_count_of_factors_le`

English:
theorem count_le_count_of_factors_le
  statement: {a b p : Associates α} (hb : b != 0) (hp : Irreducible p)
  proof: by
  by_cases ha : a = 0
  · simp_all
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  rw [h_sa]; rw [h_sb] at h ⊢
  rw [count_some hp]; rw [count_some hp]; rw [WithTop.coe_le_coe] at h
  exact Multiset.count_le_of_le _ h

中文:
定理 count_le_count_of_factors_le
  结论: {a b p : Associates α} (hb : b != 0) (hp : 不可约 p)
  证明: by
  by_cases ha : a = 0
  · simp_all
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  rw [h_sa]; rw [h_sb] at h ⊢
  rw [count_some hp]; rw [count_some hp]; rw [WithTop.coe_le_coe] at h
  exact Multiset.count_le_of_le _ h

Depends on / 依赖: Multiset, Multiset.count_le_of_le, WithTop, WithTop.coe_le_coe, coe_le_coe, count_le_of_le, count_some, factors_eq_some_iff_ne_zero, factors_eq_some_iff_ne_zero.mpr, h_sa, h_sb
-/
theorem count_le_count_of_factors_le {a b p : Associates α} (hb : b != 0) (hp : Irreducible p)
    (h : a.factors <= b.factors) : p.count a.factors <= p.count b.factors := by
  by_cases ha : a = 0
  · simp_all
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  rw [h_sa]; rw [h_sb] at h ⊢
  rw [count_some hp]; rw [count_some hp]; rw [WithTop.coe_le_coe] at h
  exact Multiset.count_le_of_le _ h

/--
theorem `count_le_count_of_le` / 定理 `count_le_count_of_le`

English:
theorem count_le_count_of_le
  given: {a b p : Associates α} (hb : b != 0) (hp : Irreducible p) (h : a <= b)
  proof: count_le_count_of_factors_le hb hp factors_mono h

中文:
定理 count_le_count_of_le
  条件: {a b p : Associates α} (hb : b != 0) (hp : 不可约 p) (h : a <= b)
  证明: count_le_count_of_factors_le hb hp factors_mono h

Depends on / 依赖: count_le_count_of_factors_le, factors_mono
-/
theorem count_le_count_of_le {a b p : Associates α} (hb : b != 0) (hp : Irreducible p) (h : a <= b) :
    p.count a.factors <= p.count b.factors :=
count_le_count_of_factors_le hb hp factors_mono h

end count

/--
theorem `prod_le` / 定理 `prod_le`

English:
theorem prod_le
  given: [Nontrivial α] {a b : FactorSet α}
  statement: a.prod <= b.prod ↔ a <= b
  proof: by
  refine ⟨fun h => ?_, prod_mono⟩
  have : a.prod.factors <= b.prod.factors := factors_mono h
  rwa [prod_factors, prod_factors] at this

中文:
定理 prod_le
  条件: [非平凡 α] {a b : FactorSet α}
  结论: a.乘积 <= b.乘积 ↔ a <= b
  证明: by
  refine ⟨fun h => ?_, prod_mono⟩
  have : a.prod.factors <= b.prod.factors := factors_mono h
  rwa [prod_factors, prod_factors] at this

Depends on / 依赖: a.prod.factors, b.prod.factors, factors, factors_mono, prod_factors, prod_mono
-/
theorem prod_le [Nontrivial α] {a b : FactorSet α} : a.prod <= b.prod ↔ a <= b := by
  refine ⟨fun h => ?_, prod_mono⟩
  have : a.prod.factors <= b.prod.factors := factors_mono h
  rwa [prod_factors, prod_factors] at this

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (Associates α)
  body: ⟨fun a b => (a.factors ⊔ b.factors).prod⟩

中文:
实例 :
  签名: 最大值 (Associates α)
  定义体: ⟨fun a b => (a.factors ⊔ b.factors).prod⟩

Depends on / 依赖: a.factors, b.factors, factors
-/
noncomputable instance : Max (Associates α) :=
  ⟨fun a b => (a.factors ⊔ b.factors).prod⟩

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Associates α)
  body: ⟨fun a b => (a.factors ⊓ b.factors).prod⟩

中文:
实例 :
  签名: 最小值 (Associates α)
  定义体: ⟨fun a b => (a.factors ⊓ b.factors).prod⟩

Depends on / 依赖: a.factors, b.factors, factors
-/
noncomputable instance : Min (Associates α) :=
  ⟨fun a b => (a.factors ⊓ b.factors).prod⟩

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (Associates α)
  body: { Associates.instPartialOrder with
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    sup_le := fun _ _ c hac hbc =>
      factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc))
le_sup_left := fun a _ => le_trans (le_of_eq (factors_prod a).symm) prod_mono le_sup_left
    le_sup_right := fun _ b =>
le_trans (le_of_eq (factors_prod b).symm) prod_mono le_sup_right
    le_inf := fun a _ _ hac hbc =>
      factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc))
    inf_le_left := fun a _ => le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a))
    inf_le_right := fun _ b => le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)) }

中文:
实例 :
  签名: 格 (Associates α)
  定义体: { Associates.instPartialOrder with
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    sup_le := fun _ _ c hac hbc =>
      factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc))
le_sup_left := fun a _ => le_trans (le_of_eq (factors_prod a).symm) prod_mono le_sup_left
    le_sup_right := fun _ b =>
le_trans (le_of_eq (factors_prod b).symm) prod_mono le_sup_right
    le_inf := fun a _ _ hac hbc =>
      factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc))
    inf_le_left := fun a _ => le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a))
    inf_le_right := fun _ b => le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)) }

Depends on / 依赖: Associates, Associates.instPartialOrder, factors_mono, factors_prod, inf_le_left, instPartialOrder, le_inf, le_of_eq, le_sup_left, le_sup_right, le_trans, prod_mo, prod_mono, sup_le
-/
noncomputable instance : Lattice (Associates α) :=
  { Associates.instPartialOrder with
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    sup_le := fun _ _ c hac hbc =>
      factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc))
le_sup_left := fun a _ => le_trans (le_of_eq (factors_prod a).symm) prod_mono le_sup_left
    le_sup_right := fun _ b =>
le_trans (le_of_eq (factors_prod b).symm) prod_mono le_sup_right
    le_inf := fun a _ _ hac hbc =>
      factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc))
    inf_le_left := fun a _ => le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a))
    inf_le_right := fun _ b => le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)) }

open scoped Classical in
/--
theorem `sup_mul_inf` / 定理 `sup_mul_inf`

English:
theorem sup_mul_inf
  given: (a b : Associates α)
  statement: (a ⊔ b) * (a ⊓ b) = a * b
  proof: show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b by
    nontriviality α
    refine eq_of_factors_eq_factors ?_
    rw [← prod_add]; rw [prod_factors]; rw [factors_mul]; rw [FactorSet.sup_add_inf_eq_add]

中文:
定理 sup_mul_inf
  条件: (a b : Associates α)
  结论: (a ⊔ b) * (a ⊓ b) = a * b
  证明: show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b by
    nontriviality α
    refine eq_of_factors_eq_factors ?_
    rw [← prod_add]; rw [prod_factors]; rw [factors_mul]; rw [FactorSet.sup_add_inf_eq_add]

Depends on / 依赖: BoundedContinuousMapClass, FactorSet, FactorSet.sup_add_inf_eq_add, a.factors, b.factors, eq_of_factors_eq_factors, factors, factors_mul, instBoundedContinuousMapClass, nontriviality, prod_add, prod_factors, sup_add_inf_eq_add
-/
theorem sup_mul_inf (a b : Associates α) : (a ⊔ b) * (a ⊓ b) = a * b :=
  show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b by
    nontriviality α
    refine eq_of_factors_eq_factors ?_
    rw [← prod_add]; rw [prod_factors]; rw [factors_mul]; rw [FactorSet.sup_add_inf_eq_add]

/--
theorem `dvd_of_mem_factors` / 定理 `dvd_of_mem_factors`

English:
theorem dvd_of_mem_factors
  given: {a p : Associates α} (hm : p in factors a)
  proof: by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact dvd_zero p
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0
  rw [← Associates.factors_prod a]
  rw [← ha']; rw [factors_mk a0 nza] at hm ⊢
  rw [prod_coe]
  apply Multiset.dvd_prod; apply Multiset.mem_map.mpr
  exact ⟨⟨p, irreducible_of_mem_factorSet hm⟩, mem_factorSet_some.mp hm, rfl⟩

中文:
定理 dvd_of_mem_factors
  条件: {a p : Associates α} (hm : p in factors a)
  证明: by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact dvd_zero p
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0
  rw [← Associates.factors_prod a]
  rw [← ha']; rw [factors_mk a0 nza] at hm ⊢
  rw [prod_coe]
  apply Multiset.dvd_prod; apply Multiset.mem_map.mpr
  exact ⟨⟨p, irreducible_of_mem_factorSet hm⟩, mem_factorSet_some.mp hm, rfl⟩

Depends on / 依赖: Associates, Associates.factors_prod, Multiset, Multiset.dvd_prod, Multiset.mem_map.mpr, dvd_prod, dvd_zero, eq_or_ne, exists_non_zero_rep, factors_mk, factors_prod, irreducible_of_mem_factorSet, mem_factorSet_some, mem_factorSet_some.mp, mem_map, prod_coe
-/
theorem dvd_of_mem_factors {a p : Associates α} (hm : p in factors a) :
    p ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact dvd_zero p
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0
  rw [← Associates.factors_prod a]
  rw [← ha']; rw [factors_mk a0 nza] at hm ⊢
  rw [prod_coe]
  apply Multiset.dvd_prod; apply Multiset.mem_map.mpr
  exact ⟨⟨p, irreducible_of_mem_factorSet hm⟩, mem_factorSet_some.mp hm, rfl⟩

/--
theorem `dvd_of_mem_factors'` / 定理 `dvd_of_mem_factors'`

English:
theorem dvd_of_mem_factors'
  statement: {a : α} {p : Associates α} {hp : Irreducible p} {hz : a != 0}
  proof: by
  have := Classical.decEq (Associates α)
  apply dvd_of_mem_factors
  rw [factors_mk _ hz]
  apply mem_factorSet_some.2 h_mem

中文:
定理 dvd_of_mem_factors'
  结论: {a : α} {p : Associates α} {hp : 不可约 p} {hz : a != 0}
  证明: by
  have := Classical.decEq (Associates α)
  apply dvd_of_mem_factors
  rw [factors_mk _ hz]
  apply mem_factorSet_some.2 h_mem

Depends on / 依赖: Associates, Classical, Classical.decEq, dvd_of_mem_factors, factors_mk, h_mem, mem_factorSet_some
-/
theorem dvd_of_mem_factors' {a : α} {p : Associates α} {hp : Irreducible p} {hz : a != 0}
    (h_mem : Subtype.mk p hp in factors' a) : p ∣ Associates.mk a := by
  have := Classical.decEq (Associates α)
  apply dvd_of_mem_factors
  rw [factors_mk _ hz]
  apply mem_factorSet_some.2 h_mem

/--
theorem `mem_factors'_of_dvd` / 定理 `mem_factors'_of_dvd`

English:
theorem mem_factors'_of_dvd
  given: {a p : α} (ha0 : a != 0) (hp : Irreducible p) (hd : p ∣ a)
  proof: by
  obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd
  apply Multiset.mem_pmap.mpr; use q; use hq
  exact Subtype.ext (Eq.symm (mk_eq_mk_iff_associated.mpr hpq))

中文:
定理 mem_factors'_of_dvd
  条件: {a p : α} (ha0 : a != 0) (hp : 不可约 p) (hd : p ∣ a)
  证明: by
  obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd
  apply Multiset.mem_pmap.mpr; use q; use hq
  exact Subtype.ext (Eq.symm (mk_eq_mk_iff_associated.mpr hpq))

Depends on / 依赖: Eq.symm, Multiset, Multiset.mem_pmap.mpr, Subtype, Subtype.ext, exists_mem_factors_of_dvd, mem_pmap, mk_eq_mk_iff_associated, mk_eq_mk_iff_associated.mpr
-/
theorem mem_factors'_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) (hd : p ∣ a) :
    Subtype.mk (Associates.mk p) (irreducible_mk.2 hp) in factors' a := by
  obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd
  apply Multiset.mem_pmap.mpr; use q; use hq
  exact Subtype.ext (Eq.symm (mk_eq_mk_iff_associated.mpr hpq))

/--
theorem `mem_factors'_iff_dvd` / 定理 `mem_factors'_iff_dvd`

English:
theorem mem_factors'_iff_dvd
  given: {a p : α} (ha0 : a != 0) (hp : Irreducible p)
  proof: by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors'
    apply ha0
  · apply mem_factors'_of_dvd ha0 hp

中文:
定理 mem_factors'_iff_dvd
  条件: {a p : α} (ha0 : a != 0) (hp : 不可约 p)
  证明: by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors'
    apply ha0
  · apply mem_factors'_of_dvd ha0 hp
-/
theorem mem_factors'_iff_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) :
    Subtype.mk (Associates.mk p) (irreducible_mk.2 hp) in factors' a ↔ p ∣ a := by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors'
    apply ha0
  · apply mem_factors'_of_dvd ha0 hp

/--
theorem `mem_factors_of_dvd` / 定理 `mem_factors_of_dvd`

English:
theorem mem_factors_of_dvd
  given: {a p : α} (ha0 : a != 0) (hp : Irreducible p) (hd : p ∣ a)
  proof: by
  rw [factors_mk _ ha0]
  exact mem_factorSet_some.mpr (mem_factors'_of_dvd ha0 hp hd)

中文:
定理 mem_factors_of_dvd
  条件: {a p : α} (ha0 : a != 0) (hp : 不可约 p) (hd : p ∣ a)
  证明: by
  rw [factors_mk _ ha0]
  exact mem_factorSet_some.mpr (mem_factors'_of_dvd ha0 hp hd)

Depends on / 依赖: _of_dvd, factors_mk, mem_factorSet_some, mem_factorSet_some.mpr, mem_factors
-/
theorem mem_factors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) (hd : p ∣ a) :
    Associates.mk p in factors (Associates.mk a) := by
  rw [factors_mk _ ha0]
  exact mem_factorSet_some.mpr (mem_factors'_of_dvd ha0 hp hd)

/--
theorem `mem_factors_iff_dvd` / 定理 `mem_factors_iff_dvd`

English:
theorem mem_factors_iff_dvd
  given: {a p : α} (ha0 : a != 0) (hp : Irreducible p)
  proof: by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors
  · apply mem_factors_of_dvd ha0 hp

中文:
定理 mem_factors_iff_dvd
  条件: {a p : α} (ha0 : a != 0) (hp : 不可约 p)
  证明: by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors
  · apply mem_factors_of_dvd ha0 hp

Depends on / 依赖: dvd_of_mem_factors, mem_factors_of_dvd, mk_dvd_mk
-/
theorem mem_factors_iff_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) :
    Associates.mk p in factors (Associates.mk a) ↔ p ∣ a := by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors
  · apply mem_factors_of_dvd ha0 hp

/--
theorem `exists_prime_dvd_of_not_inf_one` / 定理 `exists_prime_dvd_of_not_inf_one`

English:
theorem exists_prime_dvd_of_not_inf_one
  statement: {a b : α} (ha : a != 0) (hb : b != 0)
  proof: by
  classical
  have hz : factors (Associates.mk a) ⊓ factors (Associates.mk b) != 0 := by
    contrapose h with hf
    change (factors (Associates.mk a) ⊓ factors (Associates.mk b)).prod = 1
    rw [hf]
    exact Multiset.prod_zero
  rw [factors_mk a ha]; rw [factors_mk b hb]; rw [← WithTop.coe_inf] at hz
  obtain ⟨⟨p0, p0_irr⟩, p0_mem⟩ := Multiset.exists_mem_of_ne_zero ((mt WithTop.coe_eq_coe.mpr) hz)
  rw [Multiset.inf_eq_inter] at p0_mem
  obtain ⟨p, rfl⟩ : exists p, Associates.mk p = p0 := Quot.exists_rep p0
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← UniqueFactorizationMonoid.irreducible_iff_prime, ← irreducible_mk]
    exact p0_irr
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (Multiset.mem_inter.mp p0_mem).left
    apply ha
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (Multiset.mem_inter.mp p0_mem).right
    apply hb

中文:
定理 存在_prime_dvd_of_not_inf_one
  结论: {a b : α} (ha : a != 0) (hb : b != 0)
  证明: by
  classical
  have hz : factors (Associates.mk a) ⊓ factors (Associates.mk b) != 0 := by
    contrapose h with hf
    change (factors (Associates.mk a) ⊓ factors (Associates.mk b)).prod = 1
    rw [hf]
    exact Multiset.prod_zero
  rw [factors_mk a ha]; rw [factors_mk b hb]; rw [← WithTop.coe_inf] at hz
  obtain ⟨⟨p0, p0_irr⟩, p0_mem⟩ := Multiset.exists_mem_of_ne_zero ((mt WithTop.coe_eq_coe.mpr) hz)
  rw [Multiset.inf_eq_inter] at p0_mem
  obtain ⟨p, rfl⟩ : exists p, Associates.mk p = p0 := Quot.exists_rep p0
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← UniqueFactorizationMonoid.irreducible_iff_prime, ← irreducible_mk]
    exact p0_irr
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (Multiset.mem_inter.mp p0_mem).left
    apply ha
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (Multiset.mem_inter.mp p0_mem).right
    apply hb

Depends on / 依赖: Associates, Associates.mk, Multiset, Multiset.exists_mem_of_ne_zero, Multiset.inf_eq_inter, Multiset.prod_zero, Quot.exists_rep, WithTop, WithTop.coe_eq_coe.mpr, WithTop.coe_inf, classical, coe_eq_coe, coe_inf, contrapose, exists_mem_of_ne_zero, exists_rep, factors, factors_mk, inf_eq_inter, p0_irr
-/
theorem exists_prime_dvd_of_not_inf_one {a b : α} (ha : a != 0) (hb : b != 0)
    (h : Associates.mk a ⊓ Associates.mk b != 1) : exists p : α, Prime p ∧ p ∣ a ∧ p ∣ b := by
  classical
  have hz : factors (Associates.mk a) ⊓ factors (Associates.mk b) != 0 := by
    contrapose h with hf
    change (factors (Associates.mk a) ⊓ factors (Associates.mk b)).prod = 1
    rw [hf]
    exact Multiset.prod_zero
  rw [factors_mk a ha]; rw [factors_mk b hb]; rw [← WithTop.coe_inf] at hz
  obtain ⟨⟨p0, p0_irr⟩, p0_mem⟩ := Multiset.exists_mem_of_ne_zero ((mt WithTop.coe_eq_coe.mpr) hz)
  rw [Multiset.inf_eq_inter] at p0_mem
  obtain ⟨p, rfl⟩ : exists p, Associates.mk p = p0 := Quot.exists_rep p0
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← UniqueFactorizationMonoid.irreducible_iff_prime, ← irreducible_mk]
    exact p0_irr
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (Multiset.mem_inter.mp p0_mem).left
    apply ha
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (Multiset.mem_inter.mp p0_mem).right
    apply hb

/--
theorem `coprime_iff_inf_one` / 定理 `coprime_iff_inf_one`

English:
theorem coprime_iff_inf_one
  given: {a b : α} (ha0 : a != 0) (hb0 : b != 0)
  proof: by
  constructor
  · intro hg p ha hb hp
    refine (Associates.prime_mk.mpr hp).not_isUnit (isUnit_of_dvd_one ?_)
    rw [← hg]
    exact le_inf (mk_le_mk_of_dvd ha) (mk_le_mk_of_dvd hb)
  · contrapose
    intro hg hc
    obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_not_inf_one ha0 hb0 hg
    exact hc hpa hpb hp

中文:
定理 coprime_iff_inf_one
  条件: {a b : α} (ha0 : a != 0) (hb0 : b != 0)
  证明: by
  constructor
  · intro hg p ha hb hp
    refine (Associates.prime_mk.mpr hp).not_isUnit (isUnit_of_dvd_one ?_)
    rw [← hg]
    exact le_inf (mk_le_mk_of_dvd ha) (mk_le_mk_of_dvd hb)
  · contrapose
    intro hg hc
    obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_not_inf_one ha0 hb0 hg
    exact hc hpa hpb hp

Depends on / 依赖: Associates, Associates.prime_mk.mpr, contrapose, exists_prime_dvd_of_not_inf_one, isUnit_of_dvd_one, le_inf, mk_le_mk_of_dvd, not_isUnit, prime_mk
-/
theorem coprime_iff_inf_one {a b : α} (ha0 : a != 0) (hb0 : b != 0) :
    Associates.mk a ⊓ Associates.mk b = 1 ↔ forall {d : α}, d ∣ a -> d ∣ b -> ¬Prime d := by
  constructor
  · intro hg p ha hb hp
    refine (Associates.prime_mk.mpr hp).not_isUnit (isUnit_of_dvd_one ?_)
    rw [← hg]
    exact le_inf (mk_le_mk_of_dvd ha) (mk_le_mk_of_dvd hb)
  · contrapose
    intro hg hc
    obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_not_inf_one ha0 hb0 hg
    exact hc hpa hpb hp

/--
theorem `factors_self` / 定理 `factors_self`

English:
theorem factors_self
  given: [Nontrivial α] {p : Associates α} (hp : Irreducible p)
  proof: FactorSet.unique
    (by rw [factors_prod, FactorSet.prod.eq_def]; dsimp; rw [prod_singleton])

中文:
定理 factors_self
  条件: [非平凡 α] {p : Associates α} (hp : 不可约 p)
  证明: FactorSet.unique
    (by rw [factors_prod, FactorSet.prod.eq_def]; dsimp; rw [prod_singleton])

Depends on / 依赖: FactorSet, FactorSet.prod.eq_def, FactorSet.unique, eq_def, factors_prod, prod_singleton, unique
-/
theorem factors_self [Nontrivial α] {p : Associates α} (hp : Irreducible p) :
    p.factors = WithTop.some {⟨p, hp⟩} :=
  FactorSet.unique
    (by rw [factors_prod, FactorSet.prod.eq_def]; dsimp; rw [prod_singleton])

/--
theorem `factors_prime_pow` / 定理 `factors_prime_pow`

English:
theorem factors_prime_pow
  given: [Nontrivial α] {p : Associates α} (hp : Irreducible p) (k : Nat)
  proof: FactorSet.unique
    (by
      rw [Associates.factors_prod]; rw [FactorSet.prod.eq_def]
      dsimp; rw [Multiset.map_replicate, Multiset.prod_replicate, Subtype.coe_mk])

中文:
定理 factors_prime_pow
  条件: [非平凡 α] {p : Associates α} (hp : 不可约 p) (k : 自然数)
  证明: FactorSet.unique
    (by
      rw [Associates.factors_prod]; rw [FactorSet.prod.eq_def]
      dsimp; rw [Multiset.map_replicate, Multiset.prod_replicate, Subtype.coe_mk])

Depends on / 依赖: Associates, Associates.factors_prod, FactorSet, FactorSet.prod.eq_def, FactorSet.unique, Multiset, Multiset.map_replicate, Multiset.prod_replicate, Subtype, Subtype.coe_mk, coe_mk, eq_def, factors_prod, map_replicate, prod_replicate, unique
-/
theorem factors_prime_pow [Nontrivial α] {p : Associates α} (hp : Irreducible p) (k : Nat) :
    factors (p ^ k) = WithTop.some (Multiset.replicate k ⟨p, hp⟩) :=
  FactorSet.unique
    (by
      rw [Associates.factors_prod]; rw [FactorSet.prod.eq_def]
      dsimp; rw [Multiset.map_replicate, Multiset.prod_replicate, Subtype.coe_mk])

/--
theorem `prime_pow_le_iff_le_bcount` / 定理 `prime_pow_le_iff_le_bcount`

English:
theorem prime_pow_le_iff_le_bcount
  statement: [DecidableEq (Associates α)] {m p : Associates α}
  proof: by
  rcases Associates.exists_non_zero_rep h₁ with ⟨m, hm, rfl⟩
  have := nontrivial_of_ne _ _ hm
  rw [bcount.eq_def]; rw [factors_mk]; rw [Multiset.le_count_iff_replicate_le]; rw [← factors_le]; rw [factors_prime_pow]; rw [factors_mk]; rw [WithTop.coe_le_coe] <;> assumption

@[simp]

中文:
定理 prime_pow_le_iff_le_bcount
  结论: [DecidableEq (Associates α)] {m p : Associates α}
  证明: by
  rcases Associates.exists_non_zero_rep h₁ with ⟨m, hm, rfl⟩
  have := nontrivial_of_ne _ _ hm
  rw [bcount.eq_def]; rw [factors_mk]; rw [Multiset.le_count_iff_replicate_le]; rw [← factors_le]; rw [factors_prime_pow]; rw [factors_mk]; rw [WithTop.coe_le_coe] <;> assumption

@[simp]

Depends on / 依赖: Associates, Associates.exists_non_zero_rep, Multiset, Multiset.le_count_iff_replicate_le, WithTop, WithTop.coe_le_coe, bcount, bcount.eq_def, coe_le_coe, eq_def, exists_non_zero_rep, factors_le, factors_mk, factors_prime_pow, le_count_iff_replicate_le, nontrivial_of_ne
-/
theorem prime_pow_le_iff_le_bcount [DecidableEq (Associates α)] {m p : Associates α}
    (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat} : p ^ k <= m ↔ k <= bcount ⟨p, h₂⟩ m.factors := by
  rcases Associates.exists_non_zero_rep h₁ with ⟨m, hm, rfl⟩
  have := nontrivial_of_ne _ _ hm
  rw [bcount.eq_def]; rw [factors_mk]; rw [Multiset.le_count_iff_replicate_le]; rw [← factors_le]; rw [factors_prime_pow]; rw [factors_mk]; rw [WithTop.coe_le_coe] <;> assumption

@[simp]
/--
theorem `factors_one` / 定理 `factors_one`

English:
theorem factors_one
  given: [Nontrivial α]
  statement: factors (1 : Associates α) = 0
  proof: by
  apply FactorSet.unique
  rw [Associates.factors_prod]
  exact Multiset.prod_zero

@[simp]

中文:
定理 factors_one
  条件: [非平凡 α]
  结论: factors (1 : Associates α) = 0
  证明: by
  apply FactorSet.unique
  rw [Associates.factors_prod]
  exact Multiset.prod_zero

@[simp]

Depends on / 依赖: Associates, Associates.factors_prod, FactorSet, FactorSet.unique, Multiset, Multiset.prod_zero, factors_prod, prod_zero, unique
-/
theorem factors_one [Nontrivial α] : factors (1 : Associates α) = 0 := by
  apply FactorSet.unique
  rw [Associates.factors_prod]
  exact Multiset.prod_zero

@[simp]
/--
theorem `pow_factors` / 定理 `pow_factors`

English:
theorem pow_factors
  given: [Nontrivial α] {a : Associates α} {k : Nat}
  proof: by
  induction k with
  | zero => rw [zero_nsmul, pow_zero]; exact factors_one
  | succ n h => rw [pow_succ, succ_nsmul, factors_mul, h]

中文:
定理 pow_factors
  条件: [非平凡 α] {a : Associates α} {k : 自然数}
  证明: by
  induction k with
  | zero => rw [zero_nsmul, pow_zero]; exact factors_one
  | succ n h => rw [pow_succ, succ_nsmul, factors_mul, h]

Depends on / 依赖: factors_mul, factors_one, pow_succ, pow_zero, succ_nsmul, zero_nsmul
-/
theorem pow_factors [Nontrivial α] {a : Associates α} {k : Nat} :
    (a ^ k).factors = k • a.factors := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero]; exact factors_one
  | succ n h => rw [pow_succ, succ_nsmul, factors_mul, h]

section count

variable [DecidableEq (Associates α)] [forall p : Associates α, Decidable (Irreducible p)]

/--
theorem `prime_pow_dvd_iff_le` / 定理 `prime_pow_dvd_iff_le`

English:
theorem prime_pow_dvd_iff_le
  given: {m p : Associates α} (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat}
  proof: by
  rw [count]; rw [dif_pos h₂]; rw [prime_pow_le_iff_le_bcount h₁]

中文:
定理 prime_pow_dvd_iff_le
  条件: {m p : Associates α} (h₁ : m != 0) (h₂ : 不可约 p) {k : 自然数}
  证明: by
  rw [count]; rw [dif_pos h₂]; rw [prime_pow_le_iff_le_bcount h₁]

Depends on / 依赖: dif_pos, prime_pow_le_iff_le_bcount
-/
theorem prime_pow_dvd_iff_le {m p : Associates α} (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat} :
    p ^ k <= m ↔ k <= count p m.factors := by
  rw [count]; rw [dif_pos h₂]; rw [prime_pow_le_iff_le_bcount h₁]

/--
theorem `le_of_count_ne_zero` / 定理 `le_of_count_ne_zero`

English:
theorem le_of_count_ne_zero
  given: {m p : Associates α} (h0 : m != 0) (hp : Irreducible p)
  proof: by
  rw [← pos_iff_ne_zero]
  intro h
  rw [← pow_one p]
  apply (prime_pow_dvd_iff_le h0 hp).2
  simpa only

中文:
定理 le_of_count_ne_zero
  条件: {m p : Associates α} (h0 : m != 0) (hp : 不可约 p)
  证明: by
  rw [← pos_iff_ne_zero]
  intro h
  rw [← pow_one p]
  apply (prime_pow_dvd_iff_le h0 hp).2
  simpa only

Depends on / 依赖: pos_iff_ne_zero, pow_one, prime_pow_dvd_iff_le
-/
theorem le_of_count_ne_zero {m p : Associates α} (h0 : m != 0) (hp : Irreducible p) :
    count p m.factors != 0 -> p <= m := by
  rw [← pos_iff_ne_zero]
  intro h
  rw [← pow_one p]
  apply (prime_pow_dvd_iff_le h0 hp).2
  simpa only

/--
theorem `count_ne_zero_iff_dvd` / 定理 `count_ne_zero_iff_dvd`

English:
theorem count_ne_zero_iff_dvd
  given: {a p : α} (ha0 : a != 0) (hp : Irreducible p)
  proof: by
  rw [← Associates.mk_le_mk_iff_dvd]
  refine
    ⟨fun h =>
      Associates.le_of_count_ne_zero (Associates.mk_ne_zero.mpr ha0)
        (Associates.irreducible_mk.mpr hp) h,
      fun h => ?_⟩
  rw [← pow_one (Associates.mk p)]; rw [Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr ha0)
      (Associates.irreducible_mk.mpr hp)] at h
  exact (zero_lt_one.trans_le h).ne'

中文:
定理 count_ne_zero_iff_dvd
  条件: {a p : α} (ha0 : a != 0) (hp : 不可约 p)
  证明: by
  rw [← Associates.mk_le_mk_iff_dvd]
  refine
    ⟨fun h =>
      Associates.le_of_count_ne_zero (Associates.mk_ne_zero.mpr ha0)
        (Associates.irreducible_mk.mpr hp) h,
      fun h => ?_⟩
  rw [← pow_one (Associates.mk p)]; rw [Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr ha0)
      (Associates.irreducible_mk.mpr hp)] at h
  exact (zero_lt_one.trans_le h).ne'

Depends on / 依赖: Associates, Associates.irreducible_mk.mpr, Associates.le_of_count_ne_zero, Associates.mk, Associates.mk_le_mk_iff_dvd, Associates.mk_ne_zero.mpr, Associates.prime_pow_dvd_iff_le, irreducible_mk, le_of_count_ne_zero, mk_le_mk_iff_dvd, mk_ne_zero, pow_one, prime_pow_dvd_iff_le, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem count_ne_zero_iff_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) :
    (Associates.mk p).count (Associates.mk a).factors != 0 ↔ p ∣ a := by
  rw [← Associates.mk_le_mk_iff_dvd]
  refine
    ⟨fun h =>
      Associates.le_of_count_ne_zero (Associates.mk_ne_zero.mpr ha0)
        (Associates.irreducible_mk.mpr hp) h,
      fun h => ?_⟩
  rw [← pow_one (Associates.mk p)]; rw [Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr ha0)
      (Associates.irreducible_mk.mpr hp)] at h
  exact (zero_lt_one.trans_le h).ne'

/--
theorem `count_self` / 定理 `count_self`

English:
theorem count_self
  statement: [Nontrivial α] {p : Associates α}
  proof: by
  simp [factors_self hp, Associates.count_some hp]

中文:
定理 count_self
  结论: [非平凡 α] {p : Associates α}
  证明: by
  simp [factors_self hp, Associates.count_some hp]

Depends on / 依赖: Associates, Associates.count_some, count_some, factors_self
-/
theorem count_self [Nontrivial α] {p : Associates α}
    (hp : Irreducible p) : p.count p.factors = 1 := by
  simp [factors_self hp, Associates.count_some hp]

/--
theorem `count_eq_zero_of_ne` / 定理 `count_eq_zero_of_ne`

English:
theorem count_eq_zero_of_ne
  statement: {p q : Associates α} (hp : Irreducible p)
  proof: not_ne_iff.mp fun h' => h associated_iff_eq.mp hp.associated_of_dvd hq
    le_of_count_ne_zero hq.ne_zero hp h'

中文:
定理 count_eq_zero_of_ne
  结论: {p q : Associates α} (hp : 不可约 p)
  证明: not_ne_iff.mp fun h' => h associated_iff_eq.mp hp.associated_of_dvd hq
    le_of_count_ne_zero hq.ne_zero hp h'

Depends on / 依赖: associated_iff_eq, associated_iff_eq.mp, associated_of_dvd, hp.associated_of_dvd, hq.ne_zero, le_of_count_ne_zero, ne_zero, not_ne_iff, not_ne_iff.mp
-/
theorem count_eq_zero_of_ne {p q : Associates α} (hp : Irreducible p)
    (hq : Irreducible q) (h : p != q) : p.count q.factors = 0 :=
not_ne_iff.mp fun h' => h associated_iff_eq.mp hp.associated_of_dvd hq
    le_of_count_ne_zero hq.ne_zero hp h'

/--
theorem `count_mul` / 定理 `count_mul`

English:
theorem count_mul
  statement: {a : Associates α} (ha : a != 0) {b : Associates α}
  proof: by
  obtain ⟨a0, nza, rfl⟩ := exists_non_zero_rep ha
  obtain ⟨b0, nzb, rfl⟩ := exists_non_zero_rep hb
  rw [factors_mul]; rw [factors_mk a0 nza]; rw [factors_mk b0 nzb]; rw [← FactorSet.coe_add]; rw [count_some hp]; rw [Multiset.count_add]; rw [count_some hp]; rw [count_some hp]

中文:
定理 count_mul
  结论: {a : Associates α} (ha : a != 0) {b : Associates α}
  证明: by
  obtain ⟨a0, nza, rfl⟩ := exists_non_zero_rep ha
  obtain ⟨b0, nzb, rfl⟩ := exists_non_zero_rep hb
  rw [factors_mul]; rw [factors_mk a0 nza]; rw [factors_mk b0 nzb]; rw [← FactorSet.coe_add]; rw [count_some hp]; rw [Multiset.count_add]; rw [count_some hp]; rw [count_some hp]

Depends on / 依赖: FactorSet, FactorSet.coe_add, Multiset, Multiset.count_add, coe_add, count_add, count_some, exists_non_zero_rep, factors_mk, factors_mul
-/
theorem count_mul {a : Associates α} (ha : a != 0) {b : Associates α}
    (hb : b != 0) {p : Associates α} (hp : Irreducible p) :
    count p (factors (a * b)) = count p a.factors + count p b.factors := by
  obtain ⟨a0, nza, rfl⟩ := exists_non_zero_rep ha
  obtain ⟨b0, nzb, rfl⟩ := exists_non_zero_rep hb
  rw [factors_mul]; rw [factors_mk a0 nza]; rw [factors_mk b0 nzb]; rw [← FactorSet.coe_add]; rw [count_some hp]; rw [Multiset.count_add]; rw [count_some hp]; rw [count_some hp]

/--
theorem `count_of_coprime` / 定理 `count_of_coprime`

English:
theorem count_of_coprime
  statement: {a : Associates α} (ha : a != 0)
  proof: by
  rw [or_iff_not_imp_left]; rw [← Ne]
  intro hca
  contrapose! hab with hcb
  exact ⟨p, le_of_count_ne_zero ha hp hca, le_of_count_ne_zero hb hp hcb,
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hp⟩

中文:
定理 count_of_coprime
  结论: {a : Associates α} (ha : a != 0)
  证明: by
  rw [or_iff_not_imp_left]; rw [← Ne]
  intro hca
  contrapose! hab with hcb
  exact ⟨p, le_of_count_ne_zero ha hp hca, le_of_count_ne_zero hb hp hcb,
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hp⟩

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime.mp, contrapose, irreducible_iff_prime, le_of_count_ne_zero, or_iff_not_imp_left
-/
theorem count_of_coprime {a : Associates α} (ha : a != 0)
    {b : Associates α} (hb : b != 0) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d) {p : Associates α}
    (hp : Irreducible p) : count p a.factors = 0 ∨ count p b.factors = 0 := by
  rw [or_iff_not_imp_left]; rw [← Ne]
  intro hca
  contrapose! hab with hcb
  exact ⟨p, le_of_count_ne_zero ha hp hca, le_of_count_ne_zero hb hp hcb,
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hp⟩

/--
theorem `count_mul_of_coprime` / 定理 `count_mul_of_coprime`

English:
theorem count_mul_of_coprime
  statement: {a : Associates α} {b : Associates α}
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  rcases count_of_coprime ha hb hab hp with hz | hb0; · tauto
  apply Or.intro_right
  rw [count_mul ha hb hp]; rw [hb0]; rw [add_zero]

中文:
定理 count_mul_of_coprime
  结论: {a : Associates α} {b : Associates α}
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  rcases count_of_coprime ha hb hab hp with hz | hb0; · tauto
  apply Or.intro_right
  rw [count_mul ha hb hp]; rw [hb0]; rw [add_zero]

Depends on / 依赖: Or.intro_right, add_zero, count_mul, count_of_coprime, intro_right
-/
theorem count_mul_of_coprime {a : Associates α} {b : Associates α}
    (hb : b != 0) {p : Associates α} (hp : Irreducible p) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d) :
    count p a.factors = 0 ∨ count p a.factors = count p (a * b).factors := by
  by_cases ha : a = 0
  · simp [ha]
  rcases count_of_coprime ha hb hab hp with hz | hb0; · tauto
  apply Or.intro_right
  rw [count_mul ha hb hp]; rw [hb0]; rw [add_zero]

/--
theorem `count_mul_of_coprime'` / 定理 `count_mul_of_coprime'`

English:
theorem count_mul_of_coprime'
  statement: {a b : Associates α} {p : Associates α}
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [count_mul ha hb hp]
  rcases count_of_coprime ha hb hab hp with ha0 | hb0
  · apply Or.intro_right
    rw [ha0]; rw [zero_add]
  · apply Or.intro_left
    rw [hb0]; rw [add_zero]

中文:
定理 count_mul_of_coprime'
  结论: {a b : Associates α} {p : Associates α}
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [count_mul ha hb hp]
  rcases count_of_coprime ha hb hab hp with ha0 | hb0
  · apply Or.intro_right
    rw [ha0]; rw [zero_add]
  · apply Or.intro_left
    rw [hb0]; rw [add_zero]

Depends on / 依赖: Or.intro_left, Or.intro_right, add_zero, count_mul, count_of_coprime, intro_left, intro_right, zero_add
-/
theorem count_mul_of_coprime' {a b : Associates α} {p : Associates α}
    (hp : Irreducible p) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d) :
    count p (a * b).factors = count p a.factors ∨ count p (a * b).factors = count p b.factors := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [count_mul ha hb hp]
  rcases count_of_coprime ha hb hab hp with ha0 | hb0
  · apply Or.intro_right
    rw [ha0]; rw [zero_add]
  · apply Or.intro_left
    rw [hb0]; rw [add_zero]

/--
theorem `dvd_count_of_dvd_count_mul` / 定理 `dvd_count_of_dvd_count_mul`

English:
theorem dvd_count_of_dvd_count_mul
  statement: {a b : Associates α} (hb : b != 0)
  proof: by
  by_cases ha : a = 0
  · simpa [*] using habk
  rcases count_of_coprime ha hb hab hp with hz | h
  · rw [hz]
    exact dvd_zero k
  · rw [count_mul ha hb hp, h] at habk
    exact habk

中文:
定理 dvd_count_of_dvd_count_mul
  结论: {a b : Associates α} (hb : b != 0)
  证明: by
  by_cases ha : a = 0
  · simpa [*] using habk
  rcases count_of_coprime ha hb hab hp with hz | h
  · rw [hz]
    exact dvd_zero k
  · rw [count_mul ha hb hp, h] at habk
    exact habk

Depends on / 依赖: count_mul, count_of_coprime, dvd_zero
-/
theorem dvd_count_of_dvd_count_mul {a b : Associates α} (hb : b != 0)
    {p : Associates α} (hp : Irreducible p) (hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d) {k : Nat}
    (habk : k ∣ count p (a * b).factors) : k ∣ count p a.factors := by
  by_cases ha : a = 0
  · simpa [*] using habk
  rcases count_of_coprime ha hb hab hp with hz | h
  · rw [hz]
    exact dvd_zero k
  · rw [count_mul ha hb hp, h] at habk
    exact habk

/--
theorem `count_pow` / 定理 `count_pow`

English:
theorem count_pow
  statement: [Nontrivial α] {a : Associates α} (ha : a != 0)
  proof: by
  induction k with
  | zero => rw [pow_zero, factors_one, zero_mul, count_zero hp]
  | succ n h => rw [pow_succ', count_mul ha (pow_ne_zero _ ha) hp, h]; ring

中文:
定理 count_pow
  结论: [非平凡 α] {a : Associates α} (ha : a != 0)
  证明: by
  induction k with
  | zero => rw [pow_zero, factors_one, zero_mul, count_zero hp]
  | succ n h => rw [pow_succ', count_mul ha (pow_ne_zero _ ha) hp, h]; ring

Depends on / 依赖: count_mul, count_zero, factors_one, pow_ne_zero, pow_succ, pow_zero, zero_mul
-/
theorem count_pow [Nontrivial α] {a : Associates α} (ha : a != 0)
    {p : Associates α} (hp : Irreducible p) (k : Nat) :
    count p (a ^ k).factors = k * count p a.factors := by
  induction k with
  | zero => rw [pow_zero, factors_one, zero_mul, count_zero hp]
  | succ n h => rw [pow_succ', count_mul ha (pow_ne_zero _ ha) hp, h]; ring

/--
theorem `dvd_count_pow` / 定理 `dvd_count_pow`

English:
theorem dvd_count_pow
  statement: [Nontrivial α] {a : Associates α} (ha : a != 0)
  proof: by
  rw [count_pow ha hp]
  apply dvd_mul_right

中文:
定理 dvd_count_pow
  结论: [非平凡 α] {a : Associates α} (ha : a != 0)
  证明: by
  rw [count_pow ha hp]
  apply dvd_mul_right

Depends on / 依赖: count_pow, dvd_mul_right
-/
theorem dvd_count_pow [Nontrivial α] {a : Associates α} (ha : a != 0)
    {p : Associates α} (hp : Irreducible p) (k : Nat) : k ∣ count p (a ^ k).factors := by
  rw [count_pow ha hp]
  apply dvd_mul_right

/--
theorem `is_pow_of_dvd_count` / 定理 `is_pow_of_dvd_count`

English:
theorem is_pow_of_dvd_count
  statement: {a : Associates α}
  proof: by
  nontriviality α
  obtain ⟨a0, hz, rfl⟩ := exists_non_zero_rep ha
  rw [factors_mk a0 hz] at hk
  have hk' : forall p, p in factors' a0 -> k ∣ (factors' a0).count p := by
    rintro p -
    have pp : p = ⟨p.val, p.2⟩ := by simp only [Subtype.coe_eta]
    rw [pp]; rw [← count_some p.2]
    exact hk p.val p.2
  obtain ⟨u, hu⟩ := Multiset.exists_smul_of_dvd_count _ hk'
  use FactorSet.prod (u : FactorSet α)
  apply eq_of_factors_eq_factors
  rw [pow_factors]; rw [prod_factors]; rw [factors_mk a0 hz]; rw [hu]
  exact WithBot.coe_nsmul u k

中文:
定理 is_pow_of_dvd_count
  结论: {a : Associates α}
  证明: by
  nontriviality α
  obtain ⟨a0, hz, rfl⟩ := exists_non_zero_rep ha
  rw [factors_mk a0 hz] at hk
  have hk' : forall p, p in factors' a0 -> k ∣ (factors' a0).count p := by
    rintro p -
    have pp : p = ⟨p.val, p.2⟩ := by simp only [Subtype.coe_eta]
    rw [pp]; rw [← count_some p.2]
    exact hk p.val p.2
  obtain ⟨u, hu⟩ := Multiset.exists_smul_of_dvd_count _ hk'
  use FactorSet.prod (u : FactorSet α)
  apply eq_of_factors_eq_factors
  rw [pow_factors]; rw [prod_factors]; rw [factors_mk a0 hz]; rw [hu]
  exact WithBot.coe_nsmul u k

Depends on / 依赖: FactorSet, FactorSet.prod, Multiset, Multiset.exists_smul_of_dvd_count, Subtype, Subtype.coe_eta, WithBot, WithBot.coe, coe_eta, count_some, eq_of_factors_eq_factors, exists_non_zero_rep, exists_smul_of_dvd_count, factors, factors_mk, nontriviality, p.val, pow_factors, prod_factors
-/
theorem is_pow_of_dvd_count {a : Associates α}
    (ha : a != 0) {k : Nat} (hk : forall p : Associates α, Irreducible p -> k ∣ count p a.factors) :
    exists b : Associates α, a = b ^ k := by
  nontriviality α
  obtain ⟨a0, hz, rfl⟩ := exists_non_zero_rep ha
  rw [factors_mk a0 hz] at hk
  have hk' : forall p, p in factors' a0 -> k ∣ (factors' a0).count p := by
    rintro p -
    have pp : p = ⟨p.val, p.2⟩ := by simp only [Subtype.coe_eta]
    rw [pp]; rw [← count_some p.2]
    exact hk p.val p.2
  obtain ⟨u, hu⟩ := Multiset.exists_smul_of_dvd_count _ hk'
  use FactorSet.prod (u : FactorSet α)
  apply eq_of_factors_eq_factors
  rw [pow_factors]; rw [prod_factors]; rw [factors_mk a0 hz]; rw [hu]
  exact WithBot.coe_nsmul u k

/--
theorem `eq_pow_count_factors_of_dvd_pow` / 定理 `eq_pow_count_factors_of_dvd_pow`

English:
theorem eq_pow_count_factors_of_dvd_pow
  statement: {p a : Associates α}
  proof: by
  nontriviality α
  have hph := pow_ne_zero n hp.ne_zero
  have ha := ne_zero_of_dvd_ne_zero hph h
  apply eq_of_eq_counts ha (pow_ne_zero _ hp.ne_zero)
  have eq_zero_of_ne : forall q : Associates α, Irreducible q -> q != p -> _ = 0 := fun q hq h' =>
Nat.eq_zero_of_le_zero by
      convert! count_le_count_of_le hph hq h
      symm
      rw [count_pow hp.ne_zero hq]; rw [count_eq_zero_of_ne hq hp h']; rw [mul_zero]
  intro q hq
  rw [count_pow hp.ne_zero hq]
  by_cases h : q = p
  · rw [h, count_self hp, mul_one]
  · rw [count_eq_zero_of_ne hq hp h, mul_zero, eq_zero_of_ne q hq h]

中文:
定理 eq_pow_count_factors_of_dvd_pow
  结论: {p a : Associates α}
  证明: by
  nontriviality α
  have hph := pow_ne_zero n hp.ne_zero
  have ha := ne_zero_of_dvd_ne_zero hph h
  apply eq_of_eq_counts ha (pow_ne_zero _ hp.ne_zero)
  have eq_zero_of_ne : forall q : Associates α, Irreducible q -> q != p -> _ = 0 := fun q hq h' =>
Nat.eq_zero_of_le_zero by
      convert! count_le_count_of_le hph hq h
      symm
      rw [count_pow hp.ne_zero hq]; rw [count_eq_zero_of_ne hq hp h']; rw [mul_zero]
  intro q hq
  rw [count_pow hp.ne_zero hq]
  by_cases h : q = p
  · rw [h, count_self hp, mul_one]
  · rw [count_eq_zero_of_ne hq hp h, mul_zero, eq_zero_of_ne q hq h]

Depends on / 依赖: Associates, Irreducible, Nat.eq_zero_of_le_zero, convert, count_eq, count_eq_zero_of_ne, count_le_count_of_le, count_pow, count_self, eq_of_eq_counts, eq_zero_of_le_zero, eq_zero_of_ne, hp.ne_zero, mul_one, mul_zero, ne_zero, ne_zero_of_dvd_ne_zero, nontriviality, pow_ne_zero
-/
theorem eq_pow_count_factors_of_dvd_pow {p a : Associates α}
    (hp : Irreducible p) {n : Nat} (h : a ∣ p ^ n) : a = p ^ p.count a.factors := by
  nontriviality α
  have hph := pow_ne_zero n hp.ne_zero
  have ha := ne_zero_of_dvd_ne_zero hph h
  apply eq_of_eq_counts ha (pow_ne_zero _ hp.ne_zero)
  have eq_zero_of_ne : forall q : Associates α, Irreducible q -> q != p -> _ = 0 := fun q hq h' =>
Nat.eq_zero_of_le_zero by
      convert! count_le_count_of_le hph hq h
      symm
      rw [count_pow hp.ne_zero hq]; rw [count_eq_zero_of_ne hq hp h']; rw [mul_zero]
  intro q hq
  rw [count_pow hp.ne_zero hq]
  by_cases h : q = p
  · rw [h, count_self hp, mul_one]
  · rw [count_eq_zero_of_ne hq hp h, mul_zero, eq_zero_of_ne q hq h]

/--
theorem `count_factors_eq_find_of_dvd_pow` / 定理 `count_factors_eq_find_of_dvd_pow`

English:
theorem count_factors_eq_find_of_dvd_pow
  statement: {a p : Associates α}
  proof: by
  apply le_antisymm
  · refine Nat.find_le ⟨1, ?_⟩
    rw [mul_one]
    symm
    exact eq_pow_count_factors_of_dvd_pow hp h
  · have hph := pow_ne_zero (@Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩) hp.ne_zero
    rcases subsingleton_or_nontrivial α with hα | hα
    · simp [eq_iff_true_of_subsingleton] at hph
    convert! count_le_count_of_le hph hp (@Nat.find_spec (fun n => a ∣ p ^ n) _ ⟨n, h⟩)
    rw [count_pow hp.ne_zero hp]; rw [count_self hp]; rw [mul_one]

中文:
定理 count_factors_eq_find_of_dvd_pow
  结论: {a p : Associates α}
  证明: by
  apply le_antisymm
  · refine Nat.find_le ⟨1, ?_⟩
    rw [mul_one]
    symm
    exact eq_pow_count_factors_of_dvd_pow hp h
  · have hph := pow_ne_zero (@Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩) hp.ne_zero
    rcases subsingleton_or_nontrivial α with hα | hα
    · simp [eq_iff_true_of_subsingleton] at hph
    convert! count_le_count_of_le hph hp (@Nat.find_spec (fun n => a ∣ p ^ n) _ ⟨n, h⟩)
    rw [count_pow hp.ne_zero hp]; rw [count_self hp]; rw [mul_one]

Depends on / 依赖: Nat.find, Nat.find_le, Nat.find_spec, convert, count_le_count_of_le, count_pow, count_self, eq_iff_true_of_subsingleton, eq_pow_count_factors_of_dvd_pow, find_le, find_spec, hp.ne_zero, le_antisymm, mul_one, ne_zero, pow_ne_zero, subsingleton_or_nontrivial
-/
theorem count_factors_eq_find_of_dvd_pow {a p : Associates α}
    (hp : Irreducible p) [forall n : Nat, Decidable (a ∣ p ^ n)] {n : Nat} (h : a ∣ p ^ n) :
    @Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩ = p.count a.factors := by
  apply le_antisymm
  · refine Nat.find_le ⟨1, ?_⟩
    rw [mul_one]
    symm
    exact eq_pow_count_factors_of_dvd_pow hp h
  · have hph := pow_ne_zero (@Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩) hp.ne_zero
    rcases subsingleton_or_nontrivial α with hα | hα
    · simp [eq_iff_true_of_subsingleton] at hph
    convert! count_le_count_of_le hph hp (@Nat.find_spec (fun n => a ∣ p ^ n) _ ⟨n, h⟩)
    rw [count_pow hp.ne_zero hp]; rw [count_self hp]; rw [mul_one]

end count

/--
theorem `eq_pow_of_mul_eq_pow` / 定理 `eq_pow_of_mul_eq_pow`

English:
theorem eq_pow_of_mul_eq_pow
  statement: {a b c : Associates α} (ha : a != 0) (hb : b != 0)
  proof: by
  classical
  nontriviality α
  by_cases hk0 : k = 0
  · use 1
    rw [hk0]; rw [pow_zero] at h ⊢
    apply (mul_eq_one.1 h).1
  · refine is_pow_of_dvd_count ha fun p hp => ?_
    apply dvd_count_of_dvd_count_mul hb hp hab
    rw [h]
    apply dvd_count_pow _ hp
    rintro rfl
    rw [zero_pow hk0] at h
    cases mul_eq_zero.mp h <;> contradiction

中文:
定理 eq_pow_of_mul_eq_pow
  结论: {a b c : Associates α} (ha : a != 0) (hb : b != 0)
  证明: by
  classical
  nontriviality α
  by_cases hk0 : k = 0
  · use 1
    rw [hk0]; rw [pow_zero] at h ⊢
    apply (mul_eq_one.1 h).1
  · refine is_pow_of_dvd_count ha fun p hp => ?_
    apply dvd_count_of_dvd_count_mul hb hp hab
    rw [h]
    apply dvd_count_pow _ hp
    rintro rfl
    rw [zero_pow hk0] at h
    cases mul_eq_zero.mp h <;> contradiction

Depends on / 依赖: classical, dvd_count_of_dvd_count_mul, dvd_count_pow, is_pow_of_dvd_count, mul_eq_one, mul_eq_zero, mul_eq_zero.mp, nontriviality, pow_zero, zero_pow
-/
theorem eq_pow_of_mul_eq_pow {a b c : Associates α} (ha : a != 0) (hb : b != 0)
    (hab : forall d, d ∣ a -> d ∣ b -> ¬Prime d) {k : Nat} (h : a * b = c ^ k) :
    exists d : Associates α, a = d ^ k := by
  classical
  nontriviality α
  by_cases hk0 : k = 0
  · use 1
    rw [hk0]; rw [pow_zero] at h ⊢
    apply (mul_eq_one.1 h).1
  · refine is_pow_of_dvd_count ha fun p hp => ?_
    apply dvd_count_of_dvd_count_mul hb hp hab
    rw [h]
    apply dvd_count_pow _ hp
    rintro rfl
    rw [zero_pow hk0] at h
    cases mul_eq_zero.mp h <;> contradiction

/--
theorem `eq_pow_find_of_dvd_irreducible_pow` / 定理 `eq_pow_find_of_dvd_irreducible_pow`

English:
theorem eq_pow_find_of_dvd_irreducible_pow
  statement: {a p : Associates α} (hp : Irreducible p)
  proof: by
  classical rw [count_factors_eq_find_of_dvd_pow hp, ← eq_pow_count_factors_of_dvd_pow hp h]
  exact h

中文:
定理 eq_pow_find_of_dvd_irreducible_pow
  结论: {a p : Associates α} (hp : 不可约 p)
  证明: by
  classical rw [count_factors_eq_find_of_dvd_pow hp, ← eq_pow_count_factors_of_dvd_pow hp h]
  exact h

Depends on / 依赖: classical, count_factors_eq_find_of_dvd_pow, eq_pow_count_factors_of_dvd_pow
-/
theorem eq_pow_find_of_dvd_irreducible_pow {a p : Associates α} (hp : Irreducible p)
    [forall n : Nat, Decidable (a ∣ p ^ n)] {n : Nat} (h : a ∣ p ^ n) :
    a = p ^ @Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩ := by
  classical rw [count_factors_eq_find_of_dvd_pow hp, ← eq_pow_count_factors_of_dvd_pow hp h]
  exact h

end Associates
