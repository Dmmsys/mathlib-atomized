/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.Factorization.LCM
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Peel

/-!
# Exponent of a group

This file defines the exponent of a group, or more generally a monoid. For a group `G` it is defined
to be the minimal `n≥1` such that `g ^ n = 1` for all `g ∈ G`. For a finite group `G`,
it is equal to the lowest common multiple of the order of all elements of the group `G`.

## Main definitions

* `Monoid.ExponentExists` is a predicate on a monoid `G` saying that there is some positive `n`
  such that `g ^ n = 1` for all `g ∈ G`.
* `Monoid.exponent` defines the exponent of a monoid `G` as the minimal positive `n` such that
  `g ^ n = 1` for all `g ∈ G`, by convention it is `0` if no such `n` exists.
* `AddMonoid.ExponentExists` the additive version of `Monoid.ExponentExists`.
* `AddMonoid.exponent` the additive version of `Monoid.exponent`.

## Main results

* `Monoid.lcm_order_eq_exponent`: For a finite left cancel monoid `G`, the exponent is equal to the
  `Finset.lcm` of the order of its elements.
* `Monoid.exponent_eq_iSup_orderOf(')`: For a commutative cancel monoid, the exponent is
  equal to `⨆ g : G, orderOf g` (or zero if it has any order-zero elements).
* `Monoid.exponent_pi` and `Monoid.exponent_prod`: The exponent of a finite product of monoids is
  the least common multiple (`Finset.lcm` and `lcm`, respectively) of the exponents of the
  constituent monoids.
* `MonoidHom.exponent_dvd`: If `f : M₁ →⋆ M₂` is surjective, then the exponent of `M₂` divides the
  exponent of `M₁`.

## TODO
* Refactor the characteristic of a ring to be the exponent of its underlying additive group.
-/

@[expose] public section


universe u

variable {G : Type u}

namespace Monoid

section Monoid

variable (G) [Monoid G]

/-- A predicate on a monoid saying that there is a positive integer `n` such that `g ^ n = 1`
for all `g`. -/
@[to_additive
/-- A predicate on an additive monoid saying that there is a positive integer `n` such that
`n • g = 0` for all `g`. -/]
/--
Definition of `ExponentExists` / `ExponentExists` 的定义

English:
definition ExponentExists
  body: exists n, 0 < n ∧ forall g : G, g ^ n = 1

中文:
定义 ExponentExists
  定义体: exists n, 0 < n ∧ forall g : G, g ^ n = 1
-/
def ExponentExists :=
  exists n, 0 < n ∧ forall g : G, g ^ n = 1

open scoped Classical in
/-- The exponent of a group is the smallest positive integer `n` such that `g ^ n = 1` for all
`g ∈ G` if it exists, otherwise it is zero by convention. -/
@[to_additive
/-- The exponent of an additive group is the smallest positive integer `n` such that
`n • g = 0` for all `g ∈ G` if it exists, otherwise it is zero by convention. -/]
/--
Definition of `exponent` / `exponent` 的定义

English:
definition exponent
  body: if h : ExponentExists G then Nat.find h else 0

中文:
定义 exponent
  定义体: if h : ExponentExists G then Nat.find h else 0

Depends on / 依赖: ExponentExists, Nat.find
-/
noncomputable def exponent :=
  if h : ExponentExists G then Nat.find h else 0

variable {G}

@[simp]
/--
theorem `_root_.AddMonoid.exponent_additive` / 定理 `_root_.AddMonoid.exponent_additive`

English:
theorem _root_.AddMonoid.exponent_additive
  proof: rfl

@[simp]

中文:
定理 _root_.AddMonoid.exponent_additive
  证明: rfl

@[simp]
-/
theorem _root_.AddMonoid.exponent_additive :
    AddMonoid.exponent (Additive G) = exponent G := rfl

@[simp]
/--
theorem `exponent_multiplicative` / 定理 `exponent_multiplicative`

English:
theorem exponent_multiplicative
  given: {G : Type*} [AddMonoid G]
  proof: rfl

中文:
定理 exponent_multiplicative
  条件: {G : 类型} [AddMonoid G]
  证明: rfl
-/
theorem exponent_multiplicative {G : Type*} [AddMonoid G] :
    exponent (Multiplicative G) = AddMonoid.exponent G := rfl

set_option backward.isDefEq.respectTransparency false in
open MulOpposite in
@[to_additive (attr := simp)]
/--
theorem `_root_.MulOpposite.exponent` / 定理 `_root_.MulOpposite.exponent`

English:
theorem _root_.MulOpposite.exponent
  statement: exponent (MulOpposite G) = exponent G
  proof: by
  simp only [Monoid.exponent, ExponentExists]
  congr!
  all_goals exact ⟨(op_injective <| · <| op ·), (unop_injective <| · <| unop ·)⟩

@[to_additive]

中文:
定理 _root_.MulOpposite.exponent
  结论: exponent (MulOpposite G) = exponent G
  证明: by
  simp only [Monoid.exponent, ExponentExists]
  congr!
  all_goals exact ⟨(op_injective <| · <| op ·), (unop_injective <| · <| unop ·)⟩

@[to_additive]

Depends on / 依赖: ExponentExists, Monoid, Monoid.exponent, all_goals, exponent, op_injective, unop_injective
-/
theorem _root_.MulOpposite.exponent : exponent (MulOpposite G) = exponent G := by
  simp only [Monoid.exponent, ExponentExists]
  congr!
  all_goals exact ⟨(op_injective <| · <| op ·), (unop_injective <| · <| unop ·)⟩

@[to_additive]
/--
theorem `ExponentExists.isOfFinOrder` / 定理 `ExponentExists.isOfFinOrder`

English:
theorem ExponentExists.isOfFinOrder
  given: (h : ExponentExists G) {g : G}
  statement: IsOfFinOrder g
  proof: isOfFinOrder_iff_pow_eq_one.mpr by peel 2 h; exact this g

@[to_additive]

中文:
定理 ExponentExists.isOfFinOrder
  条件: (h : ExponentExists G) {g : G}
  结论: IsOfFinOrder g
  证明: isOfFinOrder_iff_pow_eq_one.mpr by peel 2 h; exact this g

@[to_additive]

Depends on / 依赖: isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one.mpr
-/
theorem ExponentExists.isOfFinOrder (h : ExponentExists G) {g : G} : IsOfFinOrder g :=
isOfFinOrder_iff_pow_eq_one.mpr by peel 2 h; exact this g

@[to_additive]
/--
theorem `ExponentExists.orderOf_pos` / 定理 `ExponentExists.orderOf_pos`

English:
theorem ExponentExists.orderOf_pos
  given: (h : ExponentExists G) (g : G)
  statement: 0 < orderOf g
  proof: h.isOfFinOrder.orderOf_pos

中文:
定理 ExponentExists.orderOf_pos
  条件: (h : ExponentExists G) (g : G)
  结论: 0 < orderOf g
  证明: h.isOfFinOrder.orderOf_pos

Depends on / 依赖: h.isOfFinOrder.orderOf_pos, isOfFinOrder, orderOf_pos
-/
theorem ExponentExists.orderOf_pos (h : ExponentExists G) (g : G) : 0 < orderOf g :=
  h.isOfFinOrder.orderOf_pos

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `exponent_ne_zero` / 定理 `exponent_ne_zero`

English:
theorem exponent_ne_zero
  statement: exponent G != 0 ↔ ExponentExists G
  proof: by
  rw [exponent]
  split_ifs with h
  · simp [h]
  --if this isn't done this way, `to_additive` freaks
  · tauto

@[to_additive]
protected alias ⟨_, ExponentExists.exponent_ne_zero⟩ := exponent_ne_zero

@[to_additive]

中文:
定理 exponent_ne_zero
  结论: exponent G != 0 ↔ ExponentExists G
  证明: by
  rw [exponent]
  split_ifs with h
  · simp [h]
  --if this isn't done this way, `to_additive` freaks
  · tauto

@[to_additive]
protected alias ⟨_, ExponentExists.exponent_ne_zero⟩ := exponent_ne_zero

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.zpow_right, exponent, h.pow_right, inv_pow, isUnit_det_of_left_inverse, nonsing_inv_cancel_or_zero, pow_right, split_ifs, zpow_right
-/
theorem exponent_ne_zero : exponent G != 0 ↔ ExponentExists G := by
  rw [exponent]
  split_ifs with h
  · simp [h]
  --if this isn't done this way, `to_additive` freaks
  · tauto

@[to_additive]
protected alias ⟨_, ExponentExists.exponent_ne_zero⟩ := exponent_ne_zero

@[to_additive]
/--
theorem `exponent_pos` / 定理 `exponent_pos`

English:
theorem exponent_pos
  statement: 0 < exponent G ↔ ExponentExists G
  proof: pos_iff_ne_zero.trans exponent_ne_zero

@[to_additive]
protected alias ⟨_, ExponentExists.exponent_pos⟩ := exponent_pos

@[to_additive]

中文:
定理 exponent_pos
  结论: 0 < exponent G ↔ ExponentExists G
  证明: pos_iff_ne_zero.trans exponent_ne_zero

@[to_additive]
protected alias ⟨_, ExponentExists.exponent_pos⟩ := exponent_pos

@[to_additive]

Depends on / 依赖: Commute, Commute.zpow_right, exponent_ne_zero, h.symm, pos_iff_ne_zero, pos_iff_ne_zero.trans, zpow_right
-/
theorem exponent_pos : 0 < exponent G ↔ ExponentExists G :=
  pos_iff_ne_zero.trans exponent_ne_zero

@[to_additive]
protected alias ⟨_, ExponentExists.exponent_pos⟩ := exponent_pos

@[to_additive]
/--
theorem `exponent_eq_zero_iff` / 定理 `exponent_eq_zero_iff`

English:
theorem exponent_eq_zero_iff
  statement: exponent G = 0 ↔ ¬ExponentExists G
  proof: exponent_ne_zero.not_right

@[to_additive exponent_eq_zero_addOrder_zero]

中文:
定理 exponent_eq_zero_iff
  结论: exponent G = 0 ↔ ¬ExponentExists G
  证明: exponent_ne_zero.not_right

@[to_additive exponent_eq_zero_addOrder_zero]

Depends on / 依赖: exponent_ne_zero, exponent_ne_zero.not_right, not_right
-/
theorem exponent_eq_zero_iff : exponent G = 0 ↔ ¬ExponentExists G :=
  exponent_ne_zero.not_right

@[to_additive exponent_eq_zero_addOrder_zero]
/--
theorem `exponent_eq_zero_of_order_zero` / 定理 `exponent_eq_zero_of_order_zero`

English:
theorem exponent_eq_zero_of_order_zero
  given: {g : G} (hg : orderOf g = 0)
  statement: exponent G = 0
  proof: .ne' hg exponent_eq_zero_iff.mpr fun h => h.orderOf_pos g

@[to_additive]

中文:
定理 exponent_eq_zero_of_order_zero
  条件: {g : G} (hg : orderOf g = 0)
  结论: exponent G = 0
  证明: .ne' hg exponent_eq_zero_iff.mpr fun h => h.orderOf_pos g

@[to_additive]

Depends on / 依赖: exponent_eq_zero_iff, exponent_eq_zero_iff.mpr, h.orderOf_pos, orderOf_pos
-/
theorem exponent_eq_zero_of_order_zero {g : G} (hg : orderOf g = 0) : exponent G = 0 :=
.ne' hg exponent_eq_zero_iff.mpr fun h => h.orderOf_pos g

@[to_additive]
/--
theorem `exponent_eq_sInf` / 定理 `exponent_eq_sInf`

English:
theorem exponent_eq_sInf
  proof: by
  by_cases h : Monoid.ExponentExists G
  · have h' : {d : Nat | 0 < d ∧ forall x : G, x ^ d = 1}.Nonempty := h
    rw [Monoid.exponent]; rw [dif_pos h]; rw [Nat.sInf_def h']
    congr
  · have : {d | 0 < d ∧ forall (x : G), x ^ d = 1} = ∅ :=
      Set.eq_empty_of_forall_notMem fun n hn => h ⟨n, h

中文:
定理 exponent_eq_sInf
  证明: by
  by_cases h : Monoid.ExponentExists G
  · have h' : {d : Nat | 0 < d ∧ forall x : G, x ^ d = 1}.Nonempty := h
    rw [Monoid.exponent]; rw [dif_pos h]; rw [Nat.sInf_def h']
    congr
  · have : {d | 0 < d ∧ forall (x : G), x ^ d = 1} = ∅ :=
      Set.eq_empty_of_forall_notMem fun n hn => h ⟨n, h

Depends on / 依赖: ExponentExists, Monoid, Monoid.ExponentExists, Monoid.exponent, Monoid.exponent_eq_zero_iff.mpr, Nat.sInf_def, Nat.sInf_empty, Nonempty, Set.eq_empty_of_forall_notMem, dif_pos, eq_empty_of_forall_notMem, exponent, exponent_eq_zero_iff, sInf_def, sInf_empty
-/
theorem exponent_eq_sInf :
    Monoid.exponent G = sInf {d : Nat | 0 < d ∧ forall x : G, x ^ d = 1} := by
  by_cases h : Monoid.ExponentExists G
  · have h' : {d : Nat | 0 < d ∧ forall x : G, x ^ d = 1}.Nonempty := h
    rw [Monoid.exponent]; rw [dif_pos h]; rw [Nat.sInf_def h']
    congr
  · have : {d | 0 < d ∧ forall (x : G), x ^ d = 1} = ∅ :=
      Set.eq_empty_of_forall_notMem fun n hn => h ⟨n, hn⟩
    rw [Monoid.exponent_eq_zero_iff.mpr h]; rw [this]; rw [Nat.sInf_empty]

/-- The exponent is zero iff for all nonzero `n`, one can find a `g` such that `g ^ n ≠ 1`. -/
@[to_additive /-- The exponent is zero iff for all nonzero `n`, one can find a `g` such that
`n • g ≠ 0`. -/]
/--
theorem `exponent_eq_zero_iff_forall` / 定理 `exponent_eq_zero_iff_forall`

English:
theorem exponent_eq_zero_iff_forall
  statement: exponent G = 0 ↔ forall n > 0, exists g : G, g ^ n != 1
  proof: by
  rw [exponent_eq_zero_iff]; rw [ExponentExists]
  push Not
  rfl

@[to_additive exponent_nsmul_eq_zero]

中文:
定理 exponent_eq_zero_iff_forall
  结论: exponent G = 0 ↔ 对任意 n > 0, 存在 g : G, g ^ n != 1
  证明: by
  rw [exponent_eq_zero_iff]; rw [ExponentExists]
  push Not
  rfl

@[to_additive exponent_nsmul_eq_zero]

Depends on / 依赖: ExponentExists, exponent_eq_zero_iff
-/
theorem exponent_eq_zero_iff_forall : exponent G = 0 ↔ forall n > 0, exists g : G, g ^ n != 1 := by
  rw [exponent_eq_zero_iff]; rw [ExponentExists]
  push Not
  rfl

@[to_additive exponent_nsmul_eq_zero]
/--
theorem `pow_exponent_eq_one` / 定理 `pow_exponent_eq_one`

English:
theorem pow_exponent_eq_one
  given: (g : G)
  statement: g ^ exponent G = 1
  proof: by
  classical
  by_cases h : ExponentExists G
  · simp_rw [exponent, dif_pos h]
    exact (Nat.find_spec h).2 g
  · simp_rw [exponent, dif_neg h, pow_zero]

@[to_additive]

中文:
定理 pow_exponent_eq_one
  条件: (g : G)
  结论: g ^ exponent G = 1
  证明: by
  classical
  by_cases h : ExponentExists G
  · simp_rw [exponent, dif_pos h]
    exact (Nat.find_spec h).2 g
  · simp_rw [exponent, dif_neg h, pow_zero]

@[to_additive]

Depends on / 依赖: ExponentExists, Nat.find_spec, classical, dif_neg, dif_pos, exponent, find_spec, pow_zero, simp_rw
-/
theorem pow_exponent_eq_one (g : G) : g ^ exponent G = 1 := by
  classical
  by_cases h : ExponentExists G
  · simp_rw [exponent, dif_pos h]
    exact (Nat.find_spec h).2 g
  · simp_rw [exponent, dif_neg h, pow_zero]

@[to_additive]
/--
theorem `pow_eq_mod_exponent` / 定理 `pow_eq_mod_exponent`

English:
theorem pow_eq_mod_exponent
  given: {n : Nat} (g : G)
  statement: g ^ n = g ^ (n % exponent G)
  proof: calc
    g ^ n = g ^ (n % exponent G + exponent G * (n / exponent G)) := by rw [Nat.mod_add_div]
    _ = g ^ (n % exponent G) := by simp [pow_add, pow_mul, pow_exponent_eq_one]

@[to_additive]

中文:
定理 pow_eq_mod_exponent
  条件: {n : 自然数} (g : G)
  结论: g ^ n = g ^ (n % exponent G)
  证明: calc
    g ^ n = g ^ (n % exponent G + exponent G * (n / exponent G)) := by rw [Nat.mod_add_div]
    _ = g ^ (n % exponent G) := by simp [pow_add, pow_mul, pow_exponent_eq_one]

@[to_additive]

Depends on / 依赖: Nat.mod_add_div, exponent, mod_add_div, pow_add, pow_exponent_eq_one, pow_mul
-/
theorem pow_eq_mod_exponent {n : Nat} (g : G) : g ^ n = g ^ (n % exponent G) :=
  calc
    g ^ n = g ^ (n % exponent G + exponent G * (n / exponent G)) := by rw [Nat.mod_add_div]
    _ = g ^ (n % exponent G) := by simp [pow_add, pow_mul, pow_exponent_eq_one]

@[to_additive]
/--
theorem `exponent_pos_of_exists` / 定理 `exponent_pos_of_exists`

English:
theorem exponent_pos_of_exists
  given: (n : Nat) (hpos : 0 < n) (hG : forall g : G, g ^ n = 1)
  proof: ExponentExists.exponent_pos ⟨n, hpos, hG⟩

@[to_additive]

中文:
定理 exponent_pos_of_exists
  条件: (n : 自然数) (hpos : 0 < n) (hG : 对任意 g : G, g ^ n = 1)
  证明: ExponentExists.exponent_pos ⟨n, hpos, hG⟩

@[to_additive]

Depends on / 依赖: ExponentExists, ExponentExists.exponent_pos, exponent_pos
-/
theorem exponent_pos_of_exists (n : Nat) (hpos : 0 < n) (hG : forall g : G, g ^ n = 1) :
    0 < exponent G :=
  ExponentExists.exponent_pos ⟨n, hpos, hG⟩

@[to_additive]
/--
theorem `exponent_min'` / 定理 `exponent_min'`

English:
theorem exponent_min'
  given: (n : Nat) (hpos : 0 < n) (hG : forall g : G, g ^ n = 1)
  statement: exponent G <= n
  proof: by
  classical
  rw [exponent]; rw [dif_pos]
  · apply Nat.find_min'
    exact ⟨hpos, hG⟩
  · exact ⟨n, hpos, hG⟩

@[to_additive]

中文:
定理 exponent_min'
  条件: (n : 自然数) (hpos : 0 < n) (hG : 对任意 g : G, g ^ n = 1)
  结论: exponent G <= n
  证明: by
  classical
  rw [exponent]; rw [dif_pos]
  · apply Nat.find_min'
    exact ⟨hpos, hG⟩
  · exact ⟨n, hpos, hG⟩

@[to_additive]

Depends on / 依赖: Nat.find_min, classical, dif_pos, exponent, find_min
-/
theorem exponent_min' (n : Nat) (hpos : 0 < n) (hG : forall g : G, g ^ n = 1) : exponent G <= n := by
  classical
  rw [exponent]; rw [dif_pos]
  · apply Nat.find_min'
    exact ⟨hpos, hG⟩
  · exact ⟨n, hpos, hG⟩

@[to_additive]
/--
theorem `exponent_min` / 定理 `exponent_min`

English:
theorem exponent_min
  given: (m : Nat) (hpos : 0 < m) (hm : m < exponent G)
  statement: exists g : G, g ^ m != 1
  proof: by
  by_contra! h
  have hcon : exponent G <= m := exponent_min' m hpos h
  lia

@[to_additive AddMonoid.exp_eq_one_iff]

中文:
定理 exponent_min
  条件: (m : 自然数) (hpos : 0 < m) (hm : m < exponent G)
  结论: 存在 g : G, g ^ m != 1
  证明: by
  by_contra! h
  have hcon : exponent G <= m := exponent_min' m hpos h
  lia

@[to_additive AddMonoid.exp_eq_one_iff]

Depends on / 依赖: exponent, exponent_min
-/
theorem exponent_min (m : Nat) (hpos : 0 < m) (hm : m < exponent G) : exists g : G, g ^ m != 1 := by
  by_contra! h
  have hcon : exponent G <= m := exponent_min' m hpos h
  lia

@[to_additive AddMonoid.exp_eq_one_iff]
/--
theorem `exp_eq_one_iff` / 定理 `exp_eq_one_iff`

English:
theorem exp_eq_one_iff
  statement: exponent G = 1 ↔ Subsingleton G
  proof: by
  refine ⟨fun eq_one => ⟨fun a b => ?a_eq_b⟩, fun h => le_antisymm ?le ?ge⟩
  · rw [← pow_one a, ← pow_one b, ← eq_one, Monoid.pow_exponent_eq_one, Monoid.pow_exponent_eq_one]
  · apply exponent_min' _ Nat.one_pos
    simp [eq_iff_true_of_subsingleton]
  · apply Nat.succ_le_of_lt
    apply expone

中文:
定理 exp_eq_one_iff
  结论: exponent G = 1 ↔ Subsingleton G
  证明: by
  refine ⟨fun eq_one => ⟨fun a b => ?a_eq_b⟩, fun h => le_antisymm ?le ?ge⟩
  · rw [← pow_one a, ← pow_one b, ← eq_one, Monoid.pow_exponent_eq_one, Monoid.pow_exponent_eq_one]
  · apply exponent_min' _ Nat.one_pos
    simp [eq_iff_true_of_subsingleton]
  · apply Nat.succ_le_of_lt
    apply expone

Depends on / 依赖: Monoid, Monoid.pow_exponent_eq_one, Nat.one_pos, Nat.succ_le_of_lt, a_eq_b, eq_iff_true_of_subsingleton, eq_one, exponent_min, exponent_pos_of_exists, le_antisymm, one_pos, pow_exponent_eq_one, pow_one, succ_le_of_lt
-/
theorem exp_eq_one_iff : exponent G = 1 ↔ Subsingleton G := by
  refine ⟨fun eq_one => ⟨fun a b => ?a_eq_b⟩, fun h => le_antisymm ?le ?ge⟩
  · rw [← pow_one a, ← pow_one b, ← eq_one, Monoid.pow_exponent_eq_one, Monoid.pow_exponent_eq_one]
  · apply exponent_min' _ Nat.one_pos
    simp [eq_iff_true_of_subsingleton]
  · apply Nat.succ_le_of_lt
    apply exponent_pos_of_exists 1 Nat.one_pos
    simp [eq_iff_true_of_subsingleton]

@[to_additive (attr := simp) AddMonoid.exp_eq_one_of_subsingleton]
/--
theorem `exp_eq_one_of_subsingleton` / 定理 `exp_eq_one_of_subsingleton`

English:
theorem exp_eq_one_of_subsingleton
  given: [hs : Subsingleton G]
  statement: exponent G = 1
  proof: exp_eq_one_iff.mpr hs

@[to_additive addOrder_dvd_exponent]

中文:
定理 exp_eq_one_of_subsingleton
  条件: [hs : Subsingleton G]
  结论: exponent G = 1
  证明: exp_eq_one_iff.mpr hs

@[to_additive addOrder_dvd_exponent]

Depends on / 依赖: exp_eq_one_iff, exp_eq_one_iff.mpr
-/
theorem exp_eq_one_of_subsingleton [hs : Subsingleton G] : exponent G = 1 :=
  exp_eq_one_iff.mpr hs

@[to_additive addOrder_dvd_exponent]
/--
theorem `order_dvd_exponent` / 定理 `order_dvd_exponent`

English:
theorem order_dvd_exponent
  given: (g : G)
  statement: orderOf g ∣ exponent G
  proof: orderOf_dvd_of_pow_eq_one pow_exponent_eq_one g

@[to_additive]

中文:
定理 order_dvd_exponent
  条件: (g : G)
  结论: orderOf g ∣ exponent G
  证明: orderOf_dvd_of_pow_eq_one pow_exponent_eq_one g

@[to_additive]

Depends on / 依赖: orderOf_dvd_of_pow_eq_one, pow_exponent_eq_one
-/
theorem order_dvd_exponent (g : G) : orderOf g ∣ exponent G :=
orderOf_dvd_of_pow_eq_one pow_exponent_eq_one g

@[to_additive]
/--
theorem `orderOf_le_exponent` / 定理 `orderOf_le_exponent`

English:
theorem orderOf_le_exponent
  given: (h : ExponentExists G) (g : G)
  statement: orderOf g <= exponent G
  proof: Nat.le_of_dvd h.exponent_pos (order_dvd_exponent g)

@[to_additive]

中文:
定理 orderOf_le_exponent
  条件: (h : ExponentExists G) (g : G)
  结论: orderOf g <= exponent G
  证明: Nat.le_of_dvd h.exponent_pos (order_dvd_exponent g)

@[to_additive]

Depends on / 依赖: Nat.le_of_dvd, exponent_pos, h.exponent_pos, le_of_dvd, order_dvd_exponent
-/
theorem orderOf_le_exponent (h : ExponentExists G) (g : G) : orderOf g <= exponent G :=
  Nat.le_of_dvd h.exponent_pos (order_dvd_exponent g)

@[to_additive]
/--
theorem `exponent_dvd_iff_forall_pow_eq_one` / 定理 `exponent_dvd_iff_forall_pow_eq_one`

English:
theorem exponent_dvd_iff_forall_pow_eq_one
  given: {n : Nat}
  statement: exponent G ∣ n ↔ forall g : G, g ^ n = 1
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  constructor
  · intro h g
    rw [Nat.dvd_iff_mod_eq_zero] at h
    rw [pow_eq_mod_exponent]; rw [h]; rw [pow_zero]
  · intro hG
    by_contra h
    rw [Nat.dvd_iff_mod_eq_zero]; rw [← Ne]; rw [← pos_iff_ne_zero] at h
    have h₂ : n % expone

中文:
定理 exponent_dvd_iff_forall_pow_eq_one
  条件: {n : 自然数}
  结论: exponent G ∣ n ↔ 对任意 g : G, g ^ n = 1
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  constructor
  · intro h g
    rw [Nat.dvd_iff_mod_eq_zero] at h
    rw [pow_eq_mod_exponent]; rw [h]; rw [pow_zero]
  · intro hG
    by_contra h
    rw [Nat.dvd_iff_mod_eq_zero]; rw [← Ne]; rw [← pos_iff_ne_zero] at h
    have h₂ : n % expone

Depends on / 依赖: Nat.dvd_iff_mod_eq_zero, Nat.mod_lt, dvd_iff_mod_eq_zero, eq_zero_or_pos, exponent, exponent_min, exponent_pos_of_exists, mod_lt, n.eq_zero_or_pos, not_ge, pos_iff_ne_zero, pow_eq_mod_exponent, pow_zero, simp_rw
-/
theorem exponent_dvd_iff_forall_pow_eq_one {n : Nat} : exponent G ∣ n ↔ forall g : G, g ^ n = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  constructor
  · intro h g
    rw [Nat.dvd_iff_mod_eq_zero] at h
    rw [pow_eq_mod_exponent]; rw [h]; rw [pow_zero]
  · intro hG
    by_contra h
    rw [Nat.dvd_iff_mod_eq_zero]; rw [← Ne]; rw [← pos_iff_ne_zero] at h
    have h₂ : n % exponent G < exponent G := Nat.mod_lt _ (exponent_pos_of_exists n hpos hG)
    have h₃ : exponent G <= n % exponent G := by
      apply exponent_min' _ h
      simp_rw [← pow_eq_mod_exponent]
      exact hG
    exact h₂.not_ge h₃

@[to_additive]
alias ⟨_, exponent_dvd_of_forall_pow_eq_one⟩ := exponent_dvd_iff_forall_pow_eq_one

@[to_additive]
/--
theorem `exponent_dvd` / 定理 `exponent_dvd`

English:
theorem exponent_dvd
  given: {n : Nat}
  statement: exponent G ∣ n ↔ forall g : G, orderOf g ∣ n
  proof: by
  simp_rw [exponent_dvd_iff_forall_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

中文:
定理 exponent_dvd
  条件: {n : 自然数}
  结论: exponent G ∣ n ↔ 对任意 g : G, orderOf g ∣ n
  证明: by
  simp_rw [exponent_dvd_iff_forall_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

Depends on / 依赖: exponent_dvd_iff_forall_pow_eq_one, orderOf_dvd_iff_pow_eq_one, simp_rw
-/
theorem exponent_dvd {n : Nat} : exponent G ∣ n ↔ forall g : G, orderOf g ∣ n := by
  simp_rw [exponent_dvd_iff_forall_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

variable (G)

@[to_additive]
/--
theorem `lcm_orderOf_dvd_exponent` / 定理 `lcm_orderOf_dvd_exponent`

English:
theorem lcm_orderOf_dvd_exponent
  given: [Fintype G]
  proof: by
  apply Finset.lcm_dvd
  intro g _
  exact order_dvd_exponent g

@[to_additive exists_addOrderOf_eq_pow_padic_val_nat_add_exponent]

中文:
定理 lcm_orderOf_dvd_exponent
  条件: [Fintype G]
  证明: by
  apply Finset.lcm_dvd
  intro g _
  exact order_dvd_exponent g

@[to_additive exists_addOrderOf_eq_pow_padic_val_nat_add_exponent]

Depends on / 依赖: Finset, Finset.lcm_dvd, lcm_dvd, order_dvd_exponent
-/
theorem lcm_orderOf_dvd_exponent [Fintype G] :
    (Finset.univ : Finset G).lcm orderOf ∣ exponent G := by
  apply Finset.lcm_dvd
  intro g _
  exact order_dvd_exponent g

@[to_additive exists_addOrderOf_eq_pow_padic_val_nat_add_exponent]
/--
theorem `_root_.Nat.Prime.exists_orderOf_eq_pow_factorization_exponent` / 定理 `_root_.Nat.Prime.exists_orderOf_eq_pow_factorization_exponent`

English:
theorem _root_.Nat.Prime.exists_orderOf_eq_pow_factorization_exponent
  given: {p : Nat} (hp : p.Prime)
  proof: by
  have := Fact.mk hp
  rcases eq_or_ne ((exponent G).factorization p) 0 with (h | h)
  · refine ⟨1, by rw [h, pow_zero, orderOf_one]⟩
  have he : 0 < exponent G :=
    Ne.bot_lt fun ht => by
      rw [ht] at h
      apply h
      rw [bot_eq_zero]; rw [Nat.factorization_zero]; rw [Finsupp.zero_app

中文:
定理 _root_.Nat.Prime.exists_orderOf_eq_pow_factorization_exponent
  条件: {p : 自然数} (hp : p.Prime)
  证明: by
  have := Fact.mk hp
  rcases eq_or_ne ((exponent G).factorization p) 0 with (h | h)
  · refine ⟨1, by rw [h, pow_zero, orderOf_one]⟩
  have he : 0 < exponent G :=
    Ne.bot_lt fun ht => by
      rw [ht] at h
      apply h
      rw [bot_eq_zero]; rw [Nat.factorization_zero]; rw [Finsupp.zero_app

Depends on / 依赖: Fact.mk, Finsupp, Finsupp.mem_support_iff, Finsupp.zero_apply, Nat.factorization_zero, Ne.bot_lt, bot_eq_zero, bot_lt, eq_or_ne, exponent, exponent_dvd_iff_forall_pow_eq_one, factorization, factorization_zero, hp.o, mem_support_iff, not_forall, orderOf_one, pow_zero, zero_apply
-/
theorem _root_.Nat.Prime.exists_orderOf_eq_pow_factorization_exponent {p : Nat} (hp : p.Prime) :
    exists g : G, orderOf g = p ^ (exponent G).factorization p := by
  have := Fact.mk hp
  rcases eq_or_ne ((exponent G).factorization p) 0 with (h | h)
  · refine ⟨1, by rw [h, pow_zero, orderOf_one]⟩
  have he : 0 < exponent G :=
    Ne.bot_lt fun ht => by
      rw [ht] at h
      apply h
      rw [bot_eq_zero]; rw [Nat.factorization_zero]; rw [Finsupp.zero_apply]
  rw [← Finsupp.mem_support_iff] at h
  obtain ⟨g, hg⟩ : exists g : G, g ^ (exponent G / p) != 1 := by
    suffices key : ¬exponent G ∣ exponent G / p by
      rwa [exponent_dvd_iff_forall_pow_eq_one, not_forall] at key
    exact fun hd =>
      hp.one_lt.not_ge
        ((mul_le_iff_le_one_left he).mp <|
Nat.le_of_dvd he Nat.mul_dvd_of_dvd_div (Nat.dvd_of_mem_primeFactors h) hd)
  obtain ⟨k, hk : exponent G = p ^ _ * k⟩ := Nat.ordProj_dvd _ _
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp h)
  refine ⟨g ^ k, ?_⟩
  rw [ht]
  apply orderOf_eq_prime_pow
  · rwa [hk, mul_comm, ht, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ hp.pos, pow_mul] at hg
  · rw [← Nat.succ_eq_add_one, ← ht, ← pow_mul, mul_comm, ← hk]
    exact pow_exponent_eq_one g

variable {G} in
open Nat in
/-- If two commuting elements `x` and `y` of a monoid have order `n` and `m`, there is an element
of order `lcm n m`. The result actually gives an explicit (computable) element, written as the
product of a power of `x` and a power of `y`. See also the result below if you don't need the
explicit formula. -/
@[to_additive /-- If two commuting elements `x` and `y` of an additive monoid have order `n` and
`m`, there is an element of order `lcm n m`. The result actually gives an explicit (computable)
element, written as the sum of a multiple of `x` and a multiple of `y`. See also the result below
if you don't need the explicit formula. -/]
/--
lemma `_root_.Commute.orderOf_mul_pow_eq_lcm` / 引理 `_root_.Commute.orderOf_mul_pow_eq_lcm`

English:
lemma _root_.Commute.orderOf_mul_pow_eq_lcm
  statement: {x y : G} (h : Commute x y) (hx : orderOf x != 0)
  proof: by
  rw [(h.pow_pow _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
  all_goals iterate 2 rw [orderOf_pow_orderOf_div]; try rw [Coprime]
  all_goals simp [factorizationLCMLeft_mul_factorizationLCMRight, factorizationLCMLeft_dvd_left,
    factorizationLCMRight_dvd_right, coprime_factorizationLCMLeft_fact

中文:
引理 _root_.Commute.orderOf_mul_pow_eq_lcm
  结论: {x y : G} (h : Commute x y) (hx : orderOf x != 0)
  证明: by
  rw [(h.pow_pow _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
  all_goals iterate 2 rw [orderOf_pow_orderOf_div]; try rw [Coprime]
  all_goals simp [factorizationLCMLeft_mul_factorizationLCMRight, factorizationLCMLeft_dvd_left,
    factorizationLCMRight_dvd_right, coprime_factorizationLCMLeft_fact

Depends on / 依赖: Coprime, all_goals, coprime_factorizationLCMLeft_factorizationLCMRight, factorizationLCMLeft_dvd_left, factorizationLCMLeft_mul_factorizationLCMRight, factorizationLCMRight_dvd_right, h.pow_pow, iterate, orderOf_mul_eq_mul_orderOf_of_coprime, orderOf_pow_orderOf_div, pow_pow
-/
lemma _root_.Commute.orderOf_mul_pow_eq_lcm {x y : G} (h : Commute x y) (hx : orderOf x != 0)
    (hy : orderOf y != 0) :
    orderOf (x ^ (orderOf x / (factorizationLCMLeft (orderOf x) (orderOf y))) *
      y ^ (orderOf y / factorizationLCMRight (orderOf x) (orderOf y))) =
      Nat.lcm (orderOf x) (orderOf y) := by
  rw [(h.pow_pow _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
  all_goals iterate 2 rw [orderOf_pow_orderOf_div]; try rw [Coprime]
  all_goals simp [factorizationLCMLeft_mul_factorizationLCMRight, factorizationLCMLeft_dvd_left,
    factorizationLCMRight_dvd_right, coprime_factorizationLCMLeft_factorizationLCMRight, hx, hy]

open Submonoid in
/-- If two commuting elements `x` and `y` of a monoid have order `n` and `m`, then there is an
element of order `lcm n m` that lies in the subgroup generated by `x` and `y`. -/
@[to_additive /-- If two commuting elements `x` and `y` of an additive monoid have order `n` and
`m`, then there is an element of order `lcm n m` that lies in the additive subgroup generated by `x`
and `y`. -/]
/--
theorem `_root_.Commute.exists_orderOf_eq_lcm` / 定理 `_root_.Commute.exists_orderOf_eq_lcm`

English:
theorem _root_.Commute.exists_orderOf_eq_lcm
  given: {x y : G} (h : Commute x y)
  proof: by
  by_cases hx : orderOf x = 0 <;> by_cases hy : orderOf y = 0
  · exact ⟨x, subset_closure (by simp), by simp [hx]⟩
  · exact ⟨x, subset_closure (by simp), by simp [hx]⟩
  · exact ⟨y, subset_closure (by simp), by simp [hy]⟩
  · exact ⟨_, mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (su

中文:
定理 _root_.Commute.exists_orderOf_eq_lcm
  条件: {x y : G} (h : Commute x y)
  证明: by
  by_cases hx : orderOf x = 0 <;> by_cases hy : orderOf y = 0
  · exact ⟨x, subset_closure (by simp), by simp [hx]⟩
  · exact ⟨x, subset_closure (by simp), by simp [hx]⟩
  · exact ⟨y, subset_closure (by simp), by simp [hy]⟩
  · exact ⟨_, mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (su

Depends on / 依赖: h.orderOf_mul_pow_eq_lcm, mul_mem, orderOf, orderOf_mul_pow_eq_lcm, pow_mem, subset_closure
-/
theorem _root_.Commute.exists_orderOf_eq_lcm {x y : G} (h : Commute x y) :
    exists z in closure {x, y}, orderOf z = Nat.lcm (orderOf x) (orderOf y) := by
  by_cases hx : orderOf x = 0 <;> by_cases hy : orderOf y = 0
  · exact ⟨x, subset_closure (by simp), by simp [hx]⟩
  · exact ⟨x, subset_closure (by simp), by simp [hx]⟩
  · exact ⟨y, subset_closure (by simp), by simp [hy]⟩
  · exact ⟨_, mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _),
      h.orderOf_mul_pow_eq_lcm hx hy⟩

/-- A nontrivial monoid has prime exponent `p` if and only if every non-identity element has
order `p`. -/
@[to_additive]
/--
lemma `exponent_eq_prime_iff` / 引理 `exponent_eq_prime_iff`

English:
lemma exponent_eq_prime_iff
  given: {G : Type*} [Monoid G] [Nontrivial G] {p : Nat} (hp : p.Prime)
  proof: by
  refine ⟨fun hG g hg => ?_, fun h => dvd_antisymm ?_ ?_⟩
  · rw [Ne, ← orderOf_eq_one_iff] at hg
exact Eq.symm (hp.dvd_iff_eq hg).mp hG ▸ Monoid.order_dvd_exponent g
  · rw [exponent_dvd]
    intro g
    by_cases hg : g = 1
    · simp [hg]
    · rw [h g hg]
  · obtain ⟨g, hg⟩ := exists_ne (1 : G

中文:
引理 exponent_eq_prime_iff
  条件: {G : 类型} [Monoid G] [Nontrivial G] {p : 自然数} (hp : p.Prime)
  证明: by
  refine ⟨fun hG g hg => ?_, fun h => dvd_antisymm ?_ ?_⟩
  · rw [Ne, ← orderOf_eq_one_iff] at hg
exact Eq.symm (hp.dvd_iff_eq hg).mp hG ▸ Monoid.order_dvd_exponent g
  · rw [exponent_dvd]
    intro g
    by_cases hg : g = 1
    · simp [hg]
    · rw [h g hg]
  · obtain ⟨g, hg⟩ := exists_ne (1 : G

Depends on / 依赖: Eq.symm, Monoid, Monoid.order_dvd_exponent, dvd_antisymm, dvd_iff_eq, exists_ne, exponent_dvd, hp.dvd_iff_eq, orderOf_eq_one_iff, order_dvd_exponent
-/
lemma exponent_eq_prime_iff {G : Type*} [Monoid G] [Nontrivial G] {p : Nat} (hp : p.Prime) :
    Monoid.exponent G = p ↔ forall g : G, g != 1 -> orderOf g = p := by
  refine ⟨fun hG g hg => ?_, fun h => dvd_antisymm ?_ ?_⟩
  · rw [Ne, ← orderOf_eq_one_iff] at hg
exact Eq.symm (hp.dvd_iff_eq hg).mp hG ▸ Monoid.order_dvd_exponent g
  · rw [exponent_dvd]
    intro g
    by_cases hg : g = 1
    · simp [hg]
    · rw [h g hg]
  · obtain ⟨g, hg⟩ := exists_ne (1 : G)
    simpa [h g hg] using Monoid.order_dvd_exponent g

variable {G}

@[to_additive]
/--
theorem `exponent_ne_zero_iff_range_orderOf_finite` / 定理 `exponent_ne_zero_iff_range_orderOf_finite`

English:
theorem exponent_ne_zero_iff_range_orderOf_finite
  given: (h : forall g : G, 0 < orderOf g)
  proof: by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · by_contra h
    obtain ⟨m, ⟨t, rfl⟩, het⟩ := Set.Infinite.exists_gt h (exponent G)
    exact pow_ne_one_of_lt_orderOf he het (pow_exponent_eq_one t)
  · lift Set.range (orderOf (G := G)) to Finset Nat using he with t ht
    have htpos : 0 < t.prod id := b

中文:
定理 exponent_ne_zero_iff_range_orderOf_finite
  条件: (h : 对任意 g : G, 0 < orderOf g)
  证明: by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · by_contra h
    obtain ⟨m, ⟨t, rfl⟩, het⟩ := Set.Infinite.exists_gt h (exponent G)
    exact pow_ne_one_of_lt_orderOf he het (pow_exponent_eq_one t)
  · lift Set.range (orderOf (G := G)) to Finset Nat using he with t ht
    have htpos : 0 < t.prod id := b

Depends on / 依赖: Finset, Finset.mem_coe, Finset.prod_pos, Infinite, Set.Infinite.exists_gt, Set.range, exists_gt, exponen, exponent, htpos.ne, mem_coe, orderOf, pow_exponent_eq_one, pow_ne_one_of_lt_orderOf, prod_pos, t.prod, zero_dvd_iff
-/
theorem exponent_ne_zero_iff_range_orderOf_finite (h : forall g : G, 0 < orderOf g) :
    exponent G != 0 ↔ (Set.range (orderOf : G -> Nat)).Finite := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · by_contra h
    obtain ⟨m, ⟨t, rfl⟩, het⟩ := Set.Infinite.exists_gt h (exponent G)
    exact pow_ne_one_of_lt_orderOf he het (pow_exponent_eq_one t)
  · lift Set.range (orderOf (G := G)) to Finset Nat using he with t ht
    have htpos : 0 < t.prod id := by
      refine Finset.prod_pos fun a ha => ?_
      rw [← Finset.mem_coe]; rw [ht] at ha
      obtain ⟨k, rfl⟩ := ha
      exact h k
    suffices exponent G ∣ t.prod id by
      intro h
      rw [h]; rw [zero_dvd_iff] at this
      exact htpos.ne' this
    rw [exponent_dvd]
    intro g
    apply Finset.dvd_prod_of_mem id (?_ : orderOf g in _)
    rw [← Finset.mem_coe]; rw [ht]
    exact Set.mem_range_self g

@[to_additive]
/--
theorem `exponent_eq_zero_iff_range_orderOf_infinite` / 定理 `exponent_eq_zero_iff_range_orderOf_infinite`

English:
theorem exponent_eq_zero_iff_range_orderOf_infinite
  given: (h : forall g : G, 0 < orderOf g)
  proof: by
  have := exponent_ne_zero_iff_range_orderOf_finite h
  rwa [Ne, not_iff_comm, Iff.comm] at this

@[to_additive]

中文:
定理 exponent_eq_zero_iff_range_orderOf_infinite
  条件: (h : 对任意 g : G, 0 < orderOf g)
  证明: by
  have := exponent_ne_zero_iff_range_orderOf_finite h
  rwa [Ne, not_iff_comm, Iff.comm] at this

@[to_additive]

Depends on / 依赖: Iff.comm, exponent_ne_zero_iff_range_orderOf_finite, not_iff_comm
-/
theorem exponent_eq_zero_iff_range_orderOf_infinite (h : forall g : G, 0 < orderOf g) :
    exponent G = 0 ↔ (Set.range (orderOf : G -> Nat)).Infinite := by
  have := exponent_ne_zero_iff_range_orderOf_finite h
  rwa [Ne, not_iff_comm, Iff.comm] at this

@[to_additive]
/--
theorem `lcm_orderOf_eq_exponent` / 定理 `lcm_orderOf_eq_exponent`

English:
theorem lcm_orderOf_eq_exponent
  given: [Fintype G]
  statement: (Finset.univ : Finset G).lcm orderOf = exponent G
  proof: Nat.dvd_antisymm
    (lcm_orderOf_dvd_exponent G)
    (exponent_dvd.mpr fun g => Finset.dvd_lcm (Finset.mem_univ g))

中文:
定理 lcm_orderOf_eq_exponent
  条件: [Fintype G]
  结论: (Finset.univ : Finset G).lcm orderOf = exponent G
  证明: Nat.dvd_antisymm
    (lcm_orderOf_dvd_exponent G)
    (exponent_dvd.mpr fun g => Finset.dvd_lcm (Finset.mem_univ g))

Depends on / 依赖: Finset, Finset.dvd_lcm, Finset.mem_univ, Nat.dvd_antisymm, dvd_antisymm, dvd_lcm, exponent_dvd, exponent_dvd.mpr, lcm_orderOf_dvd_exponent, mem_univ
-/
theorem lcm_orderOf_eq_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderOf = exponent G :=
  Nat.dvd_antisymm
    (lcm_orderOf_dvd_exponent G)
    (exponent_dvd.mpr fun g => Finset.dvd_lcm (Finset.mem_univ g))

variable {H : Type*} [Monoid H]

/--
If there exists an injective, multiplication-preserving map from `G` to `H`,
then the exponent of `G` divides the exponent of `H`.
-/
@[to_additive /-- If there exists an injective, addition-preserving map from `G` to `H`,
then the exponent of `G` divides the exponent of `H`. -/]
/--
theorem `exponent_dvd_of_monoidHom` / 定理 `exponent_dvd_of_monoidHom`

English:
theorem exponent_dvd_of_monoidHom
  given: (e : G ->* H) (e_inj : Function.Injective e)
  proof: exponent_dvd_of_forall_pow_eq_one fun g => e_inj (by
    rw [map_pow]; rw [pow_exponent_eq_one]; rw [map_one])

中文:
定理 exponent_dvd_of_monoidHom
  条件: (e : G ->* H) (e_inj : Function.Injective e)
  证明: exponent_dvd_of_forall_pow_eq_one fun g => e_inj (by
    rw [map_pow]; rw [pow_exponent_eq_one]; rw [map_one])

Depends on / 依赖: e_inj, exponent_dvd_of_forall_pow_eq_one, map_one, map_pow, pow_exponent_eq_one
-/
theorem exponent_dvd_of_monoidHom (e : G ->* H) (e_inj : Function.Injective e) :
    Monoid.exponent G ∣ Monoid.exponent H :=
  exponent_dvd_of_forall_pow_eq_one fun g => e_inj (by
    rw [map_pow]; rw [pow_exponent_eq_one]; rw [map_one])

/--
The exponent of a submonoid `H ≤ G` divides the exponent of `G`.
-/
@[to_additive /-- The exponent of an additive submonoid `H ≤ G` divides the exponent of `G`. -/]
/--
theorem `exponent_submonoid_dvd` / 定理 `exponent_submonoid_dvd`

English:
theorem exponent_submonoid_dvd
  given: (H : Submonoid G)
  proof: Monoid.exponent_dvd_of_monoidHom H.subtype H.subtype_injective

中文:
定理 exponent_submonoid_dvd
  条件: (H : Submonoid G)
  证明: Monoid.exponent_dvd_of_monoidHom H.subtype H.subtype_injective

Depends on / 依赖: H.subtype, H.subtype_injective, Monoid, Monoid.exponent_dvd_of_monoidHom, exponent_dvd_of_monoidHom, subtype, subtype_injective
-/
theorem exponent_submonoid_dvd (H : Submonoid G) :
    Monoid.exponent H ∣ Monoid.exponent G :=
  Monoid.exponent_dvd_of_monoidHom H.subtype H.subtype_injective

/--
If there exists a multiplication-preserving equivalence between `G` and `H`,
then the exponent of `G` is equal to the exponent of `H`.
-/
@[to_additive /-- If there exists an addition-preserving equivalence between `G` and `H`,
then the exponent of `G` is equal to the exponent of `H`. -/]
/--
theorem `exponent_eq_of_mulEquiv` / 定理 `exponent_eq_of_mulEquiv`

English:
theorem exponent_eq_of_mulEquiv
  given: (e : G ≃* H)
  statement: Monoid.exponent G = Monoid.exponent H
  proof: Nat.dvd_antisymm
    (exponent_dvd_of_monoidHom e e.injective)
    (exponent_dvd_of_monoidHom e.symm e.symm.injective)

中文:
定理 exponent_eq_of_mulEquiv
  条件: (e : G ≃* H)
  结论: Monoid.exponent G = Monoid.exponent H
  证明: Nat.dvd_antisymm
    (exponent_dvd_of_monoidHom e e.injective)
    (exponent_dvd_of_monoidHom e.symm e.symm.injective)

Depends on / 依赖: Nat.dvd_antisymm, dvd_antisymm, e.injective, e.symm, e.symm.injective, exponent_dvd_of_monoidHom, injective
-/
theorem exponent_eq_of_mulEquiv (e : G ≃* H) : Monoid.exponent G = Monoid.exponent H :=
  Nat.dvd_antisymm
    (exponent_dvd_of_monoidHom e e.injective)
    (exponent_dvd_of_monoidHom e.symm e.symm.injective)

end Monoid

section Submonoid

variable [Monoid G]

variable (G) in
@[to_additive (attr := simp)]
/--
theorem `_root_.Submonoid.exponent_top` / 定理 `_root_.Submonoid.exponent_top`

English:
theorem _root_.Submonoid.exponent_top
  proof: exponent_eq_of_mulEquiv Submonoid.topEquiv

@[to_additive]

中文:
定理 _root_.Submonoid.exponent_top
  证明: exponent_eq_of_mulEquiv Submonoid.topEquiv

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.topEquiv, exponent_eq_of_mulEquiv, topEquiv
-/
theorem _root_.Submonoid.exponent_top :
    Monoid.exponent (⊤ : Submonoid G) = Monoid.exponent G :=
  exponent_eq_of_mulEquiv Submonoid.topEquiv

@[to_additive]
/--
theorem `_root_.Submonoid.pow_exponent_eq_one` / 定理 `_root_.Submonoid.pow_exponent_eq_one`

English:
theorem _root_.Submonoid.pow_exponent_eq_one
  given: {S : Submonoid G} {g : G} (g_in_s : g in S)
  proof: by
  have := Monoid.pow_exponent_eq_one (⟨g, g_in_s⟩ : S)
  rwa [SubmonoidClass.mk_pow, ← OneMemClass.coe_eq_one] at this

中文:
定理 _root_.Submonoid.pow_exponent_eq_one
  条件: {S : Submonoid G} {g : G} (g_in_s : g in S)
  证明: by
  have := Monoid.pow_exponent_eq_one (⟨g, g_in_s⟩ : S)
  rwa [SubmonoidClass.mk_pow, ← OneMemClass.coe_eq_one] at this

Depends on / 依赖: Monoid, Monoid.pow_exponent_eq_one, OneMemClass, OneMemClass.coe_eq_one, SubmonoidClass, SubmonoidClass.mk_pow, coe_eq_one, g_in_s, mk_pow, pow_exponent_eq_one
-/
theorem _root_.Submonoid.pow_exponent_eq_one {S : Submonoid G} {g : G} (g_in_s : g in S) :
    g ^ (Monoid.exponent S) = 1 := by
  have := Monoid.pow_exponent_eq_one (⟨g, g_in_s⟩ : S)
  rwa [SubmonoidClass.mk_pow, ← OneMemClass.coe_eq_one] at this

end Submonoid

section LeftCancelMonoid

variable [LeftCancelMonoid G] [Finite G]

@[to_additive]
/--
theorem `ExponentExists.of_finite` / 定理 `ExponentExists.of_finite`

English:
theorem ExponentExists.of_finite
  statement: ExponentExists G
  proof: by
  let _inst := Fintype.ofFinite G
  simp only [Monoid.ExponentExists]
  refine ⟨(Finset.univ : Finset G).lcm orderOf, ?_, fun g => ?_⟩
  · simpa [pos_iff_ne_zero, Finset.lcm_eq_zero_iff] using fun x => (_root_.orderOf_pos x).ne'
  · rw [← orderOf_dvd_iff_pow_eq_one, lcm_orderOf_eq_exponent]
    e

中文:
定理 ExponentExists.of_finite
  结论: ExponentExists G
  证明: by
  let _inst := Fintype.ofFinite G
  simp only [Monoid.ExponentExists]
  refine ⟨(Finset.univ : Finset G).lcm orderOf, ?_, fun g => ?_⟩
  · simpa [pos_iff_ne_zero, Finset.lcm_eq_zero_iff] using fun x => (_root_.orderOf_pos x).ne'
  · rw [← orderOf_dvd_iff_pow_eq_one, lcm_orderOf_eq_exponent]
    e

Depends on / 依赖: ExponentExists, Finset, Finset.lcm_eq_zero_iff, Finset.univ, Fintype, Fintype.ofFinite, Monoid, Monoid.ExponentExists, _inst, _root_, _root_.orderOf_pos, lcm_eq_zero_iff, lcm_orderOf_eq_exponent, ofFinite, orderOf, orderOf_dvd_iff_pow_eq_one, orderOf_pos, order_dvd_exponent, pos_iff_ne_zero
-/
theorem ExponentExists.of_finite : ExponentExists G := by
  let _inst := Fintype.ofFinite G
  simp only [Monoid.ExponentExists]
  refine ⟨(Finset.univ : Finset G).lcm orderOf, ?_, fun g => ?_⟩
  · simpa [pos_iff_ne_zero, Finset.lcm_eq_zero_iff] using fun x => (_root_.orderOf_pos x).ne'
  · rw [← orderOf_dvd_iff_pow_eq_one, lcm_orderOf_eq_exponent]
    exact order_dvd_exponent g

@[to_additive]
/--
theorem `exponent_ne_zero_of_finite` / 定理 `exponent_ne_zero_of_finite`

English:
theorem exponent_ne_zero_of_finite
  statement: exponent G != 0
  proof: ExponentExists.of_finite.exponent_ne_zero

@[to_additive AddMonoid.one_lt_exponent]

中文:
定理 exponent_ne_zero_of_finite
  结论: exponent G != 0
  证明: ExponentExists.of_finite.exponent_ne_zero

@[to_additive AddMonoid.one_lt_exponent]

Depends on / 依赖: ExponentExists, ExponentExists.of_finite.exponent_ne_zero, exponent_ne_zero, of_finite
-/
theorem exponent_ne_zero_of_finite : exponent G != 0 :=
  ExponentExists.of_finite.exponent_ne_zero

@[to_additive AddMonoid.one_lt_exponent]
/--
lemma `one_lt_exponent` / 引理 `one_lt_exponent`

English:
lemma one_lt_exponent
  given: [Nontrivial G]
  statement: 1 < Monoid.exponent G
  proof: by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact ⟨exponent_ne_zero_of_finite, mt exp_eq_one_iff.mp (not_subsingleton G)⟩

@[to_additive]

中文:
引理 one_lt_exponent
  条件: [Nontrivial G]
  结论: 1 < Monoid.exponent G
  证明: by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact ⟨exponent_ne_zero_of_finite, mt exp_eq_one_iff.mp (not_subsingleton G)⟩

@[to_additive]

Depends on / 依赖: Nat.one_lt_iff_ne_zero_and_ne_one, exp_eq_one_iff, exp_eq_one_iff.mp, exponent_ne_zero_of_finite, not_subsingleton, one_lt_iff_ne_zero_and_ne_one
-/
lemma one_lt_exponent [Nontrivial G] : 1 < Monoid.exponent G := by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact ⟨exponent_ne_zero_of_finite, mt exp_eq_one_iff.mp (not_subsingleton G)⟩

@[to_additive]
/--
Instance `neZero_exponent_of_finite` / 实例 `neZero_exponent_of_finite`

English:
instance neZero_exponent_of_finite
  signature: : NeZero Monoid.exponent G
  body: ⟨Monoid.exponent_ne_zero_of_finite⟩

中文:
实例 neZero_exponent_of_finite
  签名: : NeZero Monoid.exponent G
  定义体: ⟨Monoid.exponent_ne_zero_of_finite⟩

Depends on / 依赖: Monoid, Monoid.exponent_ne_zero_of_finite, exponent_ne_zero_of_finite
-/
instance neZero_exponent_of_finite : NeZero Monoid.exponent G :=
  ⟨Monoid.exponent_ne_zero_of_finite⟩

end LeftCancelMonoid

section CommMonoid

variable [CommMonoid G]

@[to_additive]
/--
theorem `exists_orderOf_eq_exponent` / 定理 `exists_orderOf_eq_exponent`

English:
theorem exists_orderOf_eq_exponent
  given: (hG : ExponentExists G)
  statement: exists g : G, orderOf g = exponent G
  proof: by
  have he := hG.exponent_ne_zero
  have hne : (Set.range (orderOf : G -> Nat)).Nonempty := ⟨1, 1, orderOf_one⟩
  have hfin : (Set.range (orderOf : G -> Nat)).Finite := by
    rwa [← exponent_ne_zero_iff_range_orderOf_finite hG.orderOf_pos]
  obtain ⟨t, ht⟩ := hne.csSup_mem hfin
  use t
  apply Na

中文:
定理 exists_orderOf_eq_exponent
  条件: (hG : ExponentExists G)
  结论: 存在 g : G, orderOf g = exponent G
  证明: by
  have he := hG.exponent_ne_zero
  have hne : (Set.range (orderOf : G -> Nat)).Nonempty := ⟨1, 1, orderOf_one⟩
  have hfin : (Set.range (orderOf : G -> Nat)).Finite := by
    rwa [← exponent_ne_zero_iff_range_orderOf_finite hG.orderOf_pos]
  obtain ⟨t, ht⟩ := hne.csSup_mem hfin
  use t
  apply Na

Depends on / 依赖: Finite, List.subperm_ext_iff, Nat.dvd_antisymm, Nat.dvd_of_primeFactorsList_subperm, Nat.primeFactorsL, Nat.prime_of_mem_primeFactorsList, Nonempty, Set.range, csSup_mem, dvd_antisymm, dvd_of_primeFactorsList_subperm, exponent_ne_zero, exponent_ne_zero_iff_range_orderOf_finite, hG.exponent_ne_zero, hG.orderOf_pos, hne.csSup_mem, orderOf, orderOf_one, orderOf_pos, order_dvd_exponent
-/
theorem exists_orderOf_eq_exponent (hG : ExponentExists G) : exists g : G, orderOf g = exponent G := by
  have he := hG.exponent_ne_zero
  have hne : (Set.range (orderOf : G -> Nat)).Nonempty := ⟨1, 1, orderOf_one⟩
  have hfin : (Set.range (orderOf : G -> Nat)).Finite := by
    rwa [← exponent_ne_zero_iff_range_orderOf_finite hG.orderOf_pos]
  obtain ⟨t, ht⟩ := hne.csSup_mem hfin
  use t
  apply Nat.dvd_antisymm (order_dvd_exponent _)
  refine Nat.dvd_of_primeFactorsList_subperm he ?_
  rw [List.subperm_ext_iff]
  by_contra! ⟨p, hp, hpe⟩
  replace hp := Nat.prime_of_mem_primeFactorsList hp
  simp only [Nat.primeFactorsList_count_eq] at hpe
  set k := (orderOf t).factorization p with hk
  obtain ⟨g, hg⟩ := hp.exists_orderOf_eq_pow_factorization_exponent G
  suffices orderOf t < orderOf (t ^ p ^ k * g) by
    rw [ht] at this
    exact this.not_ge (le_csSup hfin.bddAbove <| Set.mem_range_self _)
  have hpk : p ^ k ∣ orderOf t := Nat.ordProj_dvd _ _
  have hpk' : orderOf (t ^ p ^ k) = orderOf t / p ^ k := by
    rw [orderOf_pow' t (pow_ne_zero k hp.ne_zero)]; rw [Nat.gcd_eq_right hpk]
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_lt hpe
  have hcoprime : (orderOf (t ^ p ^ k)).Coprime (orderOf g) := by
    rw [hg]; rw [Nat.coprime_pow_right_iff (pos_of_gt hpe)]; rw [Nat.coprime_comm]
    apply Or.resolve_right (Nat.coprime_or_dvd_of_prime hp _)
    nth_rw 1 [← pow_one p]
    have : 1 = (Nat.factorization (orderOf (t ^ p ^ k))) p + 1 := by
      rw [hpk']; rw [Nat.factorization_div hpk]
      simp [k, hp]
    rw [this]
    -- Porting note: convert made to_additive complain
    exact Nat.pow_succ_factorization_not_dvd (hG.orderOf_pos <| t ^ p ^ k).ne' hp
  rw [(Commute.all _ g).orderOf_mul_eq_mul_orderOf_of_coprime hcoprime]; rw [hpk']; rw [hg]; rw [ha]; rw [hk]; rw [pow_add]; rw [pow_add]; rw [pow_one]; rw [← mul_assoc]; rw [← mul_assoc]; rw [Nat.div_mul_cancel]; rw [mul_assoc]; rw [lt_mul_iff_one_lt_right hG.orderOf_pos t]; rw [← pow_succ]
  · exact one_lt_pow₀ hp.one_lt a.succ_ne_zero
  · exact hpk

@[to_additive]
/--
theorem `exponent_eq_iSup_orderOf` / 定理 `exponent_eq_iSup_orderOf`

English:
theorem exponent_eq_iSup_orderOf
  given: (h : forall g : G, 0 < orderOf g)
  proof: by
  rw [iSup]
  by_cases ExponentExists G
  case neg he =>
    rw [← exponent_eq_zero_iff] at he
    rw [he]; rw [Set.Infinite.Nat.sSup_eq_zero <| (exponent_eq_zero_iff_range_orderOf_infinite h).1 he]
  case pos he =>
    rw [csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.range_nonempty _)]
    

中文:
定理 exponent_eq_iSup_orderOf
  条件: (h : 对任意 g : G, 0 < orderOf g)
  证明: by
  rw [iSup]
  by_cases ExponentExists G
  case neg he =>
    rw [← exponent_eq_zero_iff] at he
    rw [he]; rw [Set.Infinite.Nat.sSup_eq_zero <| (exponent_eq_zero_iff_range_orderOf_infinite h).1 he]
  case pos he =>
    rw [csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.range_nonempty _)]
    

Depends on / 依赖: ExponentExists, Infinite, Set.Infinite.Nat.sSup_eq_zero, Set.mem_range, Set.range_nonempty, csSup_eq_of_forall_le_of_forall_lt_exists_gt, exists_exists_eq_and, exists_orderOf_eq_exponent, exponent_eq_zero_iff, exponent_eq_zero_iff_range_orderOf_infinite, forall_apply_eq_imp_iff, forall_exists_index, mem_range, orderOf_le_exponent, range_nonempty, sSup_eq_zero, simp_rw
-/
theorem exponent_eq_iSup_orderOf (h : forall g : G, 0 < orderOf g) :
    exponent G = ⨆ g : G, orderOf g := by
  rw [iSup]
  by_cases ExponentExists G
  case neg he =>
    rw [← exponent_eq_zero_iff] at he
    rw [he]; rw [Set.Infinite.Nat.sSup_eq_zero <| (exponent_eq_zero_iff_range_orderOf_infinite h).1 he]
  case pos he =>
    rw [csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.range_nonempty _)]
    · simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      exact orderOf_le_exponent he
    intro x hx
    obtain ⟨g, hg⟩ := exists_orderOf_eq_exponent he
    rw [← hg] at hx
    simp_rw [Set.mem_range, exists_exists_eq_and]
    exact ⟨g, hx⟩

open scoped Classical in
@[to_additive]
/--
theorem `exponent_eq_iSup_orderOf'` / 定理 `exponent_eq_iSup_orderOf'`

English:
theorem exponent_eq_iSup_orderOf'
  proof: by
  split_ifs with h
  · obtain ⟨g, hg⟩ := h
    exact exponent_eq_zero_of_order_zero hg
  · have := not_exists.mp h
exact exponent_eq_iSup_orderOf fun g => Ne.bot_lt this g

中文:
定理 exponent_eq_iSup_orderOf'
  证明: by
  split_ifs with h
  · obtain ⟨g, hg⟩ := h
    exact exponent_eq_zero_of_order_zero hg
  · have := not_exists.mp h
exact exponent_eq_iSup_orderOf fun g => Ne.bot_lt this g

Depends on / 依赖: Ne.bot_lt, bot_lt, exponent_eq_iSup_orderOf, exponent_eq_zero_of_order_zero, not_exists, not_exists.mp, split_ifs
-/
theorem exponent_eq_iSup_orderOf' :
    exponent G = if exists g : G, orderOf g = 0 then 0 else ⨆ g : G, orderOf g := by
  split_ifs with h
  · obtain ⟨g, hg⟩ := h
    exact exponent_eq_zero_of_order_zero hg
  · have := not_exists.mp h
exact exponent_eq_iSup_orderOf fun g => Ne.bot_lt this g

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid G]

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `exponent_eq_max'_orderOf` / 定理 `exponent_eq_max'_orderOf`

English:
theorem exponent_eq_max'_orderOf
  given: [Fintype G]
  proof: by
  rw [← Finset.Nonempty.csSup_eq_max']; rw [Finset.coe_image]; rw [Finset.coe_univ]; rw [Set.image_univ]; rw [← iSup]
  exact exponent_eq_iSup_orderOf orderOf_pos

中文:
定理 exponent_eq_max'_orderOf
  条件: [Fintype G]
  证明: by
  rw [← Finset.Nonempty.csSup_eq_max']; rw [Finset.coe_image]; rw [Finset.coe_univ]; rw [Set.image_univ]; rw [← iSup]
  exact exponent_eq_iSup_orderOf orderOf_pos

Depends on / 依赖: Finset, Finset.Nonempty.csSup_eq_max, Finset.coe_image, Finset.coe_univ, Nonempty, Set.image_univ, coe_image, coe_univ, csSup_eq_max, exponent_eq_iSup_orderOf, image_univ, orderOf_pos
-/
theorem exponent_eq_max'_orderOf [Fintype G] :
    exponent G = ((@Finset.univ G _).image orderOf).max' ⟨1, by simp⟩ := by
  rw [← Finset.Nonempty.csSup_eq_max']; rw [Finset.coe_image]; rw [Finset.coe_univ]; rw [Set.image_univ]; rw [← iSup]
  exact exponent_eq_iSup_orderOf orderOf_pos

end CancelCommMonoid

end Monoid

section Group

variable [Group G] {n m : Int}

@[to_additive]
/--
theorem `Group.exponent_dvd_card` / 定理 `Group.exponent_dvd_card`

English:
theorem Group.exponent_dvd_card
  given: [Fintype G]
  statement: Monoid.exponent G ∣ Fintype.card G
  proof: Monoid.exponent_dvd.mpr fun _ => orderOf_dvd_card

@[to_additive]

中文:
定理 Group.exponent_dvd_card
  条件: [Fintype G]
  结论: Monoid.exponent G ∣ Fintype.card G
  证明: Monoid.exponent_dvd.mpr fun _ => orderOf_dvd_card

@[to_additive]

Depends on / 依赖: Monoid, Monoid.exponent_dvd.mpr, exponent_dvd, orderOf_dvd_card
-/
theorem Group.exponent_dvd_card [Fintype G] : Monoid.exponent G ∣ Fintype.card G :=
Monoid.exponent_dvd.mpr fun _ => orderOf_dvd_card

@[to_additive]
/--
theorem `Group.exponent_dvd_nat_card` / 定理 `Group.exponent_dvd_nat_card`

English:
theorem Group.exponent_dvd_nat_card
  statement: Monoid.exponent G ∣ Nat.card G
  proof: Monoid.exponent_dvd.mpr orderOf_dvd_natCard

@[to_additive]

中文:
定理 Group.exponent_dvd_nat_card
  结论: Monoid.exponent G ∣ 自然数.card G
  证明: Monoid.exponent_dvd.mpr orderOf_dvd_natCard

@[to_additive]

Depends on / 依赖: Monoid, Monoid.exponent_dvd.mpr, exponent_dvd, orderOf_dvd_natCard
-/
theorem Group.exponent_dvd_nat_card : Monoid.exponent G ∣ Nat.card G :=
  Monoid.exponent_dvd.mpr orderOf_dvd_natCard

@[to_additive]
/--
theorem `Subgroup.exponent_toSubmonoid` / 定理 `Subgroup.exponent_toSubmonoid`

English:
theorem Subgroup.exponent_toSubmonoid
  given: (H : Subgroup G)
  proof: Monoid.exponent_eq_of_mulEquiv (MulEquiv.subgroupCongr rfl)

@[to_additive (attr := simp)]

中文:
定理 Subgroup.exponent_toSubmonoid
  条件: (H : Subgroup G)
  证明: Monoid.exponent_eq_of_mulEquiv (MulEquiv.subgroupCongr rfl)

@[to_additive (attr := simp)]

Depends on / 依赖: Monoid, Monoid.exponent_eq_of_mulEquiv, MulEquiv, MulEquiv.subgroupCongr, exponent_eq_of_mulEquiv, subgroupCongr
-/
theorem Subgroup.exponent_toSubmonoid (H : Subgroup G) :
    Monoid.exponent H.toSubmonoid = Monoid.exponent H :=
  Monoid.exponent_eq_of_mulEquiv (MulEquiv.subgroupCongr rfl)

@[to_additive (attr := simp)]
/--
theorem `Subgroup.exponent_top` / 定理 `Subgroup.exponent_top`

English:
theorem Subgroup.exponent_top
  statement: Monoid.exponent (⊤ : Subgroup G) = Monoid.exponent G
  proof: Monoid.exponent_eq_of_mulEquiv topEquiv

@[to_additive]

中文:
定理 Subgroup.exponent_top
  结论: Monoid.exponent (⊤ : Subgroup G) = Monoid.exponent G
  证明: Monoid.exponent_eq_of_mulEquiv topEquiv

@[to_additive]

Depends on / 依赖: Monoid, Monoid.exponent_eq_of_mulEquiv, exponent_eq_of_mulEquiv, topEquiv
-/
theorem Subgroup.exponent_top : Monoid.exponent (⊤ : Subgroup G) = Monoid.exponent G :=
  Monoid.exponent_eq_of_mulEquiv topEquiv

@[to_additive]
/--
theorem `Subgroup.pow_exponent_eq_one` / 定理 `Subgroup.pow_exponent_eq_one`

English:
theorem Subgroup.pow_exponent_eq_one
  given: {H : Subgroup G} {g : G} (g_in_H : g in H)
  proof: exponent_toSubmonoid H ▸ Submonoid.pow_exponent_eq_one g_in_H

@[to_additive]

中文:
定理 Subgroup.pow_exponent_eq_one
  条件: {H : Subgroup G} {g : G} (g_in_H : g in H)
  证明: exponent_toSubmonoid H ▸ Submonoid.pow_exponent_eq_one g_in_H

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.pow_exponent_eq_one, exponent_toSubmonoid, g_in_H, pow_exponent_eq_one
-/
theorem Subgroup.pow_exponent_eq_one {H : Subgroup G} {g : G} (g_in_H : g in H) :
    g ^ Monoid.exponent H = 1 := exponent_toSubmonoid H ▸ Submonoid.pow_exponent_eq_one g_in_H

@[to_additive]
/--
theorem `Group.exponent_dvd_iff_forall_zpow_eq_one` / 定理 `Group.exponent_dvd_iff_forall_zpow_eq_one`

English:
theorem Group.exponent_dvd_iff_forall_zpow_eq_one
  proof: by
  simp_rw [Int.natCast_dvd, Monoid.exponent_dvd_iff_forall_pow_eq_one, pow_natAbs_eq_one]

@[to_additive]

中文:
定理 Group.exponent_dvd_iff_forall_zpow_eq_one
  证明: by
  simp_rw [Int.natCast_dvd, Monoid.exponent_dvd_iff_forall_pow_eq_one, pow_natAbs_eq_one]

@[to_additive]

Depends on / 依赖: Int.natCast_dvd, Monoid, Monoid.exponent_dvd_iff_forall_pow_eq_one, exponent_dvd_iff_forall_pow_eq_one, natCast_dvd, pow_natAbs_eq_one, simp_rw
-/
theorem Group.exponent_dvd_iff_forall_zpow_eq_one :
    (Monoid.exponent G : Int) ∣ n ↔ forall g : G, g ^ n = 1 := by
  simp_rw [Int.natCast_dvd, Monoid.exponent_dvd_iff_forall_pow_eq_one, pow_natAbs_eq_one]

@[to_additive]
/--
theorem `Group.exponent_dvd_sub_iff_zpow_eq_zpow` / 定理 `Group.exponent_dvd_sub_iff_zpow_eq_zpow`

English:
theorem Group.exponent_dvd_sub_iff_zpow_eq_zpow
  proof: by
  simp_rw [Group.exponent_dvd_iff_forall_zpow_eq_one, zpow_sub, mul_inv_eq_one]

中文:
定理 Group.exponent_dvd_sub_iff_zpow_eq_zpow
  证明: by
  simp_rw [Group.exponent_dvd_iff_forall_zpow_eq_one, zpow_sub, mul_inv_eq_one]

Depends on / 依赖: Group.exponent_dvd_iff_forall_zpow_eq_one, exponent_dvd_iff_forall_zpow_eq_one, mul_inv_eq_one, simp_rw, zpow_sub
-/
theorem Group.exponent_dvd_sub_iff_zpow_eq_zpow :
    (Monoid.exponent G : Int) ∣ n - m ↔ forall g : G, g ^ n = g ^ m := by
  simp_rw [Group.exponent_dvd_iff_forall_zpow_eq_one, zpow_sub, mul_inv_eq_one]

end Group

section PiProd

open Finset Monoid

@[to_additive]
/--
theorem `Monoid.exponent_pi_eq_zero` / 定理 `Monoid.exponent_pi_eq_zero`

English:
theorem Monoid.exponent_pi_eq_zero
  statement: {ι : Type*} {M : ι -> Type*} [forall i, Monoid (M i)] {j : ι}
  proof: by
  classical
  rw [@exponent_eq_zero_iff]; rw [ExponentExists] at hj ⊢
  push Not at hj ⊢
  peel hj with n hn _
  obtain ⟨m, hm⟩ := this
  refine ⟨Pi.mulSingle j m, fun h => hm ?_⟩
  simpa using congr_fun h j

中文:
定理 Monoid.exponent_pi_eq_zero
  结论: {ι : 类型} {M : ι -> 类型} [对任意 i, Monoid (M i)] {j : ι}
  证明: by
  classical
  rw [@exponent_eq_zero_iff]; rw [ExponentExists] at hj ⊢
  push Not at hj ⊢
  peel hj with n hn _
  obtain ⟨m, hm⟩ := this
  refine ⟨Pi.mulSingle j m, fun h => hm ?_⟩
  simpa using congr_fun h j

Depends on / 依赖: ExponentExists, Pi.mulSingle, classical, congr_fun, exponent_eq_zero_iff, mulSingle
-/
theorem Monoid.exponent_pi_eq_zero {ι : Type*} {M : ι -> Type*} [forall i, Monoid (M i)] {j : ι}
    (hj : exponent (M j) = 0) : exponent ((i : ι) -> M i) = 0 := by
  classical
  rw [@exponent_eq_zero_iff]; rw [ExponentExists] at hj ⊢
  push Not at hj ⊢
  peel hj with n hn _
  obtain ⟨m, hm⟩ := this
  refine ⟨Pi.mulSingle j m, fun h => hm ?_⟩
  simpa using congr_fun h j

/-- If `f : M₁ →⋆ M₂` is surjective, then the exponent of `M₂` divides the exponent of `M₁`. -/
@[to_additive]
/--
theorem `MonoidHom.exponent_dvd` / 定理 `MonoidHom.exponent_dvd`

English:
theorem MonoidHom.exponent_dvd
  statement: {F M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
  proof: by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun m₂ => ?_
  obtain ⟨m₁, rfl⟩ := hf m₂
  rw [← map_pow]; rw [pow_exponent_eq_one]; rw [map_one]

中文:
定理 MonoidHom.exponent_dvd
  结论: {F M₁ M₂ : 类型} [Monoid M₁] [Monoid M₂]
  证明: by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun m₂ => ?_
  obtain ⟨m₁, rfl⟩ := hf m₂
  rw [← map_pow]; rw [pow_exponent_eq_one]; rw [map_one]

Depends on / 依赖: Monoid, Monoid.exponent_dvd_of_forall_pow_eq_one, exponent_dvd_of_forall_pow_eq_one, map_one, map_pow, pow_exponent_eq_one
-/
theorem MonoidHom.exponent_dvd {F M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
    [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂]
    {f : F} (hf : Function.Surjective f) : exponent M₂ ∣ exponent M₁ := by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun m₂ => ?_
  obtain ⟨m₁, rfl⟩ := hf m₂
  rw [← map_pow]; rw [pow_exponent_eq_one]; rw [map_one]

/-- The exponent of finite product of monoids is the `Finset.lcm` of the exponents of the
constituent monoids. -/
@[to_additive /-- The exponent of finite product of additive monoids is the `Finset.lcm` of the
exponents of the constituent additive monoids. -/]
/--
theorem `Monoid.exponent_pi` / 定理 `Monoid.exponent_pi`

English:
theorem Monoid.exponent_pi
  given: {ι : Type*} [Fintype ι] {M : ι -> Type*} [forall i, Monoid (M i)]
  proof: by
  refine dvd_antisymm ?_ ?_
  · refine exponent_dvd_of_forall_pow_eq_one fun m => ?_
    ext i
    rw [Pi.pow_apply]; rw [Pi.one_apply]; rw [← orderOf_dvd_iff_pow_eq_one]
    apply dvd_trans (Monoid.order_dvd_exponent (m i))
    exact Finset.dvd_lcm (mem_univ i)
  · apply Finset.lcm_dvd fun i _ =

中文:
定理 Monoid.exponent_pi
  条件: {ι : 类型} [Fintype ι] {M : ι -> 类型} [对任意 i, Monoid (M i)]
  证明: by
  refine dvd_antisymm ?_ ?_
  · refine exponent_dvd_of_forall_pow_eq_one fun m => ?_
    ext i
    rw [Pi.pow_apply]; rw [Pi.one_apply]; rw [← orderOf_dvd_iff_pow_eq_one]
    apply dvd_trans (Monoid.order_dvd_exponent (m i))
    exact Finset.dvd_lcm (mem_univ i)
  · apply Finset.lcm_dvd fun i _ =

Depends on / 依赖: Finset, Finset.dvd_lcm, Finset.lcm_dvd, Function, Function.surjective_eval, Monoid, Monoid.order_dvd_exponent, MonoidHom, MonoidHom.exponent_dvd, Pi.evalMonoidHom, Pi.one_apply, Pi.pow_apply, dvd_antisymm, dvd_lcm, dvd_trans, evalMonoidHom, exponent_dvd, exponent_dvd_of_forall_pow_eq_one, lcm_dvd, mem_univ
-/
theorem Monoid.exponent_pi {ι : Type*} [Fintype ι] {M : ι -> Type*} [forall i, Monoid (M i)] :
    exponent ((i : ι) -> M i) = lcm univ (exponent <| M ·) := by
  refine dvd_antisymm ?_ ?_
  · refine exponent_dvd_of_forall_pow_eq_one fun m => ?_
    ext i
    rw [Pi.pow_apply]; rw [Pi.one_apply]; rw [← orderOf_dvd_iff_pow_eq_one]
    apply dvd_trans (Monoid.order_dvd_exponent (m i))
    exact Finset.dvd_lcm (mem_univ i)
  · apply Finset.lcm_dvd fun i _ => ?_
    exact MonoidHom.exponent_dvd (f := Pi.evalMonoidHom (M ·) i) (Function.surjective_eval i)

/-- The exponent of product of two monoids is the `lcm` of the exponents of the
individual monoids. -/
@[to_additive AddMonoid.exponent_prod /-- The exponent of product of two additive monoids is the
`lcm` of the exponents of the individual additive monoids. -/]
/--
theorem `Monoid.exponent_prod` / 定理 `Monoid.exponent_prod`

English:
theorem Monoid.exponent_prod
  given: {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
  proof: by
  refine dvd_antisymm ?_ (lcm_dvd ?_ ?_)
  · refine exponent_dvd_of_forall_pow_eq_one fun g => ?_
    ext1
    · rw [Prod.pow_fst, Prod.fst_one, ← orderOf_dvd_iff_pow_eq_one]
exact dvd_trans (Monoid.order_dvd_exponent (g.1)) dvd_lcm_left _ _
    · rw [Prod.pow_snd, Prod.snd_one, ← orderOf_dvd_iff

中文:
定理 Monoid.exponent_prod
  条件: {M₁ M₂ : 类型} [Monoid M₁] [Monoid M₂]
  证明: by
  refine dvd_antisymm ?_ (lcm_dvd ?_ ?_)
  · refine exponent_dvd_of_forall_pow_eq_one fun g => ?_
    ext1
    · rw [Prod.pow_fst, Prod.fst_one, ← orderOf_dvd_iff_pow_eq_one]
exact dvd_trans (Monoid.order_dvd_exponent (g.1)) dvd_lcm_left _ _
    · rw [Prod.pow_snd, Prod.snd_one, ← orderOf_dvd_iff

Depends on / 依赖: Monoid, Monoid.order_dvd_exponent, MonoidHom, MonoidHom.exponent_dvd, MonoidHom.fst, MonoidHom.snd, Prod.fst_one, Prod.fst_surjective, Prod.pow_fst, Prod.pow_snd, Prod.snd_one, dvd_antisymm, dvd_lcm_left, dvd_lcm_right, dvd_trans, exponent_dvd, exponent_dvd_of_forall_pow_eq_one, fst_one, fst_surjective, lcm_dvd
-/
theorem Monoid.exponent_prod {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] :
    exponent (M₁ × M₂) = lcm (exponent M₁) (exponent M₂) := by
  refine dvd_antisymm ?_ (lcm_dvd ?_ ?_)
  · refine exponent_dvd_of_forall_pow_eq_one fun g => ?_
    ext1
    · rw [Prod.pow_fst, Prod.fst_one, ← orderOf_dvd_iff_pow_eq_one]
exact dvd_trans (Monoid.order_dvd_exponent (g.1)) dvd_lcm_left _ _
    · rw [Prod.pow_snd, Prod.snd_one, ← orderOf_dvd_iff_pow_eq_one]
exact dvd_trans (Monoid.order_dvd_exponent (g.2)) dvd_lcm_right _ _
  · exact MonoidHom.exponent_dvd (f := MonoidHom.fst M₁ M₂) Prod.fst_surjective
  · exact MonoidHom.exponent_dvd (f := MonoidHom.snd M₁ M₂) Prod.snd_surjective

end PiProd

/-! ### Properties of monoids with exponent two -/

section ExponentTwo

section Monoid

variable [Monoid G]

@[to_additive]
/--
lemma `orderOf_eq_two_iff` / 引理 `orderOf_eq_two_iff`

English:
lemma orderOf_eq_two_iff
  given: (hG : Monoid.exponent G = 2) {x : G}
  proof: ⟨by rintro hx rfl; norm_num at hx, orderOf_eq_prime (hG ▸ Monoid.pow_exponent_eq_one x)⟩

@[to_additive]

中文:
引理 orderOf_eq_two_iff
  条件: (hG : Monoid.exponent G = 2) {x : G}
  证明: ⟨by rintro hx rfl; norm_num at hx, orderOf_eq_prime (hG ▸ Monoid.pow_exponent_eq_one x)⟩

@[to_additive]

Depends on / 依赖: Monoid, Monoid.pow_exponent_eq_one, orderOf_eq_prime, pow_exponent_eq_one
-/
lemma orderOf_eq_two_iff (hG : Monoid.exponent G = 2) {x : G} :
    orderOf x = 2 ↔ x != 1 :=
  ⟨by rintro hx rfl; norm_num at hx, orderOf_eq_prime (hG ▸ Monoid.pow_exponent_eq_one x)⟩

@[to_additive]
/--
theorem `Commute.of_orderOf_dvd_two` / 定理 `Commute.of_orderOf_dvd_two`

English:
theorem Commute.of_orderOf_dvd_two
  given: [IsCancelMul G] (h : forall g : G, orderOf g ∣ 2) (a b : G)
  proof: by
  simp_rw [orderOf_dvd_iff_pow_eq_one] at h
  rw [commute_iff_eq]; rw [← mul_right_inj a]; rw [← mul_left_inj b]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  calc
    a * (a * b) * b = a ^ 2 * b ^ 2 := by simp

中文:
定理 Commute.of_orderOf_dvd_two
  条件: [IsCancelMul G] (h : 对任意 g : G, orderOf g ∣ 2) (a b : G)
  证明: by
  simp_rw [orderOf_dvd_iff_pow_eq_one] at h
  rw [commute_iff_eq]; rw [← mul_right_inj a]; rw [← mul_left_inj b]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  calc
    a * (a * b) * b = a ^ 2 * b ^ 2 := by simp

Depends on / 依赖: commute_iff_eq, mul_left_inj, mul_right_inj, orderOf_dvd_iff_pow_eq_one, simp_rw
-/
theorem Commute.of_orderOf_dvd_two [IsCancelMul G] (h : forall g : G, orderOf g ∣ 2) (a b : G) :
    Commute a b := by
  simp_rw [orderOf_dvd_iff_pow_eq_one] at h
  rw [commute_iff_eq]; rw [← mul_right_inj a]; rw [← mul_left_inj b]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  calc
    a * (a * b) * b = a ^ 2 * b ^ 2 := by simp [pow_two, mul_assoc]
    _ = 1 := by rw [h, h, mul_one]
    _ = (a * b) ^ 2 := by rw [h]
    _ = a * (b * a) * b := by simp [pow_two, mul_assoc]

/-- In a cancellative monoid of exponent two, all elements commute. -/
@[to_additive]
/--
lemma `mul_comm_of_exponent_two` / 引理 `mul_comm_of_exponent_two`

English:
lemma mul_comm_of_exponent_two
  given: [IsCancelMul G] (hG : Monoid.exponent G = 2) (a b : G)
  proof: Commute.of_orderOf_dvd_two (fun g => hG ▸ Monoid.order_dvd_exponent g) a b

中文:
引理 mul_comm_of_exponent_two
  条件: [IsCancelMul G] (hG : Monoid.exponent G = 2) (a b : G)
  证明: Commute.of_orderOf_dvd_two (fun g => hG ▸ Monoid.order_dvd_exponent g) a b

Depends on / 依赖: Commute, Commute.of_orderOf_dvd_two, Monoid, Monoid.order_dvd_exponent, of_orderOf_dvd_two, order_dvd_exponent
-/
lemma mul_comm_of_exponent_two [IsCancelMul G] (hG : Monoid.exponent G = 2) (a b : G) :
    a * b = b * a :=
  Commute.of_orderOf_dvd_two (fun g => hG ▸ Monoid.order_dvd_exponent g) a b

/-- Any cancellative monoid of exponent two is abelian. -/
@[to_additive /-- Any additive group of exponent two is abelian. -/]
/--
Definition of `commMonoidOfExponentTwo` / `commMonoidOfExponentTwo` 的定义

English:
abbreviation commMonoidOfExponentTwo
  signature: [IsCancelMul G] (hG : Monoid.exponent G = 2)
  body: mul_comm_of_exponent_two hG

中文:
缩写 commMonoidOfExponentTwo
  签名: [IsCancelMul G] (hG : Monoid.exponent G = 2)
  定义体: mul_comm_of_exponent_two hG

Depends on / 依赖: mul_comm_of_exponent_two
-/
abbrev commMonoidOfExponentTwo [IsCancelMul G] (hG : Monoid.exponent G = 2) : CommMonoid G where
  mul_comm := mul_comm_of_exponent_two hG

end Monoid

section Group

variable [Group G]

/--
If `H` is a normal subgroup of `G`, then the exponent of `G ⧸ H` divides the exponent of `G`.
-/
@[to_additive
/-- If `H` is a normal additive subgroup of `G`, then the exponent of `G ⧸ H` divides the
exponent of `G`. -/]
/--
theorem `Group.exponent_quotient_dvd` / 定理 `Group.exponent_quotient_dvd`

English:
theorem Group.exponent_quotient_dvd
  given: (H : Subgroup G) [H.Normal]
  proof: MonoidHom.exponent_dvd (QuotientGroup.mk'_surjective H)

中文:
定理 Group.exponent_quotient_dvd
  条件: (H : Subgroup G) [H.Normal]
  证明: MonoidHom.exponent_dvd (QuotientGroup.mk'_surjective H)

Depends on / 依赖: MonoidHom, MonoidHom.exponent_dvd, QuotientGroup, QuotientGroup.mk, _surjective, exponent_dvd
-/
theorem Group.exponent_quotient_dvd (H : Subgroup G) [H.Normal] :
    Monoid.exponent (G ⧸ H) ∣ Monoid.exponent G :=
  MonoidHom.exponent_dvd (QuotientGroup.mk'_surjective H)

/-- In a group of exponent two, every element is its own inverse. -/
@[to_additive]
/--
lemma `inv_eq_self_of_exponent_two` / 引理 `inv_eq_self_of_exponent_two`

English:
lemma inv_eq_self_of_exponent_two
  given: (hG : Monoid.exponent G = 2) (x : G)
  proof: inv_eq_of_mul_eq_one_left pow_two (a := x) ▸ hG ▸ Monoid.pow_exponent_eq_one x

中文:
引理 inv_eq_self_of_exponent_two
  条件: (hG : Monoid.exponent G = 2) (x : G)
  证明: inv_eq_of_mul_eq_one_left pow_two (a := x) ▸ hG ▸ Monoid.pow_exponent_eq_one x

Depends on / 依赖: Monoid, Monoid.pow_exponent_eq_one, inv_eq_of_mul_eq_one_left, pow_exponent_eq_one, pow_two
-/
lemma inv_eq_self_of_exponent_two (hG : Monoid.exponent G = 2) (x : G) :
    x⁻¹ = x :=
inv_eq_of_mul_eq_one_left pow_two (a := x) ▸ hG ▸ Monoid.pow_exponent_eq_one x

/-- If an element in a group has order two, then it is its own inverse. -/
@[to_additive]
/--
lemma `inv_eq_self_of_orderOf_eq_two` / 引理 `inv_eq_self_of_orderOf_eq_two`

English:
lemma inv_eq_self_of_orderOf_eq_two
  given: {x : G} (hx : orderOf x = 2)
  proof: inv_eq_of_mul_eq_one_left pow_two (a := x) ▸ hx ▸ pow_orderOf_eq_one x

@[to_additive]

中文:
引理 inv_eq_self_of_orderOf_eq_two
  条件: {x : G} (hx : orderOf x = 2)
  证明: inv_eq_of_mul_eq_one_left pow_two (a := x) ▸ hx ▸ pow_orderOf_eq_one x

@[to_additive]

Depends on / 依赖: inv_eq_of_mul_eq_one_left, pow_orderOf_eq_one, pow_two
-/
lemma inv_eq_self_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) :
    x⁻¹ = x :=
inv_eq_of_mul_eq_one_left pow_two (a := x) ▸ hx ▸ pow_orderOf_eq_one x

@[to_additive]
/--
lemma `mul_notMem_of_orderOf_eq_two` / 引理 `mul_notMem_of_orderOf_eq_two`

English:
lemma mul_notMem_of_orderOf_eq_two
  statement: {x y : G} (hx : orderOf x = 2)
  proof: by
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, mul_eq_left, mul_eq_right,
    mul_eq_one_iff_eq_inv, inv_eq_self_of_orderOf_eq_two hy, not_or]
  aesop

@[to_additive]

中文:
引理 mul_notMem_of_orderOf_eq_two
  结论: {x y : G} (hx : orderOf x = 2)
  证明: by
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, mul_eq_left, mul_eq_right,
    mul_eq_one_iff_eq_inv, inv_eq_self_of_orderOf_eq_two hy, not_or]
  aesop

@[to_additive]

Depends on / 依赖: Set.mem_insert_iff, Set.mem_singleton_iff, inv_eq_self_of_orderOf_eq_two, mem_insert_iff, mem_singleton_iff, mul_eq_left, mul_eq_one_iff_eq_inv, mul_eq_right, not_or
-/
lemma mul_notMem_of_orderOf_eq_two {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : x != y) : x * y ∉ ({x, y, 1} : Set G) := by
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, mul_eq_left, mul_eq_right,
    mul_eq_one_iff_eq_inv, inv_eq_self_of_orderOf_eq_two hy, not_or]
  aesop

@[to_additive]
/--
lemma `mul_notMem_of_exponent_two` / 引理 `mul_notMem_of_exponent_two`

English:
lemma mul_notMem_of_exponent_two
  statement: (h : Monoid.exponent G = 2) {x y : G}
  proof: mul_notMem_of_orderOf_eq_two (orderOf_eq_prime (h ▸ Monoid.pow_exponent_eq_one x) hx)
    (orderOf_eq_prime (h ▸ Monoid.pow_exponent_eq_one y) hy) hxy

中文:
引理 mul_notMem_of_exponent_two
  结论: (h : Monoid.exponent G = 2) {x y : G}
  证明: mul_notMem_of_orderOf_eq_two (orderOf_eq_prime (h ▸ Monoid.pow_exponent_eq_one x) hx)
    (orderOf_eq_prime (h ▸ Monoid.pow_exponent_eq_one y) hy) hxy

Depends on / 依赖: Monoid, Monoid.pow_exponent_eq_one, mul_notMem_of_orderOf_eq_two, orderOf_eq_prime, pow_exponent_eq_one
-/
lemma mul_notMem_of_exponent_two (h : Monoid.exponent G = 2) {x y : G}
    (hx : x != 1) (hy : y != 1) (hxy : x != y) : x * y ∉ ({x, y, 1} : Set G) :=
  mul_notMem_of_orderOf_eq_two (orderOf_eq_prime (h ▸ Monoid.pow_exponent_eq_one x) hx)
    (orderOf_eq_prime (h ▸ Monoid.pow_exponent_eq_one y) hy) hxy

end Group

end ExponentTwo
