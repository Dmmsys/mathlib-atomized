/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo, Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Eric Rodriguez
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Nat.SuccPred

/-!
# Linear lower bound on the growth of a generating set

This file proves that the growth of a set generating an infinite group is at least linear.
-/

public section

open Subgroup
open scoped Pointwise

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {X : Finset G} {n : Nat}

@[to_additive]
/--
lemma `pow_ssubset_pow_succ_of_pow_ne_closure` / 引理 `pow_ssubset_pow_succ_of_pow_ne_closure`

English:
lemma pow_ssubset_pow_succ_of_pow_ne_closure
  statement: (hX₁ : (1 : G) in X) (hX : X.Nontrivial)
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simpa [ssubset_iff_subset_not_subset, hX₁, -Finset.subset_singleton_iff]
      using! hX.not_subset_singleton
  refine (pow_subset_pow_right hX₁ <| n.le_add_right _).ssubset_of_ne ?_
  contrapose hXclosure with hXn
  rw [← closure_pow (mod_cast hX₁) hn]
  wlog hn₁ : n = 1
  · simp +contextual only [pow_one] at this
    replace hXn d : X ^ (n + d) = X ^ n := by
      induction d with
      | zero => rw [add_zero]
      | succ d hd =>
        rw [pow_add]; rw [pow_one] at hXn
        rw [← add_assoc]; rw [pow_add]; rw [pow_one]; rw [hd]; rw [← hXn]
    exact mod_cast this (one_mem_pow hX₁) (hX.pow hn) one_ne_zero
      (by simp [hXn, ← pow_mul, mul_two]) (by simp)
  subst hn₁
  simp only [ne_eq, one_ne_zero, not_false_eq_true, Nat.reduceAdd, pow_one] at *
  let Xgp : Subgroup G :=
  { carrier := X
    mul_mem' := fun {x y} hx hy => by
      norm_cast at *
      simpa [← hXn, ← sq] using! mul_mem_mul hx hy
    one_mem' := hX₁
    inv_mem' := fun {x} hx => by
      norm_cast at *
      have : x • X subseteq X := by
        simpa [← hXn, add_assoc, ← sq] using! smul_finset_subset_mul (t := X) hx
      have : x • X = X := eq_of_subset_of_card_le this (card_smul_finset ..).ge
      rw [← eq_inv_smul_iff] at this
      rw [this]
      simpa [mem_inv_smul_finset_iff] }
exact subset_closure.antisymm (closure_le Xgp).2 subset_rfl

@[to_additive]

中文:
引理 pow_ssubset_pow_succ_of_pow_ne_closure
  结论: (hX₁ : (1 : G) in X) (hX : X.非平凡)
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simpa [ssubset_iff_subset_not_subset, hX₁, -Finset.subset_singleton_iff]
      using! hX.not_subset_singleton
  refine (pow_subset_pow_right hX₁ <| n.le_add_right _).ssubset_of_ne ?_
  contrapose hXclosure with hXn
  rw [← closure_pow (mod_cast hX₁) hn]
  wlog hn₁ : n = 1
  · simp +contextual only [pow_one] at this
    replace hXn d : X ^ (n + d) = X ^ n := by
      induction d with
      | zero => rw [add_zero]
      | succ d hd =>
        rw [pow_add]; rw [pow_one] at hXn
        rw [← add_assoc]; rw [pow_add]; rw [pow_one]; rw [hd]; rw [← hXn]
    exact mod_cast this (one_mem_pow hX₁) (hX.pow hn) one_ne_zero
      (by simp [hXn, ← pow_mul, mul_two]) (by simp)
  subst hn₁
  simp only [ne_eq, one_ne_zero, not_false_eq_true, Nat.reduceAdd, pow_one] at *
  let Xgp : Subgroup G :=
  { carrier := X
    mul_mem' := fun {x y} hx hy => by
      norm_cast at *
      simpa [← hXn, ← sq] using! mul_mem_mul hx hy
    one_mem' := hX₁
    inv_mem' := fun {x} hx => by
      norm_cast at *
      have : x • X subseteq X := by
        simpa [← hXn, add_assoc, ← sq] using! smul_finset_subset_mul (t := X) hx
      have : x • X = X := eq_of_subset_of_card_le this (card_smul_finset ..).ge
      rw [← eq_inv_smul_iff] at this
      rw [this]
      simpa [mem_inv_smul_finset_iff] }
exact subset_closure.antisymm (closure_le Xgp).2 subset_rfl

@[to_additive]

Depends on / 依赖: Finset, Finset.subset_singleton_iff, add_assoc, add_zero, closure_pow, contextual, contrapose, eq_or_ne, hX.not_subset_singleton, hXclosure, le_add_right, mod_cast, n.le_add_right, not_subset_singleton, pow_add, pow_one, pow_subset_pow_right, replace, ssubset_iff_subset_not_subset, ssubset_of_ne
-/
lemma pow_ssubset_pow_succ_of_pow_ne_closure (hX₁ : (1 : G) in X) (hX : X.Nontrivial)
    (hXclosure : (X ^ n : Set G) != closure (X : Set G)) : X ^ n ⊂ X ^ (n + 1) := by
  obtain rfl | hn := eq_or_ne n 0
  · simpa [ssubset_iff_subset_not_subset, hX₁, -Finset.subset_singleton_iff]
      using! hX.not_subset_singleton
  refine (pow_subset_pow_right hX₁ <| n.le_add_right _).ssubset_of_ne ?_
  contrapose hXclosure with hXn
  rw [← closure_pow (mod_cast hX₁) hn]
  wlog hn₁ : n = 1
  · simp +contextual only [pow_one] at this
    replace hXn d : X ^ (n + d) = X ^ n := by
      induction d with
      | zero => rw [add_zero]
      | succ d hd =>
        rw [pow_add]; rw [pow_one] at hXn
        rw [← add_assoc]; rw [pow_add]; rw [pow_one]; rw [hd]; rw [← hXn]
    exact mod_cast this (one_mem_pow hX₁) (hX.pow hn) one_ne_zero
      (by simp [hXn, ← pow_mul, mul_two]) (by simp)
  subst hn₁
  simp only [ne_eq, one_ne_zero, not_false_eq_true, Nat.reduceAdd, pow_one] at *
  let Xgp : Subgroup G :=
  { carrier := X
    mul_mem' := fun {x y} hx hy => by
      norm_cast at *
      simpa [← hXn, ← sq] using! mul_mem_mul hx hy
    one_mem' := hX₁
    inv_mem' := fun {x} hx => by
      norm_cast at *
      have : x • X subseteq X := by
        simpa [← hXn, add_assoc, ← sq] using! smul_finset_subset_mul (t := X) hx
      have : x • X = X := eq_of_subset_of_card_le this (card_smul_finset ..).ge
      rw [← eq_inv_smul_iff] at this
      rw [this]
      simpa [mem_inv_smul_finset_iff] }
exact subset_closure.antisymm (closure_le Xgp).2 subset_rfl

@[to_additive]
/--
lemma `pow_right_strictMonoOn` / 引理 `pow_right_strictMonoOn`

English:
lemma pow_right_strictMonoOn
  given: (hX₁ : 1 in X) (hX : X.Nontrivial)
  proof: by
  refine strictMonoOn_of_lt_add_one ⟨?_⟩ fun n _ _ hn =>
    pow_ssubset_pow_succ_of_pow_ne_closure hX₁ hX hn
  rintro - - n hn m ⟨-, hmn⟩ hm
  apply hn
  obtain rfl | hm₀ := m.eq_zero_or_pos
  · simp [eq_comm (a := (1 : Set _)), coe_set_eq_one, -Set.subset_singleton_iff,
      hX.coe.not_subset_singleton] at hm
  · calc (X : Set G) ^ (n - 1)
    _ = X ^ (n - m) * X ^ (m - 1) := by rw [← pow_add]; congr 1; lia
    _ = closure (X : Set G) := by rw [hm, Set.pow_mul_subgroupClosure hX.nonempty.to_set]

@[to_additive]

中文:
引理 pow_right_strictMonoOn
  条件: (hX₁ : 1 in X) (hX : X.非平凡)
  证明: by
  refine strictMonoOn_of_lt_add_one ⟨?_⟩ fun n _ _ hn =>
    pow_ssubset_pow_succ_of_pow_ne_closure hX₁ hX hn
  rintro - - n hn m ⟨-, hmn⟩ hm
  apply hn
  obtain rfl | hm₀ := m.eq_zero_or_pos
  · simp [eq_comm (a := (1 : Set _)), coe_set_eq_one, -Set.subset_singleton_iff,
      hX.coe.not_subset_singleton] at hm
  · calc (X : Set G) ^ (n - 1)
    _ = X ^ (n - m) * X ^ (m - 1) := by rw [← pow_add]; congr 1; lia
    _ = closure (X : Set G) := by rw [hm, Set.pow_mul_subgroupClosure hX.nonempty.to_set]

@[to_additive]

Depends on / 依赖: Set.pow_mul_subgroupClosure, Set.subset_singleton_iff, closure, coe_set_eq_one, eq_comm, eq_zero_or_pos, hX.coe.not_subset_singleton, hX.nonempty.to_set, m.eq_zero_or_pos, nonempty, not_subset_singleton, pow_add, pow_mul_subgroupClosure, pow_ssubset_pow_succ_of_pow_ne_closure, strictMonoOn_of_lt_add_one, subset_singleton_iff, to_set
-/
lemma pow_right_strictMonoOn (hX₁ : 1 in X) (hX : X.Nontrivial) :
    StrictMonoOn (fun n => X ^ n) {n | (X ^ (n - 1) : Set G) != closure (X : Set G)} := by
  refine strictMonoOn_of_lt_add_one ⟨?_⟩ fun n _ _ hn =>
    pow_ssubset_pow_succ_of_pow_ne_closure hX₁ hX hn
  rintro - - n hn m ⟨-, hmn⟩ hm
  apply hn
  obtain rfl | hm₀ := m.eq_zero_or_pos
  · simp [eq_comm (a := (1 : Set _)), coe_set_eq_one, -Set.subset_singleton_iff,
      hX.coe.not_subset_singleton] at hm
  · calc (X : Set G) ^ (n - 1)
    _ = X ^ (n - m) * X ^ (m - 1) := by rw [← pow_add]; congr 1; lia
    _ = closure (X : Set G) := by rw [hm, Set.pow_mul_subgroupClosure hX.nonempty.to_set]

@[to_additive]
/--
lemma `pow_right_strictMono` / 引理 `pow_right_strictMono`

English:
lemma pow_right_strictMono
  given: (hX₁ : 1 in X) (hXclosure : (closure (X : Set G) : Set G).Infinite)
  proof: by
  obtain rfl | hX := eq_singleton_or_nontrivial hX₁
  · simp [closure_singleton_one] at hXclosure
  have h n : (X ^ (n - 1) : Set G) != closure (X : Set G) :=
    fun h => by simp [← h, ← coe_pow] at hXclosure
  simpa [h] using pow_right_strictMonoOn hX₁ hX

中文:
引理 pow_right_strictMono
  条件: (hX₁ : 1 in X) (hXclosure : (closure (X : 集合 G) : 集合 G).无限)
  证明: by
  obtain rfl | hX := eq_singleton_or_nontrivial hX₁
  · simp [closure_singleton_one] at hXclosure
  have h n : (X ^ (n - 1) : Set G) != closure (X : Set G) :=
    fun h => by simp [← h, ← coe_pow] at hXclosure
  simpa [h] using pow_right_strictMonoOn hX₁ hX

Depends on / 依赖: closure, closure_singleton_one, coe_pow, eq_singleton_or_nontrivial, hXclosure, pow_right_strictMonoOn
-/
lemma pow_right_strictMono (hX₁ : 1 in X) (hXclosure : (closure (X : Set G) : Set G).Infinite) :
    StrictMono fun n => X ^ n := by
  obtain rfl | hX := eq_singleton_or_nontrivial hX₁
  · simp [closure_singleton_one] at hXclosure
  have h n : (X ^ (n - 1) : Set G) != closure (X : Set G) :=
    fun h => by simp [← h, ← coe_pow] at hXclosure
  simpa [h] using pow_right_strictMonoOn hX₁ hX

/-- The growth of a set generating an infinite group is at least linear. -/
@[to_additive /-- The growth of a set generating an infinite group is at least linear. -/]
/--
lemma `add_one_le_card_pow` / 引理 `add_one_le_card_pow`

English:
lemma add_one_le_card_pow
  given: (hX₁ : 1 in X) (hXclosure : (closure (X : Set G) : Set G).Infinite)

中文:
引理 add_one_le_card_pow
  条件: (hX₁ : 1 in X) (hXclosure : (closure (X : 集合 G) : 集合 G).无限)
-/
lemma add_one_le_card_pow (hX₁ : 1 in X) (hXclosure : (closure (X : Set G) : Set G).Infinite) :
    forall n, n + 1 <= #(X ^ n)
  | 0 => by simp
| n + 1 => (add_one_le_card_pow hX₁ hXclosure _).trans_lt card_lt_card
      pow_right_strictMono hX₁ (by simp [hXclosure]) n.lt_succ_self

end Finset
