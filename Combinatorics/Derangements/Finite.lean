/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.Derangements.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-!
# Derangements on fintypes

This file contains lemmas that describe the cardinality of `derangements α` when `α` is a fintype.

## Main definitions

* `card_derangements_invariant`: A lemma stating that the number of derangements on a type `α`
    depends only on the cardinality of `α`.
* `numDerangements n`: The number of derangements on an n-element set, defined in a computation-
    friendly way.
* `card_derangements_eq_numDerangements`: Proof that `numDerangements` really does compute the
    number of derangements.
* `numDerangements_sum`: A lemma giving an expression for `numDerangements n` in terms of
    factorials.
-/

@[expose] public section


open derangements Equiv Fintype

variable {α : Type*} [DecidableEq α] [Fintype α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (· in derangements α)
  body: fun _ => Fintype.decidableForallFintype

中文:
实例 :
  签名: DecidablePred (· in derangements α)
  定义体: fun _ => Fintype.decidableForallFintype

Depends on / 依赖: Fintype, Fintype.decidableForallFintype, decidableForallFintype
-/
instance : DecidablePred (· in derangements α) := fun _ => Fintype.decidableForallFintype

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (derangements α)
  body: inferInstanceAs Fintype { f : Perm α | forall x : α, f x != x }

中文:
实例 :
  签名: Fintype (derangements α)
  定义体: inferInstanceAs Fintype { f : Perm α | forall x : α, f x != x }

Depends on / 依赖: Fintype
-/
instance : Fintype (derangements α) :=
inferInstanceAs Fintype { f : Perm α | forall x : α, f x != x }


/--
theorem `card_derangements_invariant` / 定理 `card_derangements_invariant`

English:
theorem card_derangements_invariant
  statement: {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
  proof: Fintype.card_congr (Equiv.derangementsCongr <| equivOfCardEq h)

中文:
定理 card_derangements_invariant
  结论: {α β : 类型} [Fintype α] [DecidableEq α] [Fintype β]
  证明: Fintype.card_congr (Equiv.derangementsCongr <| equivOfCardEq h)

Depends on / 依赖: Equiv.derangementsCongr, Fintype, Fintype.card_congr, card_congr, derangementsCongr, equivOfCardEq
-/
theorem card_derangements_invariant {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (h : card α = card β) : card (derangements α) = card (derangements β) :=
  Fintype.card_congr (Equiv.derangementsCongr <| equivOfCardEq h)

/--
theorem `card_derangements_fin_add_two` / 定理 `card_derangements_fin_add_two`

English:
theorem card_derangements_fin_add_two
  given: (n : Nat)
  proof: by
  -- get some basic results about the size of Fin (n+1) plus or minus an element
  have h1 : forall a : Fin (n + 1), card ({a}ᶜ : Set (Fin (n + 1))) = card (Fin n) := by
    intro a
    rw [Fintype.card_compl_set]
    simp
  have h2 : card (Fin (n + 2)) = card (Option (Fin (n + 1))) := by simp on

中文:
定理 card_derangements_fin_add_two
  条件: (n : 自然数)
  证明: by
  -- get some basic results about the size of Fin (n+1) plus or minus an element
  have h1 : forall a : Fin (n + 1), card ({a}ᶜ : Set (Fin (n + 1))) = card (Fin n) := by
    intro a
    rw [Fintype.card_compl_set]
    simp
  have h2 : card (Fin (n + 2)) = card (Option (Fin (n + 1))) := by simp on
-/
theorem card_derangements_fin_add_two (n : Nat) :
    card (derangements (Fin (n + 2))) =
      (n + 1) * card (derangements (Fin n)) + (n + 1) * card (derangements (Fin (n + 1))) := by
  -- get some basic results about the size of Fin (n+1) plus or minus an element
  have h1 : forall a : Fin (n + 1), card ({a}ᶜ : Set (Fin (n + 1))) = card (Fin n) := by
    intro a
    rw [Fintype.card_compl_set]
    simp
  have h2 : card (Fin (n + 2)) = card (Option (Fin (n + 1))) := by simp only [card_fin, card_option]
  -- rewrite the LHS and substitute in our fintype-level equivalence
  simp only [card_derangements_invariant h2,
    card_congr
      (@derangementsRecursionEquiv (Fin (n + 1))
        _), -- push the cardinality through the Σ and ⊕ so that we can use `card_n`
    card_sigma,
    card_sum, card_derangements_invariant (h1 _), Finset.sum_const, nsmul_eq_mul, Finset.card_fin,
    mul_add, Nat.cast_id]

/--
Definition of `numDerangements` / `numDerangements` 的定义

English:
definition numDerangements
  signature: : Nat -> Nat

中文:
定义 numDerangements
  签名: : 自然数 -> 自然数
-/
def numDerangements : Nat -> Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (numDerangements n + numDerangements (n + 1))

@[simp]
/--
theorem `numDerangements_zero` / 定理 `numDerangements_zero`

English:
theorem numDerangements_zero
  statement: numDerangements 0 = 1
  proof: rfl

@[simp]

中文:
定理 numDerangements_zero
  结论: numDerangements 0 = 1
  证明: rfl

@[simp]
-/
theorem numDerangements_zero : numDerangements 0 = 1 :=
  rfl

@[simp]
/--
theorem `numDerangements_one` / 定理 `numDerangements_one`

English:
theorem numDerangements_one
  statement: numDerangements 1 = 0
  proof: rfl

中文:
定理 numDerangements_one
  结论: numDerangements 1 = 0
  证明: rfl
-/
theorem numDerangements_one : numDerangements 1 = 0 :=
  rfl

/--
theorem `numDerangements_add_two` / 定理 `numDerangements_add_two`

English:
theorem numDerangements_add_two
  given: (n : Nat)
  proof: rfl

中文:
定理 numDerangements_add_two
  条件: (n : 自然数)
  证明: rfl
-/
theorem numDerangements_add_two (n : Nat) :
    numDerangements (n + 2) = (n + 1) * (numDerangements n + numDerangements (n + 1)) :=
  rfl

/--
theorem `numDerangements_succ` / 定理 `numDerangements_succ`

English:
theorem numDerangements_succ
  given: (n : Nat)
  proof: by
  induction n with
  | zero => rfl
  | succ n hn =>
    simp only [numDerangements_add_two, hn, pow_succ, Int.natCast_mul, Int.natCast_add]
    ring

中文:
定理 numDerangements_succ
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => rfl
  | succ n hn =>
    simp only [numDerangements_add_two, hn, pow_succ, Int.natCast_mul, Int.natCast_add]
    ring

Depends on / 依赖: Int.natCast_add, Int.natCast_mul, natCast_add, natCast_mul, numDerangements_add_two, pow_succ
-/
theorem numDerangements_succ (n : Nat) :
    (numDerangements (n + 1) : Int) = (n + 1) * (numDerangements n : Int) - (-1) ^ n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    simp only [numDerangements_add_two, hn, pow_succ, Int.natCast_mul, Int.natCast_add]
    ring

/--
theorem `card_derangements_fin_eq_numDerangements` / 定理 `card_derangements_fin_eq_numDerangements`

English:
theorem card_derangements_fin_eq_numDerangements
  given: {n : Nat}
  proof: by
  induction n using Nat.strongRecOn with | ind n hyp => _
  rcases n with _ | _ | n
  -- knock out cases 0 and 1
  · rfl
  · rfl
  -- now we have n ≥ 2. rewrite everything in terms of card_derangements, so that we can use
  -- `card_derangements_fin_add_two`
  rw [numDerangements_add_two]; rw [ca

中文:
定理 card_derangements_fin_eq_numDerangements
  条件: {n : 自然数}
  证明: by
  induction n using Nat.strongRecOn with | ind n hyp => _
  rcases n with _ | _ | n
  -- knock out cases 0 and 1
  · rfl
  · rfl
  -- now we have n ≥ 2. rewrite everything in terms of card_derangements, so that we can use
  -- `card_derangements_fin_add_two`
  rw [numDerangements_add_two]; rw [ca

Depends on / 依赖: Nat.strongRecOn, strongRecOn
-/
theorem card_derangements_fin_eq_numDerangements {n : Nat} :
    card (derangements (Fin n)) = numDerangements n := by
  induction n using Nat.strongRecOn with | ind n hyp => _
  rcases n with _ | _ | n
  -- knock out cases 0 and 1
  · rfl
  · rfl
  -- now we have n ≥ 2. rewrite everything in terms of card_derangements, so that we can use
  -- `card_derangements_fin_add_two`
  rw [numDerangements_add_two]; rw [card_derangements_fin_add_two]; rw [mul_add]; rw [hyp]; rw [hyp] <;> lia

/--
theorem `card_derangements_eq_numDerangements` / 定理 `card_derangements_eq_numDerangements`

English:
theorem card_derangements_eq_numDerangements
  given: (α : Type*) [Fintype α] [DecidableEq α]
  proof: by
  rw [← card_derangements_invariant (card_fin _)]
  exact card_derangements_fin_eq_numDerangements

中文:
定理 card_derangements_eq_numDerangements
  条件: (α : 类型) [Fintype α] [DecidableEq α]
  证明: by
  rw [← card_derangements_invariant (card_fin _)]
  exact card_derangements_fin_eq_numDerangements

Depends on / 依赖: card_derangements_fin_eq_numDerangements, card_derangements_invariant, card_fin
-/
theorem card_derangements_eq_numDerangements (α : Type*) [Fintype α] [DecidableEq α] :
    card (derangements α) = numDerangements (card α) := by
  rw [← card_derangements_invariant (card_fin _)]
  exact card_derangements_fin_eq_numDerangements

/--
theorem `numDerangements_sum` / 定理 `numDerangements_sum`

English:
theorem numDerangements_sum
  given: (n : Nat)
  proof: by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [Finset.sum_range_succ]; rw [numDerangements_succ]; rw [hn]; rw [Finset.mul_sum]; rw [tsub_self]; rw [Nat.ascFactorial_zero]; rw [Int.ofNat_one]; rw [mul_one]; rw [pow_succ']; rw [neg_one_mul]; rw [sub_eq_add_neg]; rw [add_left_inj]; rw [

中文:
定理 numDerangements_sum
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [Finset.sum_range_succ]; rw [numDerangements_succ]; rw [hn]; rw [Finset.mul_sum]; rw [tsub_self]; rw [Nat.ascFactorial_zero]; rw [Int.ofNat_one]; rw [mul_one]; rw [pow_succ']; rw [neg_one_mul]; rw [sub_eq_add_neg]; rw [add_left_inj]; rw [

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_congr, Finset.sum_range_succ, Int.ofNat_one, Nat.ascFactorial_zero, add_left_inj, ascFactorial_zero, mul_one, mul_sum, neg_one_mul, numDerangements_succ, ofNat_one, pow_succ, sub_eq_add_neg, sum_congr, sum_range_succ, tsub_self
-/
theorem numDerangements_sum (n : Nat) :
    (numDerangements n : Int) =
      ∑ k in Finset.range (n + 1), (-1 : Int) ^ k * Nat.ascFactorial (k + 1) (n - k) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [Finset.sum_range_succ]; rw [numDerangements_succ]; rw [hn]; rw [Finset.mul_sum]; rw [tsub_self]; rw [Nat.ascFactorial_zero]; rw [Int.ofNat_one]; rw [mul_one]; rw [pow_succ']; rw [neg_one_mul]; rw [sub_eq_add_neg]; rw [add_left_inj]; rw [Finset.sum_congr rfl]
    -- show that (n + 1) * (-1)^x * asc_fac x (n - x) = (-1)^x * asc_fac x (n.succ - x)
    intro x hx
    have h_le : x <= n := Finset.mem_range_succ_iff.mp hx
    rw [Nat.succ_sub h_le]; rw [Nat.ascFactorial_succ]; rw [add_right_comm]; rw [add_tsub_cancel_of_le h_le]; rw [Int.natCast_mul]; rw [Int.natCast_add]; rw [mul_left_comm]; rw [Nat.cast_one]
