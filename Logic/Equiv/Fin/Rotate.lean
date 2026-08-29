/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Lawrence Wu, Jeremy Tan
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Cyclic permutations on `Fin n`

This file defines
* `finRotate`, which corresponds to the cycle `(1, ..., n)` on `Fin n`
* `finCycle`, the permutation that adds a fixed number to each element of `Fin n`
and proves various lemmas about them.
-/

@[expose] public section

open Nat

variable {n : Nat}

/--
Definition of `finRotate` / `finRotate` 的定义

English:
definition finRotate
  signature: : forall n, Equiv.Perm (Fin n)

中文:
定义 finRotate
  签名: : 对任意 n, Equiv.Perm (Fin n)
-/
def finRotate : forall n, Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | n + 1 => finAddFlip.trans (finCongr (Nat.add_comm 1 n))

/--
lemma `finRotate_zero` / 引理 `finRotate_zero`

English:
lemma finRotate_zero
  statement: finRotate 0 = Equiv.refl _
  proof: rfl

中文:
引理 finRotate_zero
  结论: finRotate 0 = Equiv.refl _
  证明: rfl

Depends on / 依赖: complEDS
-/
@[simp] lemma finRotate_zero : finRotate 0 = Equiv.refl _ := rfl

/--
lemma `finRotate_succ` / 引理 `finRotate_succ`

English:
lemma finRotate_succ
  given: (n : Nat)
  proof: rfl

中文:
引理 finRotate_succ
  条件: (n : 自然数)
  证明: rfl

Depends on / 依赖: complEDS
-/
lemma finRotate_succ (n : Nat) :
    finRotate (n + 1) = finAddFlip.trans (finCongr (Nat.add_comm 1 n)) := rfl

/--
theorem `finRotate_of_lt` / 定理 `finRotate_of_lt`

English:
theorem finRotate_of_lt
  given: {k : Nat} (h : k < n)
  proof: by
  ext
  dsimp [finRotate_succ]
  simp [finAddFlip_apply_mk_left h, Nat.add_comm]

中文:
定理 finRotate_of_lt
  条件: {k : 自然数} (h : k < n)
  证明: by
  ext
  dsimp [finRotate_succ]
  simp [finAddFlip_apply_mk_left h, Nat.add_comm]

Depends on / 依赖: Nat.add_comm, Nat.cast_succ, add_comm, cast_succ, complEDS, dif_pos, even_two_mul, finAddFlip_apply_mk_left, finRotate_succ, m.mul_div_cancel_left, mul_div_cancel_left, two_pos
-/
theorem finRotate_of_lt {k : Nat} (h : k < n) :
    finRotate (n + 1) ⟨k, h.trans_le n.le_succ⟩ = ⟨k + 1, Nat.succ_lt_succ h⟩ := by
  ext
  dsimp [finRotate_succ]
  simp [finAddFlip_apply_mk_left h, Nat.add_comm]

/--
theorem `finRotate_last'` / 定理 `finRotate_last'`

English:
theorem finRotate_last'
  statement: finRotate (n + 1) ⟨n, by lia⟩ = ⟨0, Nat.zero_lt_succ _⟩
  proof: by
  dsimp [finRotate_succ]
  rw [finAddFlip_apply_mk_right le_rfl]
  simp

中文:
定理 finRotate_last'
  结论: finRotate (n + 1) ⟨n, by lia⟩ = ⟨0, 自然数.zero_lt_succ _⟩
  证明: by
  dsimp [finRotate_succ]
  rw [finAddFlip_apply_mk_right le_rfl]
  simp

Depends on / 依赖: Nat.mul_add_div, add_assoc, complEDS, dif_neg, finAddFlip_apply_mk_right, finRotate_succ, le_rfl, m.not_even_two_mul_add_one, mul_add_div, not_even_two_mul_add_one, two_pos
-/
theorem finRotate_last' : finRotate (n + 1) ⟨n, by lia⟩ = ⟨0, Nat.zero_lt_succ _⟩ := by
  dsimp [finRotate_succ]
  rw [finAddFlip_apply_mk_right le_rfl]
  simp

/--
theorem `finRotate_last` / 定理 `finRotate_last`

English:
theorem finRotate_last
  statement: finRotate (n + 1) (Fin.last _) = 0
  proof: finRotate_last'

中文:
定理 finRotate_last
  结论: finRotate (n + 1) (Fin.last _) = 0
  证明: finRotate_last'

Depends on / 依赖: finRotate_last
-/
theorem finRotate_last : finRotate (n + 1) (Fin.last _) = 0 :=
  finRotate_last'

/--
theorem `Fin.snoc_eq_cons_rotate` / 定理 `Fin.snoc_eq_cons_rotate`

English:
theorem Fin.snoc_eq_cons_rotate
  given: {α : Type*} (v : Fin n -> α) (a : α)
  proof: by
  ext ⟨i, h⟩
  by_cases h' : i < n
  · rw [finRotate_of_lt h', Fin.snoc, Fin.cons, dif_pos h']
    rfl
  · have h'' : n = i := by
      simp only [not_lt] at h'
      exact (Nat.eq_of_le_of_lt_succ h' h).symm
    subst h''
    rw [finRotate_last']; rw [Fin.snoc]; rw [Fin.cons]; rw [dif_neg (lt_ir

中文:
定理 Fin.snoc_eq_cons_rotate
  条件: {α : 类型} (v : Fin n -> α) (a : α)
  证明: by
  ext ⟨i, h⟩
  by_cases h' : i < n
  · rw [finRotate_of_lt h', Fin.snoc, Fin.cons, dif_pos h']
    rfl
  · have h'' : n = i := by
      simp only [not_lt] at h'
      exact (Nat.eq_of_le_of_lt_succ h' h).symm
    subst h''
    rw [finRotate_last']; rw [Fin.snoc]; rw [Fin.cons]; rw [dif_neg (lt_ir

Depends on / 依赖: Fin.cons, Fin.snoc, Nat.eq_of_le_of_lt_succ, dif_neg, dif_pos, eq_of_le_of_lt_succ, finRotate_last, finRotate_of_lt, lt_irrefl, not_lt
-/
theorem Fin.snoc_eq_cons_rotate {α : Type*} (v : Fin n -> α) (a : α) :
    @Fin.snoc _ (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α) a v (finRotate _ i) := by
  ext ⟨i, h⟩
  by_cases h' : i < n
  · rw [finRotate_of_lt h', Fin.snoc, Fin.cons, dif_pos h']
    rfl
  · have h'' : n = i := by
      simp only [not_lt] at h'
      exact (Nat.eq_of_le_of_lt_succ h' h).symm
    subst h''
    rw [finRotate_last']; rw [Fin.snoc]; rw [Fin.cons]; rw [dif_neg (lt_irrefl _)]
    rfl

@[simp]
/--
theorem `finRotate_one` / 定理 `finRotate_one`

English:
theorem finRotate_one
  statement: finRotate 1 = Equiv.refl _
  proof: Subsingleton.elim _ _

@[simp]

中文:
定理 finRotate_one
  结论: finRotate 1 = Equiv.refl _
  证明: Subsingleton.elim _ _

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem finRotate_one : finRotate 1 = Equiv.refl _ :=
  Subsingleton.elim _ _

@[simp]
/--
theorem `finRotate_apply` / 定理 `finRotate_apply`

English:
theorem finRotate_apply
  given: (i : Fin n)
  statement: haveI
  proof: i.neZero; finRotate n i = i + 1 := by
  match n with
  | 0 => exact i.elim0
  | 1 => exact @Subsingleton.elim (Fin 1) _ _ _
  | n + 2 =>
    obtain rfl | h := Fin.eq_or_lt_of_le i.le_last
    · simp [finRotate_last]
    · cases i
      simp only [Fin.lt_def, Fin.val_last] at h
      simp [finRotate_

中文:
定理 finRotate_apply
  条件: (i : Fin n)
  结论: haveI
  证明: i.neZero; finRotate n i = i + 1 := by
  match n with
  | 0 => exact i.elim0
  | 1 => exact @Subsingleton.elim (Fin 1) _ _ _
  | n + 2 =>
    obtain rfl | h := Fin.eq_or_lt_of_le i.le_last
    · simp [finRotate_last]
    · cases i
      simp only [Fin.lt_def, Fin.val_last] at h
      simp [finRotate_

Depends on / 依赖: Fin.add_def, Fin.eq_or_lt_of_le, Fin.lt_def, Fin.val_last, Nat.mod_eq_of_lt, Nat.succ_lt_succ, Subsingleton, Subsingleton.elim, add_def, eq_or_lt_of_le, finRotate, finRotate_last, finRotate_of_lt, i.elim0, i.le_last, i.neZero, le_last, lt_def, mod_eq_of_lt, neZero
-/
theorem finRotate_apply (i : Fin n) : haveI := i.neZero; finRotate n i = i + 1 := by
  match n with
  | 0 => exact i.elim0
  | 1 => exact @Subsingleton.elim (Fin 1) _ _ _
  | n + 2 =>
    obtain rfl | h := Fin.eq_or_lt_of_le i.le_last
    · simp [finRotate_last]
    · cases i
      simp only [Fin.lt_def, Fin.val_last] at h
      simp [finRotate_of_lt h, Fin.add_def, Nat.mod_eq_of_lt (Nat.succ_lt_succ h)]

@[deprecated finRotate_apply (since := "2026-03-29")]
/--
theorem `finRotate_succ_apply` / 定理 `finRotate_succ_apply`

English:
theorem finRotate_succ_apply
  given: (i : Fin (n + 1))
  statement: finRotate (n + 1) i = i + 1
  proof: by
  simp

中文:
定理 finRotate_succ_apply
  条件: (i : Fin (n + 1))
  结论: finRotate (n + 1) i = i + 1
  证明: by
  simp
-/
theorem finRotate_succ_apply (i : Fin (n + 1)) : finRotate (n + 1) i = i + 1 := by
  simp

/--
theorem `finRotate_apply_zero` / 定理 `finRotate_apply_zero`

English:
theorem finRotate_apply_zero
  statement: finRotate n.succ 0 = 1
  proof: by
  simp

中文:
定理 finRotate_apply_zero
  结论: finRotate n.succ 0 = 1
  证明: by
  simp
-/
theorem finRotate_apply_zero : finRotate n.succ 0 = 1 := by
  simp

/--
theorem `coe_finRotate_of_ne_last` / 定理 `coe_finRotate_of_ne_last`

English:
theorem coe_finRotate_of_ne_last
  given: {i : Fin n.succ} (h : i != Fin.last n)
  proof: by
  rw [finRotate_apply]
  have : (i : Nat) < n := Fin.val_lt_last h
  exact Fin.val_add_one_of_lt this

中文:
定理 coe_finRotate_of_ne_last
  条件: {i : Fin n.succ} (h : i != Fin.last n)
  证明: by
  rw [finRotate_apply]
  have : (i : Nat) < n := Fin.val_lt_last h
  exact Fin.val_add_one_of_lt this

Depends on / 依赖: Fin.val_add_one_of_lt, Fin.val_lt_last, finRotate_apply, val_add_one_of_lt, val_lt_last
-/
theorem coe_finRotate_of_ne_last {i : Fin n.succ} (h : i != Fin.last n) :
    (finRotate (n + 1) i : Nat) = i + 1 := by
  rw [finRotate_apply]
  have : (i : Nat) < n := Fin.val_lt_last h
  exact Fin.val_add_one_of_lt this

/--
theorem `coe_finRotate` / 定理 `coe_finRotate`

English:
theorem coe_finRotate
  given: (i : Fin n.succ)
  proof: by
  rw [finRotate_apply]; rw [Fin.val_add_one i]

中文:
定理 coe_finRotate
  条件: (i : Fin n.succ)
  证明: by
  rw [finRotate_apply]; rw [Fin.val_add_one i]

Depends on / 依赖: Fin.val_add_one, finRotate_apply, val_add_one
-/
theorem coe_finRotate (i : Fin n.succ) :
    (finRotate n.succ i : Nat) = if i = Fin.last n then (0 : Nat) else i + 1 := by
  rw [finRotate_apply]; rw [Fin.val_add_one i]

/--
theorem `lt_finRotate_iff_ne_last` / 定理 `lt_finRotate_iff_ne_last`

English:
theorem lt_finRotate_iff_ne_last
  given: (i : Fin (n + 1))
  proof: by
  simpa using Fin.lt_last_iff_ne_last

中文:
定理 lt_finRotate_iff_ne_last
  条件: (i : Fin (n + 1))
  证明: by
  simpa using Fin.lt_last_iff_ne_last

Depends on / 依赖: Fin.lt_last_iff_ne_last, lt_last_iff_ne_last
-/
theorem lt_finRotate_iff_ne_last (i : Fin (n + 1)) :
    i < finRotate _ i ↔ i != Fin.last n := by
  simpa using Fin.lt_last_iff_ne_last

/--
theorem `lt_finRotate_iff_ne_neg_one` / 定理 `lt_finRotate_iff_ne_neg_one`

English:
theorem lt_finRotate_iff_ne_neg_one
  given: [NeZero n] (i : Fin n)
  proof: by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [lt_finRotate_iff_ne_last]; rw [ne_eq]; rw [not_iff_not]; rw [← Fin.neg_last]; rw [neg_neg]

@[simp]

中文:
定理 lt_finRotate_iff_ne_neg_one
  条件: [NeZero n] (i : Fin n)
  证明: by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [lt_finRotate_iff_ne_last]; rw [ne_eq]; rw [not_iff_not]; rw [← Fin.neg_last]; rw [neg_neg]

@[simp]

Depends on / 依赖: Fin.neg_last, NeZero, NeZero.ne, exists_eq_succ_of_ne_zero, lt_finRotate_iff_ne_last, ne_eq, neg_last, neg_neg, not_iff_not
-/
theorem lt_finRotate_iff_ne_neg_one [NeZero n] (i : Fin n) :
    i < finRotate _ i ↔ i != -1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [lt_finRotate_iff_ne_last]; rw [ne_eq]; rw [not_iff_not]; rw [← Fin.neg_last]; rw [neg_neg]

@[simp]
/--
lemma `finRotate_symm_apply` / 引理 `finRotate_symm_apply`

English:
lemma finRotate_symm_apply
  given: (i : Fin n)
  statement: haveI
  proof: i.neZero; (finRotate _).symm i = i - 1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero i.pos.ne'
  apply (finRotate n.succ).symm_apply_eq.mpr
  rw [finRotate_apply]; rw [sub_add_cancel]

@[deprecated finRotate_symm_apply (since := "2026-03-29")]

中文:
引理 finRotate_symm_apply
  条件: (i : Fin n)
  结论: haveI
  证明: i.neZero; (finRotate _).symm i = i - 1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero i.pos.ne'
  apply (finRotate n.succ).symm_apply_eq.mpr
  rw [finRotate_apply]; rw [sub_add_cancel]

@[deprecated finRotate_symm_apply (since := "2026-03-29")]

Depends on / 依赖: exists_eq_succ_of_ne_zero, finRotate, finRotate_apply, i.neZero, i.pos.ne, n.succ, neZero, sub_add_cancel, symm_apply_eq, symm_apply_eq.mpr
-/
lemma finRotate_symm_apply (i : Fin n) : haveI := i.neZero; (finRotate _).symm i = i - 1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero i.pos.ne'
  apply (finRotate n.succ).symm_apply_eq.mpr
  rw [finRotate_apply]; rw [sub_add_cancel]

@[deprecated finRotate_symm_apply (since := "2026-03-29")]
/--
lemma `finRotate_succ_symm_apply` / 引理 `finRotate_succ_symm_apply`

English:
lemma finRotate_succ_symm_apply
  given: [NeZero n] (i : Fin n)
  statement: (finRotate _).symm i = i - 1
  proof: by
  simp

中文:
引理 finRotate_succ_symm_apply
  条件: [NeZero n] (i : Fin n)
  结论: (finRotate _).symm i = i - 1
  证明: by
  simp
-/
lemma finRotate_succ_symm_apply [NeZero n] (i : Fin n) : (finRotate _).symm i = i - 1 := by
  simp

/--
lemma `coe_finRotate_symm_of_ne_zero` / 引理 `coe_finRotate_symm_of_ne_zero`

English:
lemma coe_finRotate_symm_of_ne_zero
  given: [NeZero n] {i : Fin n} (hi : i != 0)
  proof: by
  rwa [finRotate_symm_apply, Fin.val_sub_one_of_ne_zero]

中文:
引理 coe_finRotate_symm_of_ne_zero
  条件: [NeZero n] {i : Fin n} (hi : i != 0)
  证明: by
  rwa [finRotate_symm_apply, Fin.val_sub_one_of_ne_zero]

Depends on / 依赖: Fin.val_sub_one_of_ne_zero, finRotate_symm_apply, val_sub_one_of_ne_zero
-/
lemma coe_finRotate_symm_of_ne_zero [NeZero n] {i : Fin n} (hi : i != 0) :
    ((finRotate _).symm i : Nat) = i - 1 := by
  rwa [finRotate_symm_apply, Fin.val_sub_one_of_ne_zero]

/--
theorem `finRotate_symm_lt_iff_ne_zero` / 定理 `finRotate_symm_lt_iff_ne_zero`

English:
theorem finRotate_symm_lt_iff_ne_zero
  given: [NeZero n] (i : Fin n)
  proof: by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨ne_zero_of_lt, fun hi => ?_⟩
  rw [Fin.lt_def]; rw [coe_finRotate_symm_of_ne_zero hi]
  exact sub_lt (zero_lt_of_ne_zero <| Fin.val_ne_zero_iff.mpr hi) zero_lt_one

中文:
定理 finRotate_symm_lt_iff_ne_zero
  条件: [NeZero n] (i : Fin n)
  证明: by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨ne_zero_of_lt, fun hi => ?_⟩
  rw [Fin.lt_def]; rw [coe_finRotate_symm_of_ne_zero hi]
  exact sub_lt (zero_lt_of_ne_zero <| Fin.val_ne_zero_iff.mpr hi) zero_lt_one

Depends on / 依赖: Fin.lt_def, Fin.val_ne_zero_iff.mpr, NeZero, NeZero.ne, coe_finRotate_symm_of_ne_zero, exists_eq_succ_of_ne_zero, lt_def, ne_zero_of_lt, sub_lt, val_ne_zero_iff, zero_lt_of_ne_zero, zero_lt_one
-/
theorem finRotate_symm_lt_iff_ne_zero [NeZero n] (i : Fin n) :
    (finRotate _).symm i < i ↔ i != 0 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨ne_zero_of_lt, fun hi => ?_⟩
  rw [Fin.lt_def]; rw [coe_finRotate_symm_of_ne_zero hi]
  exact sub_lt (zero_lt_of_ne_zero <| Fin.val_ne_zero_iff.mpr hi) zero_lt_one

/-- The permutation on `Fin n` that adds `k` to each number. -/
@[simps]
/--
Definition of `finCycle` / `finCycle` 的定义

English:
definition finCycle
  signature: (k : Fin n)
  body: i + k
  invFun i := i - k
  left_inv i := by have := NeZero.of_pos k.pos; simp
  right_inv i := by have := NeZero.of_pos k.pos; simp

中文:
定义 finCycle
  签名: (k : Fin n)
  定义体: i + k
  invFun i := i - k
  left_inv i := by have := NeZero.of_pos k.pos; simp
  right_inv i := by have := NeZero.of_pos k.pos; simp
-/
def finCycle (k : Fin n) : Equiv.Perm (Fin n) where
  toFun i := i + k
  invFun i := i - k
  left_inv i := by have := NeZero.of_pos k.pos; simp
  right_inv i := by have := NeZero.of_pos k.pos; simp

/--
lemma `finCycle_eq_finRotate_iterate` / 引理 `finCycle_eq_finRotate_iterate`

English:
lemma finCycle_eq_finRotate_iterate
  given: {k : Fin n}
  statement: finCycle k = (finRotate n)^[k.1]
  proof: by
  match n with
  | 0 => exact k.elim0
  | n + 1 =>
    ext i; induction k using Fin.induction with
    | zero => simp
    | succ k ih =>
      rw [Fin.val_eq_val]; rw [Fin.val_castSucc] at ih
      rw [Fin.val_succ]; rw [Function.iterate_succ']; rw [Function.comp_apply]; rw [← ih]; rw [finRotate_

中文:
引理 finCycle_eq_finRotate_iterate
  条件: {k : Fin n}
  结论: finCycle k = (finRotate n)^[k.1]
  证明: by
  match n with
  | 0 => exact k.elim0
  | n + 1 =>
    ext i; induction k using Fin.induction with
    | zero => simp
    | succ k ih =>
      rw [Fin.val_eq_val]; rw [Fin.val_castSucc] at ih
      rw [Fin.val_succ]; rw [Function.iterate_succ']; rw [Function.comp_apply]; rw [← ih]; rw [finRotate_

Depends on / 依赖: Fin.coeSucc_eq_succ, Fin.induction, Fin.val_castSucc, Fin.val_eq_val, Fin.val_succ, Function, Function.comp_apply, Function.iterate_succ, add_assoc, coeSucc_eq_succ, comp_apply, finCycle_apply, finRotate_apply, iterate_succ, k.elim0, val_castSucc, val_eq_val, val_succ
-/
lemma finCycle_eq_finRotate_iterate {k : Fin n} : finCycle k = (finRotate n)^[k.1] := by
  match n with
  | 0 => exact k.elim0
  | n + 1 =>
    ext i; induction k using Fin.induction with
    | zero => simp
    | succ k ih =>
      rw [Fin.val_eq_val]; rw [Fin.val_castSucc] at ih
      rw [Fin.val_succ]; rw [Function.iterate_succ']; rw [Function.comp_apply]; rw [← ih]; rw [finRotate_apply]; rw [finCycle_apply]; rw [finCycle_apply]; rw [add_assoc]; rw [Fin.coeSucc_eq_succ]
