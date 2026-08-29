/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Common
public import Mathlib.Data.Set.Insert

/-!
# Set enumeration

This file allows enumeration of sets given a choice function.
The definition does not assume `sel` actually is a choice function, i.e. `sel s ∈ s` and
`sel s = none ↔ s = ∅`. These assumptions are added to the lemmas needing them.
-/

@[expose] public section

assert_not_exists RelIso

noncomputable section

open Function

namespace Set

section Enumerate

variable {α : Type*} (sel : Set α -> Option α)

/--
Definition of `enumerate` / `enumerate` 的定义

English:
definition enumerate
  signature: : Set α -> Nat -> Option α

中文:
定义 enumerate
  签名: : 集合 α -> 自然数 -> 选项类型 α
-/
def enumerate : Set α -> Nat -> Option α
  | s, 0 => sel s
  | s, n + 1 => do
    let a ← sel s
    enumerate (s \ {a}) n

/--
theorem `enumerate_eq_none_of_sel` / 定理 `enumerate_eq_none_of_sel`

English:
theorem enumerate_eq_none_of_sel
  given: {s : Set α} (h : sel s = none)
  statement: forall {n}, enumerate sel s n = none

中文:
定理 enumerate_eq_none_of_sel
  条件: {s : 集合 α} (h : sel s = none)
  结论: 对任意 {n}, enumerate sel s n = none
-/
theorem enumerate_eq_none_of_sel {s : Set α} (h : sel s = none) : forall {n}, enumerate sel s n = none
  | 0 => by simp [h, enumerate]
  | n + 1 => by simp [h, enumerate]

/--
theorem `enumerate_eq_none` / 定理 `enumerate_eq_none`

English:
theorem enumerate_eq_none
  proof: Nat.le_of_succ_le_succ hm
        exact enumerate_eq_none h hm

中文:
定理 enumerate_eq_none
  证明: Nat.le_of_succ_le_succ hm
        exact enumerate_eq_none h hm

Depends on / 依赖: Nat.le_of_succ_le_succ, le_of_succ_le_succ
-/
theorem enumerate_eq_none :
    forall {s n₁ n₂}, enumerate sel s n₁ = none -> n₁ <= n₂ -> enumerate sel s n₂ = none
  | _, 0, _ => fun h _ => enumerate_eq_none_of_sel sel h
  | s, n + 1, m => fun h hm => by
    cases hs : sel s
    · exact enumerate_eq_none_of_sel sel hs
    · cases m with
      | zero => contradiction
      | succ m' =>
        simp only [enumerate, hs] at h ⊢
        have hm : n <= m' := Nat.le_of_succ_le_succ hm
        exact enumerate_eq_none h hm

/--
theorem `enumerate_mem` / 定理 `enumerate_mem`

English:
theorem enumerate_mem
  given: (h_sel : forall s a, sel s = some a -> a in s)
  proof: enumerate_mem h_sel h'
        this.left

中文:
定理 enumerate_mem
  条件: (h_sel : 对任意 s a, sel s = some a -> a in s)
  证明: enumerate_mem h_sel h'
        this.left

Depends on / 依赖: enumerate_mem, h_sel
-/
theorem enumerate_mem (h_sel : forall s a, sel s = some a -> a in s) :
    forall {s n a}, enumerate sel s n = some a -> a in s
  | s, 0, a => h_sel s a
  | s, n + 1, a => by
    cases h : sel s with
    | none => simp [enumerate_eq_none_of_sel, h]
    | some a' =>
      simp only [enumerate, h]
      exact fun h' : enumerate sel (s \ {a'}) n = some a =>
        have : a in s \ {a'} := enumerate_mem h_sel h'
        this.left

/--
theorem `enumerate_inj` / 定理 `enumerate_inj`

English:
theorem enumerate_inj
  statement: {n₁ n₂ : Nat} {a : α} {s : Set α} (h_sel : forall s a, sel s = some a -> a in s)
  proof: by
  wlog! hn : n₁ <= n₂ generalizing n₁ n₂
  · exact (this h₂ h₁ hn.le).symm
  rcases Nat.le.dest hn with ⟨m, rfl⟩
  clear hn
  induction n₁ generalizing s with
  | zero =>
    cases m with
    | zero => rfl
    | succ m =>
      have h' : enumerate sel (s \ {a}) m = some a := by
        simp_all only [enumerate, Nat.add_eq, zero_add]; exact h₂
      have : a in s \ {a} := enumerate_mem sel h_sel h'
      simp_all
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 by lia] at h₂
    cases h : sel s <;> simp_all [enumerate]; tauto

中文:
定理 enumerate_inj
  结论: {n₁ n₂ : 自然数} {a : α} {s : 集合 α} (h_sel : 对任意 s a, sel s = some a -> a in s)
  证明: by
  wlog! hn : n₁ <= n₂ generalizing n₁ n₂
  · exact (this h₂ h₁ hn.le).symm
  rcases Nat.le.dest hn with ⟨m, rfl⟩
  clear hn
  induction n₁ generalizing s with
  | zero =>
    cases m with
    | zero => rfl
    | succ m =>
      have h' : enumerate sel (s \ {a}) m = some a := by
        simp_all only [enumerate, Nat.add_eq, zero_add]; exact h₂
      have : a in s \ {a} := enumerate_mem sel h_sel h'
      simp_all
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 by lia] at h₂
    cases h : sel s <;> simp_all [enumerate]; tauto

Depends on / 依赖: Nat.add_eq, Nat.le.dest, add_eq, enumerate, enumerate_mem, generalizing, h_sel, hn.le, zero_add
-/
theorem enumerate_inj {n₁ n₂ : Nat} {a : α} {s : Set α} (h_sel : forall s a, sel s = some a -> a in s)
    (h₁ : enumerate sel s n₁ = some a) (h₂ : enumerate sel s n₂ = some a) : n₁ = n₂ := by
  wlog! hn : n₁ <= n₂ generalizing n₁ n₂
  · exact (this h₂ h₁ hn.le).symm
  rcases Nat.le.dest hn with ⟨m, rfl⟩
  clear hn
  induction n₁ generalizing s with
  | zero =>
    cases m with
    | zero => rfl
    | succ m =>
      have h' : enumerate sel (s \ {a}) m = some a := by
        simp_all only [enumerate, Nat.add_eq, zero_add]; exact h₂
      have : a in s \ {a} := enumerate_mem sel h_sel h'
      simp_all
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 by lia] at h₂
    cases h : sel s <;> simp_all [enumerate]; tauto

end Enumerate

end Set
