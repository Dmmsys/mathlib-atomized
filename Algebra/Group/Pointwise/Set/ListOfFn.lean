/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise operations with lists of sets

This file proves some lemmas about pointwise algebraic operations with lists of sets.
-/

public section

namespace Set

variable {α : Type*} [Monoid α] {s : Set α} {n : Nat}

open scoped Pointwise

@[to_additive]
/--
theorem `mem_prod_list_ofFn` / 定理 `mem_prod_list_ofFn`

English:
theorem mem_prod_list_ofFn
  given: {a : α} {s : Fin n -> Set α}
  proof: by
  induction n generalizing a with
  | zero => simp_rw [List.ofFn_zero, List.prod_nil, Fin.exists_fin_zero_pi, eq_comm, Set.mem_one]
  | succ n ih =>
    simp_rw [List.ofFn_succ, List.prod_cons, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.cons_succ,
      mem_mul, @ih, exists_exists_eq_and, SetCoe.exists, exists_prop]

@[to_additive]

中文:
定理 mem_prod_list_ofFn
  条件: {a : α} {s : 有限集 n -> 集合 α}
  证明: by
  induction n generalizing a with
  | zero => simp_rw [List.ofFn_zero, List.prod_nil, Fin.exists_fin_zero_pi, eq_comm, Set.mem_one]
  | succ n ih =>
    simp_rw [List.ofFn_succ, List.prod_cons, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.cons_succ,
      mem_mul, @ih, exists_exists_eq_and, SetCoe.exists, exists_prop]

@[to_additive]

Depends on / 依赖: Fin.cons_succ, Fin.cons_zero, Fin.exists_fin_succ_pi, Fin.exists_fin_zero_pi, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, Set.mem_one, SetCoe, SetCoe.exists, cons_succ, cons_zero, eq_comm, exists_exists_eq_and, exists_fin_succ_pi, exists_fin_zero_pi, exists_prop, generalizing, mem_mul
-/
theorem mem_prod_list_ofFn {a : α} {s : Fin n -> Set α} :
    a in (List.ofFn s).prod ↔ exists f : forall i : Fin n, s i, (List.ofFn fun i => (f i : α)).prod = a := by
  induction n generalizing a with
  | zero => simp_rw [List.ofFn_zero, List.prod_nil, Fin.exists_fin_zero_pi, eq_comm, Set.mem_one]
  | succ n ih =>
    simp_rw [List.ofFn_succ, List.prod_cons, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.cons_succ,
      mem_mul, @ih, exists_exists_eq_and, SetCoe.exists, exists_prop]

@[to_additive]
/--
theorem `mem_list_prod` / 定理 `mem_list_prod`

English:
theorem mem_list_prod
  given: {l : List (Set α)} {a : α}
  proof: by
  induction l using List.ofFnRec with | _ n f
  simp only [mem_prod_list_ofFn, List.exists_iff_exists_tuple, List.map_ofFn, List.ofFn_inj',
    Sigma.mk.inj_iff, and_left_comm, exists_and_left, exists_eq_left, heq_eq_eq]
  constructor
  · rintro ⟨fi, rfl⟩
    exact ⟨fun i => ⟨_, fi i⟩, rfl, rfl⟩
  · rintro ⟨fi, rfl, rfl⟩
    exact ⟨fun i => _, rfl⟩

@[to_additive (attr := push)]

中文:
定理 mem_list_prod
  条件: {l : 列表 (集合 α)} {a : α}
  证明: by
  induction l using List.ofFnRec with | _ n f
  simp only [mem_prod_list_ofFn, List.exists_iff_exists_tuple, List.map_ofFn, List.ofFn_inj',
    Sigma.mk.inj_iff, and_left_comm, exists_and_left, exists_eq_left, heq_eq_eq]
  constructor
  · rintro ⟨fi, rfl⟩
    exact ⟨fun i => ⟨_, fi i⟩, rfl, rfl⟩
  · rintro ⟨fi, rfl, rfl⟩
    exact ⟨fun i => _, rfl⟩

@[to_additive (attr := push)]

Depends on / 依赖: List.exists_iff_exists_tuple, List.map_ofFn, List.ofFnRec, List.ofFn_inj, Sigma.mk.inj_iff, and_left_comm, exists_and_left, exists_eq_left, exists_iff_exists_tuple, heq_eq_eq, inj_iff, map_ofFn, mem_prod_list_ofFn, ofFnRec, ofFn_inj
-/
theorem mem_list_prod {l : List (Set α)} {a : α} :
    a in l.prod ↔
      exists l' : List (Σ s : Set α, ↥s),
        List.prod (l'.map fun x => (Sigma.snd x : α)) = a ∧ l'.map Sigma.fst = l := by
  induction l using List.ofFnRec with | _ n f
  simp only [mem_prod_list_ofFn, List.exists_iff_exists_tuple, List.map_ofFn, List.ofFn_inj',
    Sigma.mk.inj_iff, and_left_comm, exists_and_left, exists_eq_left, heq_eq_eq]
  constructor
  · rintro ⟨fi, rfl⟩
    exact ⟨fun i => ⟨_, fi i⟩, rfl, rfl⟩
  · rintro ⟨fi, rfl, rfl⟩
    exact ⟨fun i => _, rfl⟩

@[to_additive (attr := push)]
/--
theorem `mem_pow` / 定理 `mem_pow`

English:
theorem mem_pow
  given: {a : α} {n : Nat}
  proof: by
  rw [← mem_prod_list_ofFn]; rw [List.ofFn_const]; rw [List.prod_replicate]

中文:
定理 mem_pow
  条件: {a : α} {n : 自然数}
  证明: by
  rw [← mem_prod_list_ofFn]; rw [List.ofFn_const]; rw [List.prod_replicate]

Depends on / 依赖: List.ofFn_const, List.prod_replicate, mem_prod_list_ofFn, ofFn_const, prod_replicate
-/
theorem mem_pow {a : α} {n : Nat} :
    a in s ^ n ↔ exists f : Fin n -> s, (List.ofFn fun i => (f i : α)).prod = a := by
  rw [← mem_prod_list_ofFn]; rw [List.ofFn_const]; rw [List.prod_replicate]

end Set
